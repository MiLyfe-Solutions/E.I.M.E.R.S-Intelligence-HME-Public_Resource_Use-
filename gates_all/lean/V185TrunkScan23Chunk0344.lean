import V185TrunkScan23Chunk0343

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2035202 : List Nat := [3, 4, 1, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2035202 : Nat := 118140960795 + 2035202 * 2 ^ 59
def prefixEnd_2035202 : Nat := 4983230072969 + 3 ^ 40 * 2035202 * 2
def baseEnd_2035202 : Nat := 1045036854991851496515283

theorem tailTrace_2035202 : CollatzResearch.WordTrace tailWord_2035202 prefixEnd_2035202 1045036854991851496515283 := by
  unfold tailWord_2035202
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557478793204553418516965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49486610115212142449378573 18557478793204553418516965)
  ·
    refine ⟨3479527273725853765971931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18557478793204553418516965 3479527273725853765971931)
    ·
      refine ⟨5219290910588780648957897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479527273725853765971931 5219290910588780648957897)
      ·
        refine ⟨3914468182941585486718423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5219290910588780648957897 3914468182941585486718423)
        ·
          refine ⟨5871702274412378230077635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914468182941585486718423 5871702274412378230077635)
          ·
            refine ⟨8807553411618567345116453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5871702274412378230077635 8807553411618567345116453)
            ·
              refine ⟨1651416264678481377209335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8807553411618567345116453 1651416264678481377209335)
              ·
                refine ⟨2477124397017722065814003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651416264678481377209335 2477124397017722065814003)
                ·
                  refine ⟨3715686595526583098721005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477124397017722065814003 3715686595526583098721005)
                  ·
                    refine ⟨1393382473322468662020377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3715686595526583098721005 1393382473322468662020377)
                    ·
                      refine ⟨1045036854991851496515283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393382473322468662020377 1045036854991851496515283)
                      ·
                        rfl

theorem cell23_2035202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2035202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035202 prefixEnd_2035202 := by exact prefixLift 2035202
  have htrace : WordTrace (prefixWord ++ tailWord_2035202) baseStart_2035202 baseEnd_2035202 := by
    simpa [prefixWord, tailWord_2035202, baseEnd_2035202] using wordTrace_append hprefix tailTrace_2035202
  have hstable : (prefixWord ++ tailWord_2035202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035202).length < 2 ^ (prefixWord ++ tailWord_2035202).sum := by decide
  have hdescent : baseEnd_2035202 < baseStart_2035202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035221 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 5]
def baseStart_2035221 : Nat := 118140960795 + 2035221 * 2 ^ 59
def prefixEnd_2035221 : Nat := 4983230072969 + 3 ^ 40 * 2035221 * 2
def baseEnd_2035221 : Nat := 116116290124920769130855

theorem tailTrace_2035221 : CollatzResearch.WordTrace tailWord_2035221 prefixEnd_2035221 116116290124920769130855 := by
  unfold tailWord_2035221
  simp only [CollatzResearch.WordTrace]
  refine ⟨74230608159749379919009517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49487072106499586612673011 74230608159749379919009517)
  ·
    refine ⟨27836478059906017469628569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74230608159749379919009517 27836478059906017469628569)
    ·
      refine ⟨20877358544929513102221427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27836478059906017469628569 20877358544929513102221427)
      ·
        refine ⟨31316037817394269653332141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20877358544929513102221427 31316037817394269653332141)
        ·
          refine ⟨11743514181522851119999553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31316037817394269653332141 11743514181522851119999553)
          ·
            refine ⟨8807635636142138339999665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11743514181522851119999553 8807635636142138339999665)
            ·
              refine ⟨6605726727106603754999749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8807635636142138339999665 6605726727106603754999749)
              ·
                refine ⟨1238573761332488204062453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6605726727106603754999749 1238573761332488204062453)
                ·
                  refine ⟨116116290124920769130855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1238573761332488204062453 116116290124920769130855)
                  ·
                    rfl

theorem cell23_2035221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_2035221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035221 prefixEnd_2035221 := by exact prefixLift 2035221
  have htrace : WordTrace (prefixWord ++ tailWord_2035221) baseStart_2035221 baseEnd_2035221 := by
    simpa [prefixWord, tailWord_2035221, baseEnd_2035221] using wordTrace_append hprefix tailTrace_2035221
  have hstable : (prefixWord ++ tailWord_2035221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035221).length < 2 ^ (prefixWord ++ tailWord_2035221).sum := by decide
  have hdescent : baseEnd_2035221 < baseStart_2035221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035232 : List Nat := [2, 1, 1, 6, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2035232 : Nat := 118140960795 + 2035232 * 2 ^ 59
def prefixEnd_2035232 : Nat := 4983230072969 + 3 ^ 40 * 2035232 * 2
def baseEnd_2035232 : Nat := 1045052259411486379140145

theorem tailTrace_2035232 : CollatzResearch.WordTrace tailWord_2035232 prefixEnd_2035232 1045052259411486379140145 := by
  unfold tailWord_2035232
  simp only [CollatzResearch.WordTrace]
  refine ⟨37115504681354764398829975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49487339575139685865106633 37115504681354764398829975)
  ·
    refine ⟨55673257022032146598244963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37115504681354764398829975 55673257022032146598244963)
    ·
      refine ⟨83509885533048219897367445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55673257022032146598244963 83509885533048219897367445)
      ·
        refine ⟨3914525884361635307689099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83509885533048219897367445 3914525884361635307689099)
        ·
          refine ⟨5871788826542452961533649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914525884361635307689099 5871788826542452961533649)
          ·
            refine ⟨4403841619906839721150237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5871788826542452961533649 4403841619906839721150237)
            ·
              refine ⟨1651440607465064895431339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4403841619906839721150237 1651440607465064895431339)
              ·
                refine ⟨2477160911197597343147009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651440607465064895431339 2477160911197597343147009)
                ·
                  refine ⟨1857870683398198007360257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2477160911197597343147009 1857870683398198007360257)
                  ·
                    refine ⟨1393403012548648505520193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1857870683398198007360257 1393403012548648505520193)
                    ·
                      refine ⟨1045052259411486379140145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393403012548648505520193 1045052259411486379140145)
                      ·
                        rfl

theorem cell23_2035232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2035232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035232 prefixEnd_2035232 := by exact prefixLift 2035232
  have htrace : WordTrace (prefixWord ++ tailWord_2035232) baseStart_2035232 baseEnd_2035232 := by
    simpa [prefixWord, tailWord_2035232, baseEnd_2035232] using wordTrace_append hprefix tailTrace_2035232
  have hstable : (prefixWord ++ tailWord_2035232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035232).length < 2 ^ (prefixWord ++ tailWord_2035232).sum := by decide
  have hdescent : baseEnd_2035232 < baseStart_2035232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035234 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_2035234 : Nat := 118140960795 + 2035234 * 2 ^ 59
def prefixEnd_2035234 : Nat := 4983230072969 + 3 ^ 40 * 2035234 * 2
def baseEnd_2035234 : Nat := 348351095457598457105045

theorem tailTrace_2035234 : CollatzResearch.WordTrace tailWord_2035234 prefixEnd_2035234 348351095457598457105045 := by
  unfold tailWord_2035234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18557770577175570784808189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49487388205801522092821837 18557770577175570784808189)
  ·
    refine ⟨6959163966440839044303071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18557770577175570784808189 6959163966440839044303071)
    ·
      refine ⟨10438745949661258566454607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6959163966440839044303071 10438745949661258566454607)
      ·
        refine ⟨15658118924491887849681911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10438745949661258566454607 15658118924491887849681911)
        ·
          refine ⟨23487178386737831774522867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15658118924491887849681911 23487178386737831774522867)
          ·
            refine ⟨35230767580106747661784301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23487178386737831774522867 35230767580106747661784301)
            ·
              refine ⟨13211537842540030373169113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35230767580106747661784301 13211537842540030373169113)
              ·
                refine ⟨9908653381905022779876835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13211537842540030373169113 9908653381905022779876835)
                ·
                  refine ⟨14862980072857534169815253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9908653381905022779876835 14862980072857534169815253)
                  ·
                    refine ⟨348351095457598457105045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14862980072857534169815253 348351095457598457105045)
                    ·
                      rfl

theorem cell23_2035234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_2035234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035234 prefixEnd_2035234 := by exact prefixLift 2035234
  have htrace : WordTrace (prefixWord ++ tailWord_2035234) baseStart_2035234 baseEnd_2035234 := by
    simpa [prefixWord, tailWord_2035234, baseEnd_2035234] using wordTrace_append hprefix tailTrace_2035234
  have hstable : (prefixWord ++ tailWord_2035234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035234).length < 2 ^ (prefixWord ++ tailWord_2035234).sum := by decide
  have hdescent : baseEnd_2035234 < baseStart_2035234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035331 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 3, 5, 2]
def baseStart_2035331 : Nat := 118140960795 + 2035331 * 2 ^ 59
def prefixEnd_2035331 : Nat := 4983230072969 + 3 ^ 40 * 2035331 * 2
def baseEnd_2035331 : Nat := 1045103093996281491802189

theorem tailTrace_2035331 : CollatzResearch.WordTrace tailWord_2035331 prefixEnd_2035331 1045103093996281491802189 := by
  unfold tailWord_2035331
  simp only [CollatzResearch.WordTrace]
  refine ⟨74234620189350868705513847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49489746792900579137009231 74234620189350868705513847)
  ·
    refine ⟨111351930284026303058270771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74234620189350868705513847 111351930284026303058270771)
    ·
      refine ⟨167027895426039454587406157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111351930284026303058270771 167027895426039454587406157)
      ·
        refine ⟨62635460784764795470277309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167027895426039454587406157 62635460784764795470277309)
        ·
          refine ⟨23488297794286798301353991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62635460784764795470277309 23488297794286798301353991)
          ·
            refine ⟨35232446691430197452030987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23488297794286798301353991 35232446691430197452030987)
            ·
              refine ⟨52848670037145296178046481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35232446691430197452030987 52848670037145296178046481)
              ·
                refine ⟨39636502527858972133534861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52848670037145296178046481 39636502527858972133534861)
                ·
                  refine ⟨14863688447947114550075573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39636502527858972133534861 14863688447947114550075573)
                  ·
                    refine ⟨1393470791995041989069585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14863688447947114550075573 1393470791995041989069585)
                    ·
                      refine ⟨1045103093996281491802189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393470791995041989069585 1045103093996281491802189)
                      ·
                        rfl

theorem cell23_2035331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_2035331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035331 prefixEnd_2035331 := by exact prefixLift 2035331
  have htrace : WordTrace (prefixWord ++ tailWord_2035331) baseStart_2035331 baseEnd_2035331 := by
    simpa [prefixWord, tailWord_2035331, baseEnd_2035331] using wordTrace_append hprefix tailTrace_2035331
  have hstable : (prefixWord ++ tailWord_2035331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035331).length < 2 ^ (prefixWord ++ tailWord_2035331).sum := by decide
  have hdescent : baseEnd_2035331 < baseStart_2035331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035358 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2035358 : Nat := 118140960795 + 2035358 * 2 ^ 59
def prefixEnd_2035358 : Nat := 4983230072969 + 3 ^ 40 * 2035358 * 2
def baseEnd_2035358 : Nat := 348372319324650962054855

theorem tailTrace_2035358 : CollatzResearch.WordTrace tailWord_2035358 prefixEnd_2035358 348372319324650962054855 := by
  unfold tailWord_2035358
  simp only [CollatzResearch.WordTrace]
  refine ⟨9279450620031631539593341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49490403306835368211164485 9279450620031631539593341)
  ·
    refine ⟨3479793982511861827347503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9279450620031631539593341 3479793982511861827347503)
    ·
      refine ⟨5219690973767792741021255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3479793982511861827347503 5219690973767792741021255)
      ·
        refine ⟨7829536460651689111531883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5219690973767792741021255 7829536460651689111531883)
        ·
          refine ⟨11744304690977533667297825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829536460651689111531883 11744304690977533667297825)
          ·
            refine ⟨8808228518233150250473369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11744304690977533667297825 8808228518233150250473369)
            ·
              refine ⟨6606171388674862687855027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8808228518233150250473369 6606171388674862687855027)
              ·
                refine ⟨9909257083012294031782541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606171388674862687855027 9909257083012294031782541)
                ·
                  refine ⟨3715971406129610261918453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9909257083012294031782541 3715971406129610261918453)
                  ·
                    refine ⟨348372319324650962054855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3715971406129610261918453 348372319324650962054855)
                    ·
                      rfl

theorem cell23_2035358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2035358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035358 prefixEnd_2035358 := by exact prefixLift 2035358
  have htrace : WordTrace (prefixWord ++ tailWord_2035358) baseStart_2035358 baseEnd_2035358 := by
    simpa [prefixWord, tailWord_2035358, baseEnd_2035358] using wordTrace_append hprefix tailTrace_2035358
  have hstable : (prefixWord ++ tailWord_2035358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035358).length < 2 ^ (prefixWord ++ tailWord_2035358).sum := by decide
  have hdescent : baseEnd_2035358 < baseStart_2035358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035388 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 4, 4]
def baseStart_2035388 : Nat := 118140960795 + 2035388 * 2 ^ 59
def prefixEnd_2035388 : Nat := 4983230072969 + 3 ^ 40 * 2035388 * 2
def baseEnd_2035388 : Nat := 348377454131195922929809

theorem tailTrace_2035388 : CollatzResearch.WordTrace tailWord_2035388 prefixEnd_2035388 348377454131195922929809 := by
  unfold tailWord_2035388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37118349575072183720169409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49491132766762911626892545 37118349575072183720169409)
  ·
    refine ⟨27838762181304137790127057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37118349575072183720169409 27838762181304137790127057)
    ·
      refine ⟨20879071635978103342595293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27838762181304137790127057 20879071635978103342595293)
      ·
        refine ⟨7829651863491788753473235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20879071635978103342595293 7829651863491788753473235)
        ·
          refine ⟨11744477795237683130209853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7829651863491788753473235 11744477795237683130209853)
          ·
            refine ⟨4404179173214131173828695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11744477795237683130209853 4404179173214131173828695)
            ·
              refine ⟨6606268759821196760743043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404179173214131173828695 6606268759821196760743043)
              ·
                refine ⟨9909403139731795141114565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606268759821196760743043 9909403139731795141114565)
                ·
                  refine ⟨1858013088699711588958981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9909403139731795141114565 1858013088699711588958981)
                  ·
                    refine ⟨348377454131195922929809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858013088699711588958981 348377454131195922929809)
                    ·
                      rfl

theorem cell23_2035388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_2035388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035388 prefixEnd_2035388 := by exact prefixLift 2035388
  have htrace : WordTrace (prefixWord ++ tailWord_2035388) baseStart_2035388 baseEnd_2035388 := by
    simpa [prefixWord, tailWord_2035388, baseEnd_2035388] using wordTrace_append hprefix tailTrace_2035388
  have hstable : (prefixWord ++ tailWord_2035388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035388).length < 2 ^ (prefixWord ++ tailWord_2035388).sum := by decide
  have hdescent : baseEnd_2035388 < baseStart_2035388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035405 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_2035405 : Nat := 118140960795 + 2035405 * 2 ^ 59
def prefixEnd_2035405 : Nat := 4983230072969 + 3 ^ 40 * 2035405 * 2
def baseEnd_2035405 : Nat := 348380363854904734092283

theorem tailTrace_2035405 : CollatzResearch.WordTrace tailWord_2035405 prefixEnd_2035405 348380363854904734092283 := by
  unfold tailWord_2035405
  simp only [CollatzResearch.WordTrace]
  refine ⟨74237319191082779343707669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49491546127388519562471779 74237319191082779343707669)
  ·
    refine ⟨3479874337082005281736297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 74237319191082779343707669 3479874337082005281736297)
    ·
      refine ⟨2609905752811503961302223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3479874337082005281736297 2609905752811503961302223)
      ·
        refine ⟨3914858629217255941953335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2609905752811503961302223 3914858629217255941953335)
        ·
          refine ⟨5872287943825883912930003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914858629217255941953335 5872287943825883912930003)
          ·
            refine ⟨8808431915738825869395005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872287943825883912930003 8808431915738825869395005)
            ·
              refine ⟨3303161968402059701023127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8808431915738825869395005 3303161968402059701023127)
              ·
                refine ⟨4954742952603089551534691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303161968402059701023127 4954742952603089551534691)
                ·
                  refine ⟨7432114428904634327302037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4954742952603089551534691 7432114428904634327302037)
                  ·
                    refine ⟨348380363854904734092283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7432114428904634327302037 348380363854904734092283)
                    ·
                      rfl

theorem cell23_2035405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_2035405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035405 prefixEnd_2035405 := by exact prefixLift 2035405
  have htrace : WordTrace (prefixWord ++ tailWord_2035405) baseStart_2035405 baseEnd_2035405 := by
    simpa [prefixWord, tailWord_2035405, baseEnd_2035405] using wordTrace_append hprefix tailTrace_2035405
  have hstable : (prefixWord ++ tailWord_2035405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035405).length < 2 ^ (prefixWord ++ tailWord_2035405).sum := by decide
  have hdescent : baseEnd_2035405 < baseStart_2035405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035412 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2035412 : Nat := 118140960795 + 2035412 * 2 ^ 59
def prefixEnd_2035412 : Nat := 4983230072969 + 3 ^ 40 * 2035412 * 2
def baseEnd_2035412 : Nat := 1045144685929295674889317

theorem tailTrace_2035412 : CollatzResearch.WordTrace tailWord_2035412 prefixEnd_2035412 1045144685929295674889317 := by
  unfold tailWord_2035412
  simp only [CollatzResearch.WordTrace]
  refine ⟨37118787251028709769606245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49491716334704946359474993 37118787251028709769606245)
  ·
    refine ⟨6959772609567883081801171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37118787251028709769606245 6959772609567883081801171)
    ·
      refine ⟨10439658914351824622701757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6959772609567883081801171 10439658914351824622701757)
      ·
        refine ⟨3914872092881934233513159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10439658914351824622701757 3914872092881934233513159)
        ·
          refine ⟨5872308139322901350269739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3914872092881934233513159 5872308139322901350269739)
          ·
            refine ⟨8808462208984352025404609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5872308139322901350269739 8808462208984352025404609)
            ·
              refine ⟨6606346656738264019053457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8808462208984352025404609 6606346656738264019053457)
              ·
                refine ⟨4954759992553698014290093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606346656738264019053457 4954759992553698014290093)
                ·
                  refine ⟨1858034997207636755358785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4954759992553698014290093 1858034997207636755358785)
                  ·
                    refine ⟨1393526247905727566519089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1858034997207636755358785 1393526247905727566519089)
                    ·
                      refine ⟨1045144685929295674889317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393526247905727566519089 1045144685929295674889317)
                      ·
                        rfl

theorem cell23_2035412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2035412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035412 prefixEnd_2035412 := by exact prefixLift 2035412
  have htrace : WordTrace (prefixWord ++ tailWord_2035412) baseStart_2035412 baseEnd_2035412 := by
    simpa [prefixWord, tailWord_2035412, baseEnd_2035412] using wordTrace_append hprefix tailTrace_2035412
  have hstable : (prefixWord ++ tailWord_2035412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035412).length < 2 ^ (prefixWord ++ tailWord_2035412).sum := by decide
  have hdescent : baseEnd_2035412 < baseStart_2035412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035418 : List Nat := [3, 1, 1, 2, 2, 5, 2, 7]
def baseStart_2035418 : Nat := 118140960795 + 2035418 * 2 ^ 59
def prefixEnd_2035418 : Nat := 4983230072969 + 3 ^ 40 * 2035418 * 2
def baseEnd_2035418 : Nat := 38709176548637875978307

theorem tailTrace_2035418 : CollatzResearch.WordTrace tailWord_2035418 prefixEnd_2035418 38709176548637875978307 := by
  unfold tailWord_2035418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18559448335008920640982727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49491862226690455042620605 18559448335008920640982727)
  ·
    refine ⟨27839172502513380961474091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18559448335008920640982727 27839172502513380961474091)
    ·
      refine ⟨41758758753770071442211137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27839172502513380961474091 41758758753770071442211137)
      ·
        refine ⟨31319069065327553581658353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41758758753770071442211137 31319069065327553581658353)
        ·
          refine ⟨23489301798995665186243765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31319069065327553581658353 23489301798995665186243765)
          ·
            refine ⟨2202122043655843611210353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23489301798995665186243765 2202122043655843611210353)
            ·
              refine ⟨1651591532741882708407765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202122043655843611210353 1651591532741882708407765)
              ·
                refine ⟨38709176548637875978307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1651591532741882708407765 38709176548637875978307)
                ·
                  rfl

theorem cell23_2035418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 2, 7].length) (baseStart_2035418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035418 prefixEnd_2035418 := by exact prefixLift 2035418
  have htrace : WordTrace (prefixWord ++ tailWord_2035418) baseStart_2035418 baseEnd_2035418 := by
    simpa [prefixWord, tailWord_2035418, baseEnd_2035418] using wordTrace_append hprefix tailTrace_2035418
  have hstable : (prefixWord ++ tailWord_2035418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035418).length < 2 ^ (prefixWord ++ tailWord_2035418).sum := by decide
  have hdescent : baseEnd_2035418 < baseStart_2035418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035428 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_2035428 : Nat := 118140960795 + 2035428 * 2 ^ 59
def prefixEnd_2035428 : Nat := 4983230072969 + 3 ^ 40 * 2035428 * 2
def baseEnd_2035428 : Nat := 1045152901619767612289243

theorem tailTrace_2035428 : CollatzResearch.WordTrace tailWord_2035428 prefixEnd_2035428 1045152901619767612289243 := by
  unfold tailWord_2035428
  simp only [CollatzResearch.WordTrace]
  refine ⟨37119079034999727135897469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49492105379999636181196625 37119079034999727135897469)
  ·
    refine ⟨13919654638124897675961551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37119079034999727135897469 13919654638124897675961551)
    ·
      refine ⟨20879481957187346513942327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13919654638124897675961551 20879481957187346513942327)
      ·
        refine ⟨31319222935781019770913491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20879481957187346513942327 31319222935781019770913491)
        ·
          refine ⟨46978834403671529656370237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31319222935781019770913491 46978834403671529656370237)
          ·
            refine ⟨17617062901376823621138839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46978834403671529656370237 17617062901376823621138839)
            ·
              refine ⟨26425594352065235431708259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17617062901376823621138839 26425594352065235431708259)
              ·
                refine ⟨39638391528097853147562389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26425594352065235431708259 39638391528097853147562389)
                ·
                  refine ⟨1858049602879586866291987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39638391528097853147562389 1858049602879586866291987)
                  ·
                    refine ⟨2787074404319380299437981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1858049602879586866291987 2787074404319380299437981)
                    ·
                      refine ⟨1045152901619767612289243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787074404319380299437981 1045152901619767612289243)
                      ·
                        rfl

theorem cell23_2035428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_2035428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035428 prefixEnd_2035428 := by exact prefixLift 2035428
  have htrace : WordTrace (prefixWord ++ tailWord_2035428) baseStart_2035428 baseEnd_2035428 := by
    simpa [prefixWord, tailWord_2035428, baseEnd_2035428] using wordTrace_append hprefix tailTrace_2035428
  have hstable : (prefixWord ++ tailWord_2035428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035428).length < 2 ^ (prefixWord ++ tailWord_2035428).sum := by decide
  have hdescent : baseEnd_2035428 < baseStart_2035428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035446 : List Nat := [5, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_2035446 : Nat := 118140960795 + 2035446 * 2 ^ 59
def prefixEnd_2035446 : Nat := 4983230072969 + 3 ^ 40 * 2035446 * 2
def baseEnd_2035446 : Nat := 1045162144271548541864161

theorem tailTrace_2035446 : CollatzResearch.WordTrace tailWord_2035446 prefixEnd_2035446 1045162144271548541864161 := by
  unfold tailWord_2035446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4639925911495890209121887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49492543055956162230633461 4639925911495890209121887)
  ·
    refine ⟨6959888867243835313682831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4639925911495890209121887 6959888867243835313682831)
    ·
      refine ⟨10439833300865752970524247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6959888867243835313682831 10439833300865752970524247)
      ·
        refine ⟨15659749951298629455786371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10439833300865752970524247 15659749951298629455786371)
        ·
          refine ⟨23489624926947944183679557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15659749951298629455786371 23489624926947944183679557)
          ·
            refine ⟨4404304673802739534439917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23489624926947944183679557 4404304673802739534439917)
            ·
              refine ⟨1651614252676027325414969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4404304673802739534439917 1651614252676027325414969)
              ·
                refine ⟨1238710689507020494061227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651614252676027325414969 1238710689507020494061227)
                ·
                  refine ⟨1858066034260530741091841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238710689507020494061227 1858066034260530741091841)
                  ·
                    refine ⟨1393549525695398055818881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1858066034260530741091841 1393549525695398055818881)
                    ·
                      refine ⟨1045162144271548541864161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393549525695398055818881 1045162144271548541864161)
                      ·
                        rfl

theorem cell23_2035446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_2035446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035446 prefixEnd_2035446 := by exact prefixLift 2035446
  have htrace : WordTrace (prefixWord ++ tailWord_2035446) baseStart_2035446 baseEnd_2035446 := by
    simpa [prefixWord, tailWord_2035446, baseEnd_2035446] using wordTrace_append hprefix tailTrace_2035446
  have hstable : (prefixWord ++ tailWord_2035446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035446).length < 2 ^ (prefixWord ++ tailWord_2035446).sum := by decide
  have hdescent : baseEnd_2035446 < baseStart_2035446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035471 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 3]
def baseStart_2035471 : Nat := 118140960795 + 2035471 * 2 ^ 59
def prefixEnd_2035471 : Nat := 4983230072969 + 3 ^ 40 * 2035471 * 2
def baseEnd_2035471 : Nat := 1045174981287910944051545

theorem tailTrace_2035471 : CollatzResearch.WordTrace tailWord_2035471 prefixEnd_2035471 1045174981287910944051545 := by
  unfold tailWord_2035471
  simp only [CollatzResearch.WordTrace]
  refine ⟨74239726408843672615610267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49493150939229115077073511 74239726408843672615610267)
  ·
    refine ⟨111359589613265508923415401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74239726408843672615610267 111359589613265508923415401)
    ·
      refine ⟨83519692209949131692561551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111359589613265508923415401 83519692209949131692561551)
      ·
        refine ⟨125279538314923697538842327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83519692209949131692561551 125279538314923697538842327)
        ·
          refine ⟨187919307472385546308263491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125279538314923697538842327 187919307472385546308263491)
          ·
            refine ⟨281878961208578319462395237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187919307472385546308263491 281878961208578319462395237)
            ·
              refine ⟨52852305226608434899199107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281878961208578319462395237 52852305226608434899199107)
              ·
                refine ⟨79278457839912652348798661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52852305226608434899199107 79278457839912652348798661)
                ·
                  refine ⟨14864710844983622315399749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79278457839912652348798661 14864710844983622315399749)
                  ·
                    refine ⟨2787133283434429184137453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14864710844983622315399749 2787133283434429184137453)
                    ·
                      refine ⟨1045174981287910944051545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787133283434429184137453 1045174981287910944051545)
                      ·
                        rfl

theorem cell23_2035471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 3].length) (baseStart_2035471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035471 prefixEnd_2035471 := by exact prefixLift 2035471
  have htrace : WordTrace (prefixWord ++ tailWord_2035471) baseStart_2035471 baseEnd_2035471 := by
    simpa [prefixWord, tailWord_2035471, baseEnd_2035471] using wordTrace_append hprefix tailTrace_2035471
  have hstable : (prefixWord ++ tailWord_2035471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035471).length < 2 ^ (prefixWord ++ tailWord_2035471).sum := by decide
  have hdescent : baseEnd_2035471 < baseStart_2035471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035538 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2035538 : Nat := 118140960795 + 2035538 * 2 ^ 59
def prefixEnd_2035538 : Nat := 4983230072969 + 3 ^ 40 * 2035538 * 2
def baseEnd_2035538 : Nat := 348403128163920727304579

theorem tailTrace_2035538 : CollatzResearch.WordTrace tailWord_2035538 prefixEnd_2035538 348403128163920727304579 := by
  unfold tailWord_2035538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560542524900235764574817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49494780066400628705532845 18560542524900235764574817)
  ·
    refine ⟨13920406893675176823431113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18560542524900235764574817 13920406893675176823431113)
    ·
      refine ⟨10440305170256382617573335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13920406893675176823431113 10440305170256382617573335)
      ·
        refine ⟨15660457755384573926360003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10440305170256382617573335 15660457755384573926360003)
        ·
          refine ⟨23490686633076860889540005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15660457755384573926360003 23490686633076860889540005)
          ·
            refine ⟨4404503743701911416788751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23490686633076860889540005 4404503743701911416788751)
            ·
              refine ⟨6606755615552867125183127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404503743701911416788751 6606755615552867125183127)
              ·
                refine ⟨9910133423329300687774691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6606755615552867125183127 9910133423329300687774691)
                ·
                  refine ⟨14865200134993951031662037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910133423329300687774691 14865200134993951031662037)
                  ·
                    refine ⟨348403128163920727304579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14865200134993951031662037 348403128163920727304579)
                    ·
                      rfl

theorem cell23_2035538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2035538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035538 prefixEnd_2035538 := by exact prefixLift 2035538
  have htrace : WordTrace (prefixWord ++ tailWord_2035538) baseStart_2035538 baseEnd_2035538 := by
    simpa [prefixWord, tailWord_2035538, baseEnd_2035538] using wordTrace_append hprefix tailTrace_2035538
  have hstable : (prefixWord ++ tailWord_2035538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035538).length < 2 ^ (prefixWord ++ tailWord_2035538).sum := by decide
  have hdescent : baseEnd_2035538 < baseStart_2035538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035561 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 5]
def baseStart_2035561 : Nat := 118140960795 + 2035561 * 2 ^ 59
def prefixEnd_2035561 : Nat := 4983230072969 + 3 ^ 40 * 2035561 * 2
def baseEnd_2035561 : Nat := 1045221194546815591926131

theorem tailTrace_2035561 : CollatzResearch.WordTrace tailWord_2035561 prefixEnd_2035561 1045221194546815591926131 := by
  unfold tailWord_2035561
  simp only [CollatzResearch.WordTrace]
  refine ⟨74243008978517617986386537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49495339319011745324257691 74243008978517617986386537)
  ·
    refine ⟨55682256733888213489789903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74243008978517617986386537 55682256733888213489789903)
    ·
      refine ⟨83523385100832320234684855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55682256733888213489789903 83523385100832320234684855)
      ·
        refine ⟨125285077651248480352027283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83523385100832320234684855 125285077651248480352027283)
        ·
          refine ⟨187927616476872720528040925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125285077651248480352027283 187927616476872720528040925)
          ·
            refine ⟨70472856178827270198015347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187927616476872720528040925 70472856178827270198015347)
            ·
              refine ⟨105709284268240905297023021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70472856178827270198015347 105709284268240905297023021)
              ·
                refine ⟨39640981600590339486383633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105709284268240905297023021 39640981600590339486383633)
                ·
                  refine ⟨29730736200442754614787725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39640981600590339486383633 29730736200442754614787725)
                  ·
                    refine ⟨11149026075166032980545397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29730736200442754614787725 11149026075166032980545397)
                    ·
                      refine ⟨1045221194546815591926131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11149026075166032980545397 1045221194546815591926131)
                      ·
                        rfl

theorem cell23_2035561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_2035561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035561 prefixEnd_2035561 := by exact prefixLift 2035561
  have htrace : WordTrace (prefixWord ++ tailWord_2035561) baseStart_2035561 baseEnd_2035561 := by
    simpa [prefixWord, tailWord_2035561, baseEnd_2035561] using wordTrace_append hprefix tailTrace_2035561
  have hstable : (prefixWord ++ tailWord_2035561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035561).length < 2 ^ (prefixWord ++ tailWord_2035561).sum := by decide
  have hdescent : baseEnd_2035561 < baseStart_2035561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035571 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_2035571 : Nat := 118140960795 + 2035571 * 2 ^ 59
def prefixEnd_2035571 : Nat := 4983230072969 + 3 ^ 40 * 2035571 * 2
def baseEnd_2035571 : Nat := 1045226329353360552801085

theorem tailTrace_2035571 : CollatzResearch.WordTrace tailWord_2035571 prefixEnd_2035571 1045226329353360552801085 := by
  unfold tailWord_2035571
  simp only [CollatzResearch.WordTrace]
  refine ⟨74243373708481389694250567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49495582472320926462833711 74243373708481389694250567)
  ·
    refine ⟨111365060562722084541375851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74243373708481389694250567 111365060562722084541375851)
    ·
      refine ⟨167047590844083126812063777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111365060562722084541375851 167047590844083126812063777)
      ·
        refine ⟨125285693133062345109047833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167047590844083126812063777 125285693133062345109047833)
        ·
          refine ⟨93964269849796758831785875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125285693133062345109047833 93964269849796758831785875)
          ·
            refine ⟨140946404774695138247678813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93964269849796758831785875 140946404774695138247678813)
            ·
              refine ⟨52854901790510676842879555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140946404774695138247678813 52854901790510676842879555)
              ·
                refine ⟨79282352685766015264319333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52854901790510676842879555 79282352685766015264319333)
                ·
                  refine ⟨14865441128581127862059875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79282352685766015264319333 14865441128581127862059875)
                  ·
                    refine ⟨22298161692871691793089813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14865441128581127862059875 22298161692871691793089813)
                    ·
                      refine ⟨1045226329353360552801085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22298161692871691793089813 1045226329353360552801085)
                      ·
                        rfl

theorem cell23_2035571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_2035571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035571 prefixEnd_2035571 := by exact prefixLift 2035571
  have htrace : WordTrace (prefixWord ++ tailWord_2035571) baseStart_2035571 baseEnd_2035571 := by
    simpa [prefixWord, tailWord_2035571, baseEnd_2035571] using wordTrace_append hprefix tailTrace_2035571
  have hstable : (prefixWord ++ tailWord_2035571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035571).length < 2 ^ (prefixWord ++ tailWord_2035571).sum := by decide
  have hdescent : baseEnd_2035571 < baseStart_2035571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035578 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_2035578 : Nat := 118140960795 + 2035578 * 2 ^ 59
def prefixEnd_2035578 : Nat := 4983230072969 + 3 ^ 40 * 2035578 * 2
def baseEnd_2035578 : Nat := 1045229923717942025413553

theorem tailTrace_2035578 : CollatzResearch.WordTrace tailWord_2035578 prefixEnd_2035578 1045229923717942025413553 := by
  unfold tailWord_2035578
  simp only [CollatzResearch.WordTrace]
  refine ⟨18560907254864007472438847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49495752679637353259836925 18560907254864007472438847)
  ·
    refine ⟨27841360882296011208658271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18560907254864007472438847 27841360882296011208658271)
    ·
      refine ⟨41762041323444016812987407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27841360882296011208658271 41762041323444016812987407)
      ·
        refine ⟨62643061985166025219481111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41762041323444016812987407 62643061985166025219481111)
        ·
          refine ⟨93964592977749037829221667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62643061985166025219481111 93964592977749037829221667)
          ·
            refine ⟨140946889466623556743832501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93964592977749037829221667 140946889466623556743832501)
            ·
              refine ⟨13213770887495958444734297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140946889466623556743832501 13213770887495958444734297)
              ·
                refine ⟨9910328165621968833550723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13213770887495958444734297 9910328165621968833550723)
                ·
                  refine ⟨14865492248432953250326085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9910328165621968833550723 14865492248432953250326085)
                  ·
                    refine ⟨2787279796581178734436141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14865492248432953250326085 2787279796581178734436141)
                    ·
                      refine ⟨1045229923717942025413553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787279796581178734436141 1045229923717942025413553)
                      ·
                        rfl

theorem cell23_2035578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_2035578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035578 prefixEnd_2035578 := by exact prefixLift 2035578
  have htrace : WordTrace (prefixWord ++ tailWord_2035578) baseStart_2035578 baseEnd_2035578 := by
    simpa [prefixWord, tailWord_2035578, baseEnd_2035578] using wordTrace_append hprefix tailTrace_2035578
  have hstable : (prefixWord ++ tailWord_2035578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035578).length < 2 ^ (prefixWord ++ tailWord_2035578).sum := by decide
  have hdescent : baseEnd_2035578 < baseStart_2035578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035612 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2035612 : Nat := 118140960795 + 2035612 * 2 ^ 59
def prefixEnd_2035612 : Nat := 4983230072969 + 3 ^ 40 * 2035612 * 2
def baseEnd_2035612 : Nat := 1045247382060194892388397

theorem tailTrace_2035612 : CollatzResearch.WordTrace tailWord_2035612 prefixEnd_2035612 1045247382060194892388397 := by
  unfold tailWord_2035612
  simp only [CollatzResearch.WordTrace]
  refine ⟨37122434550666426848246545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49496579400888569130995393 37122434550666426848246545)
  ·
    refine ⟨27841825912999820136184909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37122434550666426848246545 27841825912999820136184909)
    ·
      refine ⟨10440684717374932551069341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27841825912999820136184909 10440684717374932551069341)
      ·
        refine ⟨3915256769015599706651003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10440684717374932551069341 3915256769015599706651003)
        ·
          refine ⟨5872885153523399559976505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3915256769015599706651003 5872885153523399559976505)
          ·
            refine ⟨4404663865142549669982379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5872885153523399559976505 4404663865142549669982379)
            ·
              refine ⟨6606995797713824504973569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404663865142549669982379 6606995797713824504973569)
              ·
                refine ⟨4955246848285368378730177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6606995797713824504973569 4955246848285368378730177)
                ·
                  refine ⟨3716435136214026284047633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955246848285368378730177 3716435136214026284047633)
                  ·
                    refine ⟨2787326352160519713035725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716435136214026284047633 2787326352160519713035725)
                    ·
                      refine ⟨1045247382060194892388397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787326352160519713035725 1045247382060194892388397)
                      ·
                        rfl

theorem cell23_2035612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2035612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035612 prefixEnd_2035612 := by exact prefixLift 2035612
  have htrace : WordTrace (prefixWord ++ tailWord_2035612) baseStart_2035612 baseEnd_2035612 := by
    simpa [prefixWord, tailWord_2035612, baseEnd_2035612] using wordTrace_append hprefix tailTrace_2035612
  have hstable : (prefixWord ++ tailWord_2035612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035612).length < 2 ^ (prefixWord ++ tailWord_2035612).sum := by decide
  have hdescent : baseEnd_2035612 < baseStart_2035612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035625 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 3]
def baseStart_2035625 : Nat := 118140960795 + 2035625 * 2 ^ 59
def prefixEnd_2035625 : Nat := 4983230072969 + 3 ^ 40 * 2035625 * 2
def baseEnd_2035625 : Nat := 1045254057308703341525837

theorem tailTrace_2035625 : CollatzResearch.WordTrace tailWord_2035625 prefixEnd_2035625 1045254057308703341525837 := by
  unfold tailWord_2035625
  simp only [CollatzResearch.WordTrace]
  refine ⟨74245343250285756916716329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49496895500190504611144219 74245343250285756916716329)
  ·
    refine ⟨55684007437714317687537247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74245343250285756916716329 55684007437714317687537247)
    ·
      refine ⟨83526011156571476531305871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55684007437714317687537247 83526011156571476531305871)
      ·
        refine ⟨125289016734857214796958807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83526011156571476531305871 125289016734857214796958807)
        ·
          refine ⟨187933525102285822195438211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125289016734857214796958807 187933525102285822195438211)
          ·
            refine ⟨281900287653428733293157317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187933525102285822195438211 281900287653428733293157317)
            ·
              refine ⟨52856303935017887492466997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281900287653428733293157317 52856303935017887492466997)
              ·
                refine ⟨4955278493907926952418781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52856303935017887492466997 4955278493907926952418781)
                ·
                  refine ⟨1858229435215472607157043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4955278493907926952418781 1858229435215472607157043)
                  ·
                    refine ⟨2787344152823208910735565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1858229435215472607157043 2787344152823208910735565)
                    ·
                      refine ⟨1045254057308703341525837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787344152823208910735565 1045254057308703341525837)
                      ·
                        rfl

theorem cell23_2035625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_2035625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035625 prefixEnd_2035625 := by exact prefixLift 2035625
  have htrace : WordTrace (prefixWord ++ tailWord_2035625) baseStart_2035625 baseEnd_2035625 := by
    simpa [prefixWord, tailWord_2035625, baseEnd_2035625] using wordTrace_append hprefix tailTrace_2035625
  have hstable : (prefixWord ++ tailWord_2035625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035625).length < 2 ^ (prefixWord ++ tailWord_2035625).sum := by decide
  have hdescent : baseEnd_2035625 < baseStart_2035625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035635 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 4, 3, 2]
def baseStart_2035635 : Nat := 118140960795 + 2035635 * 2 ^ 59
def prefixEnd_2035635 : Nat := 4983230072969 + 3 ^ 40 * 2035635 * 2
def baseEnd_2035635 : Nat := 1045259192115248302400791

theorem tailTrace_2035635 : CollatzResearch.WordTrace tailWord_2035635 prefixEnd_2035635 1045259192115248302400791 := by
  unfold tailWord_2035635
  simp only [CollatzResearch.WordTrace]
  refine ⟨74245707980249528624580359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49497138653499685749720239 74245707980249528624580359)
  ·
    refine ⟨111368561970374292936870539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74245707980249528624580359 111368561970374292936870539)
    ·
      refine ⟨167052842955561439405305809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111368561970374292936870539 167052842955561439405305809)
      ·
        refine ⟨125289632216671079553979357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167052842955561439405305809 125289632216671079553979357)
        ·
          refine ⟨46983612081251654832742259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125289632216671079553979357 46983612081251654832742259)
          ·
            refine ⟨70475418121877482249113389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46983612081251654832742259 70475418121877482249113389)
            ·
              refine ⟨26428281795704055843417521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70475418121877482249113389 26428281795704055843417521)
              ·
                refine ⟨19821211346778041882563141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26428281795704055843417521 19821211346778041882563141)
                ·
                  refine ⟨3716477127520882852980589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19821211346778041882563141 3716477127520882852980589)
                  ·
                    refine ⟨1393678922820331069867721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716477127520882852980589 1393678922820331069867721)
                    ·
                      refine ⟨1045259192115248302400791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393678922820331069867721 1045259192115248302400791)
                      ·
                        rfl

theorem cell23_2035635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3, 2].length) (baseStart_2035635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035635 prefixEnd_2035635 := by exact prefixLift 2035635
  have htrace : WordTrace (prefixWord ++ tailWord_2035635) baseStart_2035635 baseEnd_2035635 := by
    simpa [prefixWord, tailWord_2035635, baseEnd_2035635] using wordTrace_append hprefix tailTrace_2035635
  have hstable : (prefixWord ++ tailWord_2035635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035635).length < 2 ^ (prefixWord ++ tailWord_2035635).sum := by decide
  have hdescent : baseEnd_2035635 < baseStart_2035635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035645 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_2035645 : Nat := 118140960795 + 2035645 * 2 ^ 59
def prefixEnd_2035645 : Nat := 4983230072969 + 3 ^ 40 * 2035645 * 2
def baseEnd_2035645 : Nat := 348421442307264421091915

theorem tailTrace_2035645 : CollatzResearch.WordTrace tailWord_2035645 prefixEnd_2035645 348421442307264421091915 := by
  unfold tailWord_2035645
  simp only [CollatzResearch.WordTrace]
  refine ⟨74246072710213300332444389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49497381806808866888296259 74246072710213300332444389)
  ·
    refine ⟨13921138633164993812333323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74246072710213300332444389 13921138633164993812333323)
    ·
      refine ⟨20881707949747490718499985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921138633164993812333323 20881707949747490718499985)
      ·
        refine ⟨15661280962310618038874989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20881707949747490718499985 15661280962310618038874989)
        ·
          refine ⟨5872980360866481764578121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15661280962310618038874989 5872980360866481764578121)
          ·
            refine ⟨4404735270649861323433591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5872980360866481764578121 4404735270649861323433591)
            ·
              refine ⟨6607102905974791985150387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4404735270649861323433591 6607102905974791985150387)
              ·
                refine ⟨9910654358962187977725581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607102905974791985150387 9910654358962187977725581)
                ·
                  refine ⟨3716495384610820491647093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9910654358962187977725581 3716495384610820491647093)
                  ·
                    refine ⟨348421442307264421091915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3716495384610820491647093 348421442307264421091915)
                    ·
                      rfl

theorem cell23_2035645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_2035645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035645 prefixEnd_2035645 := by exact prefixLift 2035645
  have htrace : WordTrace (prefixWord ++ tailWord_2035645) baseStart_2035645 baseEnd_2035645 := by
    simpa [prefixWord, tailWord_2035645, baseEnd_2035645] using wordTrace_append hprefix tailTrace_2035645
  have hstable : (prefixWord ++ tailWord_2035645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035645).length < 2 ^ (prefixWord ++ tailWord_2035645).sum := by decide
  have hdescent : baseEnd_2035645 < baseStart_2035645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035658 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_2035658 : Nat := 118140960795 + 2035658 * 2 ^ 59
def prefixEnd_2035658 : Nat := 4983230072969 + 3 ^ 40 * 2035658 * 2
def baseEnd_2035658 : Nat := 348423667390100570804395

theorem tailTrace_2035658 : CollatzResearch.WordTrace tailWord_2035658 prefixEnd_2035658 348423667390100570804395 := by
  unfold tailWord_2035658
  simp only [CollatzResearch.WordTrace]
  refine ⟨18561636714791550888166907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49497697906110802368445085 18561636714791550888166907)
  ·
    refine ⟨27842455072187326332250361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18561636714791550888166907 27842455072187326332250361)
    ·
      refine ⟨20881841304140494749187771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27842455072187326332250361 20881841304140494749187771)
      ·
        refine ⟨31322761956210742123781657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20881841304140494749187771 31322761956210742123781657)
        ·
          refine ⟨23492071467158056592836243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31322761956210742123781657 23492071467158056592836243)
          ·
            refine ⟨35238107200737084889254365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23492071467158056592836243 35238107200737084889254365)
            ·
              refine ⟨13214290200276406833470387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35238107200737084889254365 13214290200276406833470387)
              ·
                refine ⟨19821435300414610250205581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13214290200276406833470387 19821435300414610250205581)
                ·
                  refine ⟨7433038237655478843827093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19821435300414610250205581 7433038237655478843827093)
                  ·
                    refine ⟨348423667390100570804395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7433038237655478843827093 348423667390100570804395)
                    ·
                      rfl

theorem cell23_2035658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_2035658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035658 prefixEnd_2035658 := by exact prefixLift 2035658
  have htrace : WordTrace (prefixWord ++ tailWord_2035658) baseStart_2035658 baseEnd_2035658 := by
    simpa [prefixWord, tailWord_2035658, baseEnd_2035658] using wordTrace_append hprefix tailTrace_2035658
  have hstable : (prefixWord ++ tailWord_2035658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035658).length < 2 ^ (prefixWord ++ tailWord_2035658).sum := by decide
  have hdescent : baseEnd_2035658 < baseStart_2035658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035662 : List Nat := [4, 1, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_2035662 : Nat := 118140960795 + 2035662 * 2 ^ 59
def prefixEnd_2035662 : Nat := 4983230072969 + 3 ^ 40 * 2035662 * 2
def baseEnd_2035662 : Nat := 348424352030973232254389

theorem tailTrace_2035662 : CollatzResearch.WordTrace tailWord_2035662 prefixEnd_2035662 348424352030973232254389 := by
  unfold tailWord_2035662
  simp only [CollatzResearch.WordTrace]
  refine ⟨9280836593893964029476655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49497795167434474823875493 9280836593893964029476655)
  ·
    refine ⟨13921254890840946044214983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9280836593893964029476655 13921254890840946044214983)
    ·
      refine ⟨20881882336261419066322475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13921254890840946044214983 20881882336261419066322475)
      ·
        refine ⟨31322823504392128599483713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20881882336261419066322475 31322823504392128599483713)
        ·
          refine ⟨23492117628294096449612785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31322823504392128599483713 23492117628294096449612785)
          ·
            refine ⟨17619088221220572337209589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23492117628294096449612785 17619088221220572337209589)
            ·
              refine ⟨1651789520739428656613399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17619088221220572337209589 1651789520739428656613399)
              ·
                refine ⟨2477684281109142984920099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651789520739428656613399 2477684281109142984920099)
                ·
                  refine ⟨3716526421663714477380149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477684281109142984920099 3716526421663714477380149)
                  ·
                    refine ⟨348424352030973232254389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3716526421663714477380149 348424352030973232254389)
                    ·
                      rfl

theorem cell23_2035662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_2035662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035662 prefixEnd_2035662 := by exact prefixLift 2035662
  have htrace : WordTrace (prefixWord ++ tailWord_2035662) baseStart_2035662 baseEnd_2035662 := by
    simpa [prefixWord, tailWord_2035662, baseEnd_2035662] using wordTrace_append hprefix tailTrace_2035662
  have hstable : (prefixWord ++ tailWord_2035662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035662).length < 2 ^ (prefixWord ++ tailWord_2035662).sum := by decide
  have hdescent : baseEnd_2035662 < baseStart_2035662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035670 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2035670 : Nat := 118140960795 + 2035670 * 2 ^ 59
def prefixEnd_2035670 : Nat := 4983230072969 + 3 ^ 40 * 2035670 * 2
def baseEnd_2035670 : Nat := 348425721312718555154377

theorem tailTrace_2035670 : CollatzResearch.WordTrace tailWord_2035670 prefixEnd_2035670 348425721312718555154377 := by
  unfold tailWord_2035670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4640436533445170600131529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49497989690081819734736309 4640436533445170600131529)
  ·
    refine ⟨3480327400083877950098647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4640436533445170600131529 3480327400083877950098647)
    ·
      refine ⟨5220491100125816925147971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3480327400083877950098647 5220491100125816925147971)
      ·
        refine ⟨7830736650188725387721957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5220491100125816925147971 7830736650188725387721957)
        ·
          refine ⟨1468263121910386010197867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7830736650188725387721957 1468263121910386010197867)
          ·
            refine ⟨2202394682865579015296801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468263121910386010197867 2202394682865579015296801)
            ·
              refine ⟨1651796012149184261472601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202394682865579015296801 1651796012149184261472601)
              ·
                refine ⟨1238847009111888196104451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1651796012149184261472601 1238847009111888196104451)
                ·
                  refine ⟨1858270513667832294156677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1238847009111888196104451 1858270513667832294156677)
                  ·
                    refine ⟨348425721312718555154377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858270513667832294156677 348425721312718555154377)
                    ·
                      rfl

theorem cell23_2035670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2035670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035670 prefixEnd_2035670 := by exact prefixLift 2035670
  have htrace : WordTrace (prefixWord ++ tailWord_2035670) baseStart_2035670 baseEnd_2035670 := by
    simpa [prefixWord, tailWord_2035670, baseEnd_2035670] using wordTrace_append hprefix tailTrace_2035670
  have hstable : (prefixWord ++ tailWord_2035670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035670).length < 2 ^ (prefixWord ++ tailWord_2035670).sum := by decide
  have hdescent : baseEnd_2035670 < baseStart_2035670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035695 : List Nat := [1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 4]
def baseStart_2035695 : Nat := 118140960795 + 2035695 * 2 ^ 59
def prefixEnd_2035695 : Nat := 4983230072969 + 3 ^ 40 * 2035695 * 2
def baseEnd_2035695 : Nat := 1045290000954518067650515

theorem tailTrace_2035695 : CollatzResearch.WordTrace tailWord_2035695 prefixEnd_2035695 1045290000954518067650515 := by
  unfold tailWord_2035695
  simp only [CollatzResearch.WordTrace]
  refine ⟨74247896360032158871764539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49498597573354772581176359 74247896360032158871764539)
  ·
    refine ⟨111371844540048238307646809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74247896360032158871764539 111371844540048238307646809)
    ·
      refine ⟨83528883405036178730735107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111371844540048238307646809 83528883405036178730735107)
      ·
        refine ⟨125293325107554268096102661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83528883405036178730735107 125293325107554268096102661)
        ·
          refine ⟨23492498457666425268019249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125293325107554268096102661 23492498457666425268019249)
          ·
            refine ⟨17619373843249818951014437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23492498457666425268019249 17619373843249818951014437)
            ·
              refine ⟨3303632595609341053315207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17619373843249818951014437 3303632595609341053315207)
              ·
                refine ⟨4955448893414011579972811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303632595609341053315207 4955448893414011579972811)
                ·
                  refine ⟨7433173340121017369959217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4955448893414011579972811 7433173340121017369959217)
                  ·
                    refine ⟨5574880005090763027469413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7433173340121017369959217 5574880005090763027469413)
                    ·
                      refine ⟨1045290000954518067650515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5574880005090763027469413 1045290000954518067650515)
                      ·
                        rfl

theorem cell23_2035695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 4].length) (baseStart_2035695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035695 prefixEnd_2035695 := by exact prefixLift 2035695
  have htrace : WordTrace (prefixWord ++ tailWord_2035695) baseStart_2035695 baseEnd_2035695 := by
    simpa [prefixWord, tailWord_2035695, baseEnd_2035695] using wordTrace_append hprefix tailTrace_2035695
  have hstable : (prefixWord ++ tailWord_2035695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035695).length < 2 ^ (prefixWord ++ tailWord_2035695).sum := by decide
  have hdescent : baseEnd_2035695 < baseStart_2035695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035705 : List Nat := [1, 2, 1, 3, 1, 5, 3, 7]
def baseStart_2035705 : Nat := 118140960795 + 2035705 * 2 ^ 59
def prefixEnd_2035705 : Nat := 4983230072969 + 3 ^ 40 * 2035705 * 2
def baseEnd_2035705 : Nat := 38714634657817149204647

theorem tailTrace_2035705 : CollatzResearch.WordTrace tailWord_2035705 prefixEnd_2035705 38714634657817149204647 := by
  unfold tailWord_2035705
  simp only [CollatzResearch.WordTrace]
  refine ⟨74248261089995930579628569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49498840726663953719752379 74248261089995930579628569)
  ·
    refine ⟨55686195817496947934721427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74248261089995930579628569 55686195817496947934721427)
    ·
      refine ⟨83529293726245421902082141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55686195817496947934721427 83529293726245421902082141)
      ·
        refine ⟨31323485147342033213280803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83529293726245421902082141 31323485147342033213280803)
        ·
          refine ⟨46985227721013049819921205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31323485147342033213280803 46985227721013049819921205)
          ·
            refine ⟨4404865098844973420617613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46985227721013049819921205 4404865098844973420617613)
            ·
              refine ⟨1651824412066865032731605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4404865098844973420617613 1651824412066865032731605)
              ·
                refine ⟨38714634657817149204647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1651824412066865032731605 38714634657817149204647)
                ·
                  rfl

theorem cell23_2035705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 3, 7].length) (baseStart_2035705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035705 prefixEnd_2035705 := by exact prefixLift 2035705
  have htrace : WordTrace (prefixWord ++ tailWord_2035705) baseStart_2035705 baseEnd_2035705 := by
    simpa [prefixWord, tailWord_2035705, baseEnd_2035705] using wordTrace_append hprefix tailTrace_2035705
  have hstable : (prefixWord ++ tailWord_2035705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035705).length < 2 ^ (prefixWord ++ tailWord_2035705).sum := by decide
  have hdescent : baseEnd_2035705 < baseStart_2035705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035719 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 1, 2, 3]
def baseStart_2035719 : Nat := 118140960795 + 2035719 * 2 ^ 59
def prefixEnd_2035719 : Nat := 4983230072969 + 3 ^ 40 * 2035719 * 2
def baseEnd_2035719 : Nat := 1045302324490225973750405

theorem tailTrace_2035719 : CollatzResearch.WordTrace tailWord_2035719 prefixEnd_2035719 1045302324490225973750405 := by
  unfold tailWord_2035719
  simp only [CollatzResearch.WordTrace]
  refine ⟨74248771711945210970638211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49499181141296807313758807 74248771711945210970638211)
  ·
    refine ⟨111373157567917816455957317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74248771711945210970638211 111373157567917816455957317)
    ·
      refine ⟨20882467043984590585491997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111373157567917816455957317 20882467043984590585491997)
      ·
        refine ⟨7830925141494221469559499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20882467043984590585491997 7830925141494221469559499)
        ·
          refine ⟨11746387712241332204339249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7830925141494221469559499 11746387712241332204339249)
          ·
            refine ⟨8809790784180999153254437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11746387712241332204339249 8809790784180999153254437)
            ·
              refine ⟨1651835772033937341235207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8809790784180999153254437 1651835772033937341235207)
              ·
                refine ⟨2477753658050906011852811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1651835772033937341235207 2477753658050906011852811)
                ·
                  refine ⟨3716630487076359017779217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477753658050906011852811 3716630487076359017779217)
                  ·
                    refine ⟨2787472865307269263334413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3716630487076359017779217 2787472865307269263334413)
                    ·
                      refine ⟨1045302324490225973750405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787472865307269263334413 1045302324490225973750405)
                      ·
                        rfl

theorem cell23_2035719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_2035719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035719 prefixEnd_2035719 := by exact prefixLift 2035719
  have htrace : WordTrace (prefixWord ++ tailWord_2035719) baseStart_2035719 baseEnd_2035719 := by
    simpa [prefixWord, tailWord_2035719, baseEnd_2035719] using wordTrace_append hprefix tailTrace_2035719
  have hstable : (prefixWord ++ tailWord_2035719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035719).length < 2 ^ (prefixWord ++ tailWord_2035719).sum := by decide
  have hdescent : baseEnd_2035719 < baseStart_2035719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035728 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5]
def baseStart_2035728 : Nat := 118140960795 + 2035728 * 2 ^ 59
def prefixEnd_2035728 : Nat := 4983230072969 + 3 ^ 40 * 2035728 * 2
def baseEnd_2035728 : Nat := 1045306945816116438537863

theorem tailTrace_2035728 : CollatzResearch.WordTrace tailWord_2035728 prefixEnd_2035728 1045306945816116438537863 := by
  unfold tailWord_2035728
  simp only [CollatzResearch.WordTrace]
  refine ⟨37124549984456302753857919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49499399979275070338477225 37124549984456302753857919)
  ·
    refine ⟨55686824976684454130786879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37124549984456302753857919 55686824976684454130786879)
    ·
      refine ⟨83530237465026681196180319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55686824976684454130786879 83530237465026681196180319)
      ·
        refine ⟨125295356197540021794270479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83530237465026681196180319 125295356197540021794270479)
        ·
          refine ⟨187943034296310032691405719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125295356197540021794270479 187943034296310032691405719)
          ·
            refine ⟨281914551444465049037108579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187943034296310032691405719 281914551444465049037108579)
            ·
              refine ⟨422871827166697573555662869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281914551444465049037108579 422871827166697573555662869)
              ·
                refine ⟨19822116898438948760421697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 422871827166697573555662869 19822116898438948760421697)
                ·
                  refine ⟨14866587673829211570316273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19822116898438948760421697 14866587673829211570316273)
                  ·
                    refine ⟨11149940755371908677737205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14866587673829211570316273 11149940755371908677737205)
                    ·
                      refine ⟨1045306945816116438537863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11149940755371908677737205 1045306945816116438537863)
                      ·
                        rfl

theorem cell23_2035728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_2035728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035728 prefixEnd_2035728 := by exact prefixLift 2035728
  have htrace : WordTrace (prefixWord ++ tailWord_2035728) baseStart_2035728 baseEnd_2035728 := by
    simpa [prefixWord, tailWord_2035728, baseEnd_2035728] using wordTrace_append hprefix tailTrace_2035728
  have hstable : (prefixWord ++ tailWord_2035728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035728).length < 2 ^ (prefixWord ++ tailWord_2035728).sum := by decide
  have hdescent : baseEnd_2035728 < baseStart_2035728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035772 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 3, 4, 2]
def baseStart_2035772 : Nat := 118140960795 + 2035772 * 2 ^ 59
def prefixEnd_2035772 : Nat := 4983230072969 + 3 ^ 40 * 2035772 * 2
def baseEnd_2035772 : Nat := 1045329538964914266387661

theorem tailTrace_2035772 : CollatzResearch.WordTrace tailWord_2035772 prefixEnd_2035772 1045329538964914266387661 := by
  unfold tailWord_2035772
  simp only [CollatzResearch.WordTrace]
  refine ⟨37125352390376600511158785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49500469853835467348211713 37125352390376600511158785)
  ·
    refine ⟨27844014292782450383369089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37125352390376600511158785 27844014292782450383369089)
    ·
      refine ⟨20883010719586837787526817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27844014292782450383369089 20883010719586837787526817)
      ·
        refine ⟨15662258039690128340645113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20883010719586837787526817 15662258039690128340645113)
        ·
          refine ⟨11746693529767596255483835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15662258039690128340645113 11746693529767596255483835)
          ·
            refine ⟨17620040294651394383225753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11746693529767596255483835 17620040294651394383225753)
            ·
              refine ⟨13215030220988545787419315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17620040294651394383225753 13215030220988545787419315)
              ·
                refine ⟨19822545331482818681128973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215030220988545787419315 19822545331482818681128973)
                ·
                  refine ⟨7433454499306057005423365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19822545331482818681128973 7433454499306057005423365)
                  ·
                    refine ⟨1393772718619885688516881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7433454499306057005423365 1393772718619885688516881)
                    ·
                      refine ⟨1045329538964914266387661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393772718619885688516881 1045329538964914266387661)
                      ·
                        rfl

theorem cell23_2035772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_2035772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035772 prefixEnd_2035772 := by exact prefixLift 2035772
  have htrace : WordTrace (prefixWord ++ tailWord_2035772) baseStart_2035772 baseEnd_2035772 := by
    simpa [prefixWord, tailWord_2035772, baseEnd_2035772] using wordTrace_append hprefix tailTrace_2035772
  have hstable : (prefixWord ++ tailWord_2035772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035772).length < 2 ^ (prefixWord ++ tailWord_2035772).sum := by decide
  have hdescent : baseEnd_2035772 < baseStart_2035772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035810 : List Nat := [3, 3, 2, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2035810 : Nat := 118140960795 + 2035810 * 2 ^ 59
def prefixEnd_2035810 : Nat := 4983230072969 + 3 ^ 40 * 2035810 * 2
def baseEnd_2035810 : Nat := 1045349051229785117712487

theorem tailTrace_2035810 : CollatzResearch.WordTrace tailWord_2035810 prefixEnd_2035810 1045349051229785117712487 := by
  unfold tailWord_2035810
  simp only [CollatzResearch.WordTrace]
  refine ⟨18563022688653883378050221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49501393836410355674800589 18563022688653883378050221)
  ·
    refine ⟨6961133508245206266768833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18563022688653883378050221 6961133508245206266768833)
    ·
      refine ⟨5220850131183904700076625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6961133508245206266768833 5220850131183904700076625)
      ·
        refine ⟨3915637598387928525057469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5220850131183904700076625 3915637598387928525057469)
        ·
          refine ⟨1468364099395473196896551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3915637598387928525057469 1468364099395473196896551)
          ·
            refine ⟨2202546149093209795344827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468364099395473196896551 2202546149093209795344827)
            ·
              refine ⟨3303819223639814693017241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202546149093209795344827 3303819223639814693017241)
              ·
                refine ⟨2477864417729861019762931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3303819223639814693017241 2477864417729861019762931)
                ·
                  refine ⟨3716796626594791529644397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2477864417729861019762931 3716796626594791529644397)
                  ·
                    refine ⟨1393798734973046823616649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3716796626594791529644397 1393798734973046823616649)
                    ·
                      refine ⟨1045349051229785117712487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393798734973046823616649 1045349051229785117712487)
                      ·
                        rfl

theorem cell23_2035810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2035810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035810 prefixEnd_2035810 := by exact prefixLift 2035810
  have htrace : WordTrace (prefixWord ++ tailWord_2035810) baseStart_2035810 baseEnd_2035810 := by
    simpa [prefixWord, tailWord_2035810, baseEnd_2035810] using wordTrace_append hprefix tailTrace_2035810
  have hstable : (prefixWord ++ tailWord_2035810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035810).length < 2 ^ (prefixWord ++ tailWord_2035810).sum := by decide
  have hdescent : baseEnd_2035810 < baseStart_2035810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035872 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 5, 4]
def baseStart_2035872 : Nat := 118140960795 + 2035872 * 2 ^ 59
def prefixEnd_2035872 : Nat := 4983230072969 + 3 ^ 40 * 2035872 * 2
def baseEnd_2035872 : Nat := 348460295676787958379067

theorem tailTrace_2035872 : CollatzResearch.WordTrace tailWord_2035872 prefixEnd_2035872 348460295676787958379067 := by
  unfold tailWord_2035872
  simp only [CollatzResearch.WordTrace]
  refine ⟨37127176040195459050478935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49502901386927278733971913 37127176040195459050478935)
  ·
    refine ⟨55690764060293188575718403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37127176040195459050478935 55690764060293188575718403)
    ·
      refine ⟨83536146090439782863577605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55690764060293188575718403 83536146090439782863577605)
      ·
        refine ⟨15663027391957459286920801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83536146090439782863577605 15663027391957459286920801)
        ·
          refine ⟨11747270543968094465190601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15663027391957459286920801 11747270543968094465190601)
          ·
            refine ⟨8810452907976070848892951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11747270543968094465190601 8810452907976070848892951)
            ·
              refine ⟨13215679361964106273339427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8810452907976070848892951 13215679361964106273339427)
              ·
                refine ⟨19823519042946159410009141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13215679361964106273339427 19823519042946159410009141)
                ·
                  refine ⟨1858454910276202444688357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19823519042946159410009141 1858454910276202444688357)
                  ·
                    refine ⟨348460295676787958379067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858454910276202444688357 348460295676787958379067)
                    ·
                      rfl

theorem cell23_2035872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 5, 4].length) (baseStart_2035872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035872 prefixEnd_2035872 := by exact prefixLift 2035872
  have htrace : WordTrace (prefixWord ++ tailWord_2035872) baseStart_2035872 baseEnd_2035872 := by
    simpa [prefixWord, tailWord_2035872, baseEnd_2035872] using wordTrace_append hprefix tailTrace_2035872
  have hstable : (prefixWord ++ tailWord_2035872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035872).length < 2 ^ (prefixWord ++ tailWord_2035872).sum := by decide
  have hdescent : baseEnd_2035872 < baseStart_2035872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035876 : List Nat := [2, 3, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_2035876 : Nat := 118140960795 + 2035876 * 2 ^ 59
def prefixEnd_2035876 : Nat := 4983230072969 + 3 ^ 40 * 2035876 * 2
def baseEnd_2035876 : Nat := 348460980317660619829061

theorem tailTrace_2035876 : CollatzResearch.WordTrace tailWord_2035876 prefixEnd_2035876 348460980317660619829061 := by
  unfold tailWord_2035876
  simp only [CollatzResearch.WordTrace]
  refine ⟨37127248986188213392051741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49502998648250951189402321 37127248986188213392051741)
  ·
    refine ⟨13922718369820580022019403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37127248986188213392051741 13922718369820580022019403)
    ·
      refine ⟨20884077554730870033029105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13922718369820580022019403 20884077554730870033029105)
      ·
        refine ⟨15663058166048152524771829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20884077554730870033029105 15663058166048152524771829)
        ·
          refine ⟨1468411703067014299197359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15663058166048152524771829 1468411703067014299197359)
          ·
            refine ⟨2202617554600521448796039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1468411703067014299197359 2202617554600521448796039)
            ·
              refine ⟨3303926331900782173194059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202617554600521448796039 3303926331900782173194059)
              ·
                refine ⟨4955889497851173259791089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3303926331900782173194059 4955889497851173259791089)
                ·
                  refine ⟨3716917123388379944843317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4955889497851173259791089 3716917123388379944843317)
                  ·
                    refine ⟨348460980317660619829061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3716917123388379944843317 348460980317660619829061)
                    ·
                      rfl

theorem cell23_2035876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_2035876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035876 prefixEnd_2035876 := by exact prefixLift 2035876
  have htrace : WordTrace (prefixWord ++ tailWord_2035876) baseStart_2035876 baseEnd_2035876 := by
    simpa [prefixWord, tailWord_2035876, baseEnd_2035876] using wordTrace_append hprefix tailTrace_2035876
  have hstable : (prefixWord ++ tailWord_2035876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035876).length < 2 ^ (prefixWord ++ tailWord_2035876).sum := by decide
  have hdescent : baseEnd_2035876 < baseStart_2035876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035879 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2035879 : Nat := 118140960795 + 2035879 * 2 ^ 59
def prefixEnd_2035879 : Nat := 4983230072969 + 3 ^ 40 * 2035879 * 2
def baseEnd_2035879 : Nat := 1045384481394945347749669

theorem tailTrace_2035879 : CollatzResearch.WordTrace tailWord_2035879 prefixEnd_2035879 1045384481394945347749669 := by
  unfold tailWord_2035879
  simp only [CollatzResearch.WordTrace]
  refine ⟨74254607391365558296462691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49503071594243705530975127 74254607391365558296462691)
  ·
    refine ⟨111381911087048337444694037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74254607391365558296462691 111381911087048337444694037)
    ·
      refine ⟨5221027082205390817720033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111381911087048337444694037 5221027082205390817720033)
      ·
        refine ⟨3915770311654043113290025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5221027082205390817720033 3915770311654043113290025)
        ·
          refine ⟨2936827733740532334967519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3915770311654043113290025 2936827733740532334967519)
          ·
            refine ⟨4405241600610798502451279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2936827733740532334967519 4405241600610798502451279)
            ·
              refine ⟨6607862400916197753676919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405241600610798502451279 6607862400916197753676919)
              ·
                refine ⟨9911793601374296630515379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6607862400916197753676919 9911793601374296630515379)
                ·
                  refine ⟨14867690402061444945773069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9911793601374296630515379 14867690402061444945773069)
                  ·
                    refine ⟨5575383900773041854664901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14867690402061444945773069 5575383900773041854664901)
                    ·
                      refine ⟨1045384481394945347749669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5575383900773041854664901 1045384481394945347749669)
                      ·
                        rfl

theorem cell23_2035879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2035879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035879 prefixEnd_2035879 := by exact prefixLift 2035879
  have htrace : WordTrace (prefixWord ++ tailWord_2035879) baseStart_2035879 baseEnd_2035879 := by
    simpa [prefixWord, tailWord_2035879, baseEnd_2035879] using wordTrace_append hprefix tailTrace_2035879
  have hstable : (prefixWord ++ tailWord_2035879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035879).length < 2 ^ (prefixWord ++ tailWord_2035879).sum := by decide
  have hdescent : baseEnd_2035879 < baseStart_2035879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035929 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 3]
def baseStart_2035929 : Nat := 118140960795 + 2035929 * 2 ^ 59
def prefixEnd_2035929 : Nat := 4983230072969 + 3 ^ 40 * 2035929 * 2
def baseEnd_2035929 : Nat := 1045410155427670152124439

theorem tailTrace_2035929 : CollatzResearch.WordTrace tailWord_2035929 prefixEnd_2035929 1045410155427670152124439 := by
  unfold tailWord_2035929
  simp only [CollatzResearch.WordTrace]
  refine ⟨74256431041184416835782841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49504287360789611223855227 74256431041184416835782841)
  ·
    refine ⟨55692323280888312626837131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74256431041184416835782841 55692323280888312626837131)
    ·
      refine ⟨83538484921332468940255697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55692323280888312626837131 83538484921332468940255697)
      ·
        refine ⟨62653863690999351705191773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83538484921332468940255697 62653863690999351705191773)
        ·
          refine ⟨23495198884124756889446915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62653863690999351705191773 23495198884124756889446915)
          ·
            refine ⟨35242798326187135334170373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23495198884124756889446915 35242798326187135334170373)
            ·
              refine ⟨6608024686160087875156945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35242798326187135334170373 6608024686160087875156945)
              ·
                refine ⟨4956018514620065906367709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6608024686160087875156945 4956018514620065906367709)
                ·
                  refine ⟨1858506942982524714887891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4956018514620065906367709 1858506942982524714887891)
                  ·
                    refine ⟨2787760414473787072331837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1858506942982524714887891 2787760414473787072331837)
                    ·
                      refine ⟨1045410155427670152124439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787760414473787072331837 1045410155427670152124439)
                      ·
                        rfl

theorem cell23_2035929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_2035929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035929 prefixEnd_2035929 := by exact prefixLift 2035929
  have htrace : WordTrace (prefixWord ++ tailWord_2035929) baseStart_2035929 baseEnd_2035929 := by
    simpa [prefixWord, tailWord_2035929, baseEnd_2035929] using wordTrace_append hprefix tailTrace_2035929
  have hstable : (prefixWord ++ tailWord_2035929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035929).length < 2 ^ (prefixWord ++ tailWord_2035929).sum := by decide
  have hdescent : baseEnd_2035929 < baseStart_2035929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035979 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 2, 4]
def baseStart_2035979 : Nat := 118140960795 + 2035979 * 2 ^ 59
def prefixEnd_2035979 : Nat := 4983230072969 + 3 ^ 40 * 2035979 * 2
def baseEnd_2035979 : Nat := 348478609820131652166403

theorem tailTrace_2035979 : CollatzResearch.WordTrace tailWord_2035979 prefixEnd_2035979 348478609820131652166403 := by
  unfold tailWord_2035979
  simp only [CollatzResearch.WordTrace]
  refine ⟨74258254691003275375102991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49505503127335516916735327 74258254691003275375102991)
  ·
    refine ⟨111387382036504913062654487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74258254691003275375102991 111387382036504913062654487)
    ·
      refine ⟨167081073054757369593981731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111387382036504913062654487 167081073054757369593981731)
      ·
        refine ⟨250621609582136054390972597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167081073054757369593981731 250621609582136054390972597)
        ·
          refine ⟨23495775898325255099153681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 250621609582136054390972597 23495775898325255099153681)
          ·
            refine ⟨17621831923743941324365261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23495775898325255099153681 17621831923743941324365261)
            ·
              refine ⟨6608186971403977996636973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17621831923743941324365261 6608186971403977996636973)
              ·
                refine ⟨2478070114276491748738865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6608186971403977996636973 2478070114276491748738865)
                ·
                  refine ⟨1858552585707368811554149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2478070114276491748738865 1858552585707368811554149)
                  ·
                    refine ⟨348478609820131652166403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858552585707368811554149 348478609820131652166403)
                    ·
                      rfl

theorem cell23_2035979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 4].length) (baseStart_2035979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035979 prefixEnd_2035979 := by exact prefixLift 2035979
  have htrace : WordTrace (prefixWord ++ tailWord_2035979) baseStart_2035979 baseEnd_2035979 := by
    simpa [prefixWord, tailWord_2035979, baseEnd_2035979] using wordTrace_append hprefix tailTrace_2035979
  have hstable : (prefixWord ++ tailWord_2035979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035979).length < 2 ^ (prefixWord ++ tailWord_2035979).sum := by decide
  have hdescent : baseEnd_2035979 < baseStart_2035979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035982 : List Nat := [4, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_2035982 : Nat := 118140960795 + 2035982 * 2 ^ 59
def prefixEnd_2035982 : Nat := 4983230072969 + 3 ^ 40 * 2035982 * 2
def baseEnd_2035982 : Nat := 1045437369902358444761695

theorem tailTrace_2035982 : CollatzResearch.WordTrace tailWord_2035982 prefixEnd_2035982 1045437369902358444761695 := by
  unfold tailWord_2035982
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282295513749050860932775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49505576073328271258308133 9282295513749050860932775)
  ·
    refine ⟨13923443270623576291399163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282295513749050860932775 13923443270623576291399163)
    ·
      refine ⟨20885164905935364437098745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13923443270623576291399163 20885164905935364437098745)
      ·
        refine ⟨15663873679451523327824059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20885164905935364437098745 15663873679451523327824059)
        ·
          refine ⟨23495810519177284991736089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15663873679451523327824059 23495810519177284991736089)
          ·
            refine ⟨17621857889382963743802067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23495810519177284991736089 17621857889382963743802067)
            ·
              refine ⟨26432786834074445615703101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17621857889382963743802067 26432786834074445615703101)
              ·
                refine ⟨9912295062777917105888663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26432786834074445615703101 9912295062777917105888663)
                ·
                  refine ⟨14868442594166875658832995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9912295062777917105888663 14868442594166875658832995)
                  ·
                    refine ⟨22302663891250313488249493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14868442594166875658832995 22302663891250313488249493)
                    ·
                      refine ⟨1045437369902358444761695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22302663891250313488249493 1045437369902358444761695)
                      ·
                        rfl

theorem cell23_2035982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_2035982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035982 prefixEnd_2035982 := by exact prefixLift 2035982
  have htrace : WordTrace (prefixWord ++ tailWord_2035982) baseStart_2035982 baseEnd_2035982 := by
    simpa [prefixWord, tailWord_2035982, baseEnd_2035982] using wordTrace_append hprefix tailTrace_2035982
  have hstable : (prefixWord ++ tailWord_2035982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035982).length < 2 ^ (prefixWord ++ tailWord_2035982).sum := by decide
  have hdescent : baseEnd_2035982 < baseStart_2035982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2035999 : List Nat := [1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 4]
def baseStart_2035999 : Nat := 118140960795 + 2035999 * 2 ^ 59
def prefixEnd_2035999 : Nat := 4983230072969 + 3 ^ 40 * 2035999 * 2
def baseEnd_2035999 : Nat := 1045446099073484878249117

theorem tailTrace_2035999 : CollatzResearch.WordTrace tailWord_2035999 prefixEnd_2035999 1045446099073484878249117 := by
  unfold tailWord_2035999
  simp only [CollatzResearch.WordTrace]
  refine ⟨74258984150930818790831051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49505989433953879193887367 74258984150930818790831051)
  ·
    refine ⟨111388476226396228186246577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74258984150930818790831051 111388476226396228186246577)
    ·
      refine ⟨83541357169797171139684933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111388476226396228186246577 83541357169797171139684933)
      ·
        refine ⟨15664004469336969588690925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83541357169797171139684933 15664004469336969588690925)
        ·
          refine ⟨5874001676001363595759097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15664004469336969588690925 5874001676001363595759097)
          ·
            refine ⟨4405501257001022696819323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5874001676001363595759097 4405501257001022696819323)
            ·
              refine ⟨6608251885501534045228985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4405501257001022696819323 6608251885501534045228985)
              ·
                refine ⟨4956188914126150533921739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6608251885501534045228985 4956188914126150533921739)
                ·
                  refine ⟨7434283371189225800882609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956188914126150533921739 7434283371189225800882609)
                  ·
                    refine ⟨5575712528391919350661957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7434283371189225800882609 5575712528391919350661957)
                    ·
                      refine ⟨1045446099073484878249117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5575712528391919350661957 1045446099073484878249117)
                      ·
                        rfl

theorem cell23_2035999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_2035999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2035999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2035999 prefixEnd_2035999 := by exact prefixLift 2035999
  have htrace : WordTrace (prefixWord ++ tailWord_2035999) baseStart_2035999 baseEnd_2035999 := by
    simpa [prefixWord, tailWord_2035999, baseEnd_2035999] using wordTrace_append hprefix tailTrace_2035999
  have hstable : (prefixWord ++ tailWord_2035999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2035999).length < 2 ^ (prefixWord ++ tailWord_2035999).sum := by decide
  have hdescent : baseEnd_2035999 < baseStart_2035999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2035999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036003 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 1, 2, 2]
def baseStart_2036003 : Nat := 118140960795 + 2036003 * 2 ^ 59
def prefixEnd_2036003 : Nat := 4983230072969 + 3 ^ 40 * 2036003 * 2
def baseEnd_2036003 : Nat := 1045448152996102862599099

theorem tailTrace_2036003 : CollatzResearch.WordTrace tailWord_2036003 prefixEnd_2036003 1045448152996102862599099 := by
  unfold tailWord_2036003
  simp only [CollatzResearch.WordTrace]
  refine ⟨74259130042916327473976663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49506086695277551649317775 74259130042916327473976663)
  ·
    refine ⟨111388695064374491210964995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74259130042916327473976663 111388695064374491210964995)
    ·
      refine ⟨167083042596561736816447493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111388695064374491210964995 167083042596561736816447493)
      ·
        refine ⟨31328070486855325653083905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167083042596561736816447493 31328070486855325653083905)
        ·
          refine ⟨23496052865141494239812929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31328070486855325653083905 23496052865141494239812929)
          ·
            refine ⟨17622039648856120679859697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23496052865141494239812929 17622039648856120679859697)
            ·
              refine ⟨13216529736642090509894773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17622039648856120679859697 13216529736642090509894773)
              ·
                refine ⟨1239049662810195985302635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13216529736642090509894773 1239049662810195985302635)
                ·
                  refine ⟨1858574494215293977953953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239049662810195985302635 1858574494215293977953953)
                  ·
                    refine ⟨1393930870661470483465465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1858574494215293977953953 1393930870661470483465465)
                    ·
                      refine ⟨1045448152996102862599099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393930870661470483465465 1045448152996102862599099)
                      ·
                        rfl

theorem cell23_2036003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_2036003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036003 prefixEnd_2036003 := by exact prefixLift 2036003
  have htrace : WordTrace (prefixWord ++ tailWord_2036003) baseStart_2036003 baseEnd_2036003 := by
    simpa [prefixWord, tailWord_2036003, baseEnd_2036003] using wordTrace_append hprefix tailTrace_2036003
  have hstable : (prefixWord ++ tailWord_2036003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036003).length < 2 ^ (prefixWord ++ tailWord_2036003).sum := by decide
  have hdescent : baseEnd_2036003 < baseStart_2036003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036014 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2036014 : Nat := 118140960795 + 2036014 * 2 ^ 59
def prefixEnd_2036014 : Nat := 4983230072969 + 3 ^ 40 * 2036014 * 2
def baseEnd_2036014 : Nat := 1045453801283302319561549

theorem tailTrace_2036014 : CollatzResearch.WordTrace tailWord_2036014 prefixEnd_2036014 1045453801283302319561549 := by
  unfold tailWord_2036014
  simp only [CollatzResearch.WordTrace]
  refine ⟨9282441405734559544078387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49506354163917650901751397 9282441405734559544078387)
  ·
    refine ⟨13923662108601839316117581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9282441405734559544078387 13923662108601839316117581)
    ·
      refine ⟨5221373290725689743544093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13923662108601839316117581 5221373290725689743544093)
      ·
        refine ⟨1958014984022133653829035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5221373290725689743544093 1958014984022133653829035)
        ·
          refine ⟨2937022476033200480743553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958014984022133653829035 2937022476033200480743553)
          ·
            refine ⟨2202766857024900360557665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937022476033200480743553 2202766857024900360557665)
            ·
              refine ⟨1652075142768675270418249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2202766857024900360557665 1652075142768675270418249)
              ·
                refine ⟨1239056357076506452813687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652075142768675270418249 1239056357076506452813687)
                ·
                  refine ⟨1858584535614759679220531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239056357076506452813687 1858584535614759679220531)
                  ·
                    refine ⟨2787876803422139518830797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1858584535614759679220531 2787876803422139518830797)
                    ·
                      refine ⟨1045453801283302319561549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2787876803422139518830797 1045453801283302319561549)
                      ·
                        rfl

theorem cell23_2036014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2036014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036014 prefixEnd_2036014 := by exact prefixLift 2036014
  have htrace : WordTrace (prefixWord ++ tailWord_2036014) baseStart_2036014 baseEnd_2036014 := by
    simpa [prefixWord, tailWord_2036014, baseEnd_2036014] using wordTrace_append hprefix tailTrace_2036014
  have hstable : (prefixWord ++ tailWord_2036014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036014).length < 2 ^ (prefixWord ++ tailWord_2036014).sum := by decide
  have hdescent : baseEnd_2036014 < baseStart_2036014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036063 : List Nat := [1, 1, 2, 3, 1, 2, 6, 1, 1, 3, 2]
def baseStart_2036063 : Nat := 118140960795 + 2036063 * 2 ^ 59
def prefixEnd_2036063 : Nat := 4983230072969 + 3 ^ 40 * 2036063 * 2
def baseEnd_2036063 : Nat := 1045478961835372627848823

theorem tailTrace_2036063 : CollatzResearch.WordTrace tailWord_2036063 prefixEnd_2036063 1045478961835372627848823 := by
  unfold tailWord_2036063
  simp only [CollatzResearch.WordTrace]
  refine ⟨74261318422698957721160843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49507545615132638480773895 74261318422698957721160843)
  ·
    refine ⟨111391977634048436581741265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74261318422698957721160843 111391977634048436581741265)
    ·
      refine ⟨83543983225536327436305949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111391977634048436581741265 83543983225536327436305949)
      ·
        refine ⟨31328993709576122788614731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83543983225536327436305949 31328993709576122788614731)
        ·
          refine ⟨46993490564364184182922097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31328993709576122788614731 46993490564364184182922097)
          ·
            refine ⟨35245117923273138137191573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46993490564364184182922097 35245117923273138137191573)
            ·
              refine ⟨1652114902653428350180855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35245117923273138137191573 1652114902653428350180855)
              ·
                refine ⟨2478172353980142525271283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652114902653428350180855 2478172353980142525271283)
                ·
                  refine ⟨3717258530970213787906925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478172353980142525271283 3717258530970213787906925)
                  ·
                    refine ⟨1393971949113830170465097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717258530970213787906925 1393971949113830170465097)
                    ·
                      refine ⟨1045478961835372627848823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393971949113830170465097 1045478961835372627848823)
                      ·
                        rfl

theorem cell23_2036063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_2036063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036063 prefixEnd_2036063 := by exact prefixLift 2036063
  have htrace : WordTrace (prefixWord ++ tailWord_2036063) baseStart_2036063 baseEnd_2036063 := by
    simpa [prefixWord, tailWord_2036063, baseEnd_2036063] using wordTrace_append hprefix tailTrace_2036063
  have hstable : (prefixWord ++ tailWord_2036063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036063).length < 2 ^ (prefixWord ++ tailWord_2036063).sum := by decide
  have hdescent : baseEnd_2036063 < baseStart_2036063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036093 : List Nat := [1, 4, 1, 1, 2, 5, 1, 1, 1, 4, 2]
def baseStart_2036093 : Nat := 118140960795 + 2036093 * 2 ^ 59
def prefixEnd_2036093 : Nat := 4983230072969 + 3 ^ 40 * 2036093 * 2
def baseEnd_2036093 : Nat := 1045494366255007510473685

theorem tailTrace_2036093 : CollatzResearch.WordTrace tailWord_2036093 prefixEnd_2036093 1045494366255007510473685 := by
  unfold tailWord_2036093
  simp only [CollatzResearch.WordTrace]
  refine ⟨74262412612590272844752933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49508275075060181896501955 74262412612590272844752933)
  ·
    refine ⟨13924202364860676158391175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74262412612590272844752933 13924202364860676158391175)
    ·
      refine ⟨20886303547291014237586763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13924202364860676158391175 20886303547291014237586763)
      ·
        refine ⟨31329455320936521356380145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20886303547291014237586763 31329455320936521356380145)
        ·
          refine ⟨23497091490702391017285109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31329455320936521356380145 23497091490702391017285109)
          ·
            refine ⟨2202852327253349157870479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23497091490702391017285109 2202852327253349157870479)
            ·
              refine ⟨3304278490880023736805719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2202852327253349157870479 3304278490880023736805719)
              ·
                refine ⟨4956417736320035605208579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3304278490880023736805719 4956417736320035605208579)
                ·
                  refine ⟨7434626604480053407812869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4956417736320035605208579 7434626604480053407812869)
                  ·
                    refine ⟨1393992488340010013964913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7434626604480053407812869 1393992488340010013964913)
                    ·
                      refine ⟨1045494366255007510473685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1393992488340010013964913 1045494366255007510473685)
                      ·
                        rfl

theorem cell23_2036093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_2036093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036093 prefixEnd_2036093 := by exact prefixLift 2036093
  have htrace : WordTrace (prefixWord ++ tailWord_2036093) baseStart_2036093 baseEnd_2036093 := by
    simpa [prefixWord, tailWord_2036093, baseEnd_2036093] using wordTrace_append hprefix tailTrace_2036093
  have hstable : (prefixWord ++ tailWord_2036093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036093).length < 2 ^ (prefixWord ++ tailWord_2036093).sum := by decide
  have hdescent : baseEnd_2036093 < baseStart_2036093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036169 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 3]
def baseStart_2036169 : Nat := 118140960795 + 2036169 * 2 ^ 59
def prefixEnd_2036169 : Nat := 4983230072969 + 3 ^ 40 * 2036169 * 2
def baseEnd_2036169 : Nat := 1045533390784749213123335

theorem tailTrace_2036169 : CollatzResearch.WordTrace tailWord_2036169 prefixEnd_2036169 1045533390784749213123335 := by
  unfold tailWord_2036169
  simp only [CollatzResearch.WordTrace]
  refine ⟨74265184560314937824519561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49510123040209958549679707 74265184560314937824519561)
  ·
    refine ⟨55698888420236203368389671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74265184560314937824519561 55698888420236203368389671)
    ·
      refine ⟨83548332630354305052584507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55698888420236203368389671 83548332630354305052584507)
      ·
        refine ⟨125322498945531457578876761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83548332630354305052584507 125322498945531457578876761)
        ·
          refine ⟨93991874209148593184157571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125322498945531457578876761 93991874209148593184157571)
          ·
            refine ⟨140987811313722889776236357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93991874209148593184157571 140987811313722889776236357)
            ·
              refine ⟨26435214621323041833044317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140987811313722889776236357 26435214621323041833044317)
              ·
                refine ⟨9913205482996140687391619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26435214621323041833044317 9913205482996140687391619)
                ·
                  refine ⟨14869808224494211031087429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9913205482996140687391619 14869808224494211031087429)
                  ·
                    refine ⟨2788089042092664568328893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14869808224494211031087429 2788089042092664568328893)
                    ·
                      refine ⟨1045533390784749213123335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2788089042092664568328893 1045533390784749213123335)
                      ·
                        rfl

theorem cell23_2036169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_2036169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036169 prefixEnd_2036169 := by exact prefixLift 2036169
  have htrace : WordTrace (prefixWord ++ tailWord_2036169) baseStart_2036169 baseEnd_2036169 := by
    simpa [prefixWord, tailWord_2036169, baseEnd_2036169] using wordTrace_append hprefix tailTrace_2036169
  have hstable : (prefixWord ++ tailWord_2036169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036169).length < 2 ^ (prefixWord ++ tailWord_2036169).sum := by decide
  have hdescent : baseEnd_2036169 < baseStart_2036169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036186 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_2036186 : Nat := 118140960795 + 2036186 * 2 ^ 59
def prefixEnd_2036186 : Nat := 4983230072969 + 3 ^ 40 * 2036186 * 2
def baseEnd_2036186 : Nat := 1045542119955875646610757

theorem tailTrace_2036186 : CollatzResearch.WordTrace tailWord_2036186 prefixEnd_2036186 1045542119955875646610757 := by
  unfold tailWord_2036186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18566451150313337431972103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49510536400835566485258941 18566451150313337431972103)
  ·
    refine ⟨27849676725470006147958155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18566451150313337431972103 27849676725470006147958155)
    ·
      refine ⟨41774515088205009221937233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27849676725470006147958155 41774515088205009221937233)
      ·
        refine ⟨31330886316153756916452925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41774515088205009221937233 31330886316153756916452925)
        ·
          refine ⟨11749082368557658843669847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31330886316153756916452925 11749082368557658843669847)
          ·
            refine ⟨17623623552836488265504771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11749082368557658843669847 17623623552836488265504771)
            ·
              refine ⟨26435435329254732398257157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17623623552836488265504771 26435435329254732398257157)
              ·
                refine ⟨4956644124235262324673217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26435435329254732398257157 4956644124235262324673217)
                ·
                  refine ⟨3717483093176446743504913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4956644124235262324673217 3717483093176446743504913)
                  ·
                    refine ⟨2788112319882335057628685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3717483093176446743504913 2788112319882335057628685)
                    ·
                      refine ⟨1045542119955875646610757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2788112319882335057628685 1045542119955875646610757)
                      ·
                        rfl

theorem cell23_2036186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_2036186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036186 prefixEnd_2036186 := by exact prefixLift 2036186
  have htrace : WordTrace (prefixWord ++ tailWord_2036186) baseStart_2036186 baseEnd_2036186 := by
    simpa [prefixWord, tailWord_2036186, baseEnd_2036186] using wordTrace_append hprefix tailTrace_2036186
  have hstable : (prefixWord ++ tailWord_2036186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036186).length < 2 ^ (prefixWord ++ tailWord_2036186).sum := by decide
  have hdescent : baseEnd_2036186 < baseStart_2036186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036193 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 1, 4]
def baseStart_2036193 : Nat := 118140960795 + 2036193 * 2 ^ 59
def prefixEnd_2036193 : Nat := 4983230072969 + 3 ^ 40 * 2036193 * 2
def baseEnd_2036193 : Nat := 348515238106819039741075

theorem tailTrace_2036193 : CollatzResearch.WordTrace tailWord_2036193 prefixEnd_2036193 348515238106819039741075 := by
  unfold tailWord_2036193
  simp only [CollatzResearch.WordTrace]
  refine ⟨74266059912227989923393233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49510706608151993282262155 74266059912227989923393233)
  ·
    refine ⟨55699544934170992442544925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74266059912227989923393233 55699544934170992442544925)
    ·
      refine ⟨20887329350314122165954347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55699544934170992442544925 20887329350314122165954347)
      ·
        refine ⟨31330994025471183248931521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20887329350314122165954347 31330994025471183248931521)
        ·
          refine ⟨23498245519103387436698641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31330994025471183248931521 23498245519103387436698641)
          ·
            refine ⟨17623684139327540577523981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23498245519103387436698641 17623684139327540577523981)
            ·
              refine ⟨6608881552247827716571493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17623684139327540577523981 6608881552247827716571493)
              ·
                refine ⟨1239165291046467696857155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6608881552247827716571493 1239165291046467696857155)
                ·
                  refine ⟨1858747936569701545285733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239165291046467696857155 1858747936569701545285733)
                  ·
                    refine ⟨348515238106819039741075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1858747936569701545285733 348515238106819039741075)
                    ·
                      rfl

theorem cell23_2036193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_2036193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036193 prefixEnd_2036193 := by exact prefixLift 2036193
  have htrace : WordTrace (prefixWord ++ tailWord_2036193) baseStart_2036193 baseEnd_2036193 := by
    simpa [prefixWord, tailWord_2036193, baseEnd_2036193] using wordTrace_append hprefix tailTrace_2036193
  have hstable : (prefixWord ++ tailWord_2036193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036193).length < 2 ^ (prefixWord ++ tailWord_2036193).sum := by decide
  have hdescent : baseEnd_2036193 < baseStart_2036193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036206 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_2036206 : Nat := 118140960795 + 2036206 * 2 ^ 59
def prefixEnd_2036206 : Nat := 4983230072969 + 3 ^ 40 * 2036206 * 2
def baseEnd_2036206 : Nat := 116172487729885063151185

theorem tailTrace_2036206 : CollatzResearch.WordTrace tailWord_2036206 prefixEnd_2036206 116172487729885063151185 := by
  unfold tailWord_2036206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283316757647611642952059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49511022707453928762410981 9283316757647611642952059)
  ·
    refine ⟨13924975136471417464428089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9283316757647611642952059 13924975136471417464428089)
    ·
      refine ⟨10443731352353563098321067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13924975136471417464428089 10443731352353563098321067)
      ·
        refine ⟨15665597028530344647481601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10443731352353563098321067 15665597028530344647481601)
        ·
          refine ⟨11749197771397758485611201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15665597028530344647481601 11749197771397758485611201)
          ·
            refine ⟨8811898328548318864208401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11749197771397758485611201 8811898328548318864208401)
            ·
              refine ⟨6608923746411239148156301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8811898328548318864208401 6608923746411239148156301)
              ·
                refine ⟨2478346404904214680558613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6608923746411239148156301 2478346404904214680558613)
                ·
                  refine ⟨116172487729885063151185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2478346404904214680558613 116172487729885063151185)
                  ·
                    rfl

theorem cell23_2036206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_2036206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036206 prefixEnd_2036206 := by exact prefixLift 2036206
  have htrace : WordTrace (prefixWord ++ tailWord_2036206) baseStart_2036206 baseEnd_2036206 := by
    simpa [prefixWord, tailWord_2036206, baseEnd_2036206] using wordTrace_append hprefix tailTrace_2036206
  have hstable : (prefixWord ++ tailWord_2036206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036206).length < 2 ^ (prefixWord ++ tailWord_2036206).sum := by decide
  have hdescent : baseEnd_2036206 < baseStart_2036206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036230 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_2036230 : Nat := 118140960795 + 2036230 * 2 ^ 59
def prefixEnd_2036230 : Nat := 4983230072969 + 3 ^ 40 * 2036230 * 2
def baseEnd_2036230 : Nat := 1045564713104673474460555

theorem tailTrace_2036230 : CollatzResearch.WordTrace tailWord_2036230 prefixEnd_2036230 1045564713104673474460555 := by
  unfold tailWord_2036230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2320856544159185788827817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49511606275395963494993429 2320856544159185788827817)
  ·
    refine ⟨1740642408119389341620863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2320856544159185788827817 1740642408119389341620863)
    ·
      refine ⟨2610963612179084012431295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740642408119389341620863 2610963612179084012431295)
      ·
        refine ⟨3916445418268626018646943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2610963612179084012431295 3916445418268626018646943)
        ·
          refine ⟨5874668127402939027970415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3916445418268626018646943 5874668127402939027970415)
          ·
            refine ⟨8812002191104408541955623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5874668127402939027970415 8812002191104408541955623)
            ·
              refine ⟨13218003286656612812933435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812002191104408541955623 13218003286656612812933435)
              ·
                refine ⟨19827004929984919219400153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13218003286656612812933435 19827004929984919219400153)
                ·
                  refine ⟨14870253697488689414550115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19827004929984919219400153 14870253697488689414550115)
                  ·
                    refine ⟨22305380546233034121825173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14870253697488689414550115 22305380546233034121825173)
                    ·
                      refine ⟨1045564713104673474460555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22305380546233034121825173 1045564713104673474460555)
                      ·
                        rfl

theorem cell23_2036230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_2036230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036230 prefixEnd_2036230 := by exact prefixLift 2036230
  have htrace : WordTrace (prefixWord ++ tailWord_2036230) baseStart_2036230 baseEnd_2036230 := by
    simpa [prefixWord, tailWord_2036230, baseEnd_2036230] using wordTrace_append hprefix tailTrace_2036230
  have hstable : (prefixWord ++ tailWord_2036230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036230).length < 2 ^ (prefixWord ++ tailWord_2036230).sum := by decide
  have hdescent : baseEnd_2036230 < baseStart_2036230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036250 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3]
def baseStart_2036250 : Nat := 118140960795 + 2036250 * 2 ^ 59
def prefixEnd_2036250 : Nat := 4983230072969 + 3 ^ 40 * 2036250 * 2
def baseEnd_2036250 : Nat := 1045574982717763396210463

theorem tailTrace_2036250 : CollatzResearch.WordTrace tailWord_2036250 prefixEnd_2036250 1045574982717763396210463 := by
  unfold tailWord_2036250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18567034718255372164554551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49512092582014325772145469 18567034718255372164554551)
  ·
    refine ⟨27850552077383058246831827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18567034718255372164554551 27850552077383058246831827)
    ·
      refine ⟨41775828116074587370247741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27850552077383058246831827 41775828116074587370247741)
      ·
        refine ⟨15665935543527970263842903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41775828116074587370247741 15665935543527970263842903)
        ·
          refine ⟨23498903315291955395764355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15665935543527970263842903 23498903315291955395764355)
          ·
            refine ⟨35248354972937933093646533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23498903315291955395764355 35248354972937933093646533)
            ·
              refine ⟨6609066557425862455058725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35248354972937933093646533 6609066557425862455058725)
              ·
                refine ⟨1239199979517349210323511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6609066557425862455058725 1239199979517349210323511)
                ·
                  refine ⟨1858799969276023815485267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239199979517349210323511 1858799969276023815485267)
                  ·
                    refine ⟨2788199953914035723227901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1858799969276023815485267 2788199953914035723227901)
                    ·
                      refine ⟨1045574982717763396210463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2788199953914035723227901 1045574982717763396210463)
                      ·
                        rfl

theorem cell23_2036250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_2036250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036250 prefixEnd_2036250 := by exact prefixLift 2036250
  have htrace : WordTrace (prefixWord ++ tailWord_2036250) baseStart_2036250 baseEnd_2036250 := by
    simpa [prefixWord, tailWord_2036250, baseEnd_2036250] using wordTrace_append hprefix tailTrace_2036250
  have hstable : (prefixWord ++ tailWord_2036250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036250).length < 2 ^ (prefixWord ++ tailWord_2036250).sum := by decide
  have hdescent : baseEnd_2036250 < baseStart_2036250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036270 : List Nat := [4, 1, 3, 1, 3, 1, 2, 2, 1, 5]
def baseStart_2036270 : Nat := 118140960795 + 2036270 * 2 ^ 59
def prefixEnd_2036270 : Nat := 4983230072969 + 3 ^ 40 * 2036270 * 2
def baseEnd_2036270 : Nat := 348528417443617772653457

theorem tailTrace_2036270 : CollatzResearch.WordTrace tailWord_2036270 prefixEnd_2036270 348528417443617772653457 := by
  unfold tailWord_2036270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9283608541618629009243283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49512578888632688049297509 9283608541618629009243283)
  ·
    refine ⟨13925412812427943513864925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9283608541618629009243283 13925412812427943513864925)
    ·
      refine ⟨5222029804660478817699347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13925412812427943513864925 5222029804660478817699347)
      ·
        refine ⟨7833044706990718226549021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222029804660478817699347 7833044706990718226549021)
        ·
          refine ⟨2937391765121519334955883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7833044706990718226549021 2937391765121519334955883)
          ·
            refine ⟨4406087647682279002433825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2937391765121519334955883 4406087647682279002433825)
            ·
              refine ⟨3304565735761709251825369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4406087647682279002433825 3304565735761709251825369)
              ·
                refine ⟨2478424301821281938869027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3304565735761709251825369 2478424301821281938869027)
                ·
                  refine ⟨3717636452731922908303541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478424301821281938869027 3717636452731922908303541)
                  ·
                    refine ⟨348528417443617772653457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3717636452731922908303541 348528417443617772653457)
                    ·
                      rfl

theorem cell23_2036270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_2036270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036270 prefixEnd_2036270 := by exact prefixLift 2036270
  have htrace : WordTrace (prefixWord ++ tailWord_2036270) baseStart_2036270 baseEnd_2036270 := by
    simpa [prefixWord, tailWord_2036270, baseEnd_2036270] using wordTrace_append hprefix tailTrace_2036270
  have hstable : (prefixWord ++ tailWord_2036270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036270).length < 2 ^ (prefixWord ++ tailWord_2036270).sum := by decide
  have hdescent : baseEnd_2036270 < baseStart_2036270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036279 : List Nat := [1, 1, 3, 1, 2, 3, 3, 9]
def baseStart_2036279 : Nat := 118140960795 + 2036279 * 2 ^ 59
def prefixEnd_2036279 : Nat := 4983230072969 + 3 ^ 40 * 2036279 * 2
def baseEnd_2036279 : Nat := 38725550876175695657327

theorem tailTrace_2036279 : CollatzResearch.WordTrace tailWord_2036279 prefixEnd_2036279 38725550876175695657327 := by
  unfold tailWord_2036279
  simp only [CollatzResearch.WordTrace]
  refine ⟨74269196589916426611023891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49512797726610951074015927 74269196589916426611023891)
  ·
    refine ⟨111403794884874639916535837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74269196589916426611023891 111403794884874639916535837)
    ·
      refine ⟨41776423081827989968700939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111403794884874639916535837 41776423081827989968700939)
      ·
        refine ⟨62664634622741984953051409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41776423081827989968700939 62664634622741984953051409)
        ·
          refine ⟨46998475967056488714788557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62664634622741984953051409 46998475967056488714788557)
          ·
            refine ⟨17624428487646183268045709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46998475967056488714788557 17624428487646183268045709)
            ·
              refine ⟨6609160682867318725517141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17624428487646183268045709 6609160682867318725517141)
              ·
                refine ⟨38725550876175695657327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6609160682867318725517141 38725550876175695657327)
                ·
                  rfl

theorem cell23_2036279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 9].length) (baseStart_2036279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036279 prefixEnd_2036279 := by exact prefixLift 2036279
  have htrace : WordTrace (prefixWord ++ tailWord_2036279) baseStart_2036279 baseEnd_2036279 := by
    simpa [prefixWord, tailWord_2036279, baseEnd_2036279] using wordTrace_append hprefix tailTrace_2036279
  have hstable : (prefixWord ++ tailWord_2036279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036279).length < 2 ^ (prefixWord ++ tailWord_2036279).sum := by decide
  have hdescent : baseEnd_2036279 < baseStart_2036279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036293 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_2036293 : Nat := 118140960795 + 2036293 * 2 ^ 59
def prefixEnd_2036293 : Nat := 4983230072969 + 3 ^ 40 * 2036293 * 2
def baseEnd_2036293 : Nat := 1045597062385906727972765

theorem tailTrace_2036293 : CollatzResearch.WordTrace tailWord_2036293 prefixEnd_2036293 1045597062385906727972765 := by
  unfold tailWord_2036293
  simp only [CollatzResearch.WordTrace]
  refine ⟨74269707211865707002033533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49513138141243804668022355 74269707211865707002033533)
  ·
    refine ⟨27851140204449640125762575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74269707211865707002033533 27851140204449640125762575)
    ·
      refine ⟨41776710306674460188643863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27851140204449640125762575 41776710306674460188643863)
      ·
        refine ⟨62665065460011690282965795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41776710306674460188643863 62665065460011690282965795)
        ·
          refine ⟨93997598190017535424448693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62665065460011690282965795 93997598190017535424448693)
          ·
            refine ⟨8812274830314143946042065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93997598190017535424448693 8812274830314143946042065)
            ·
              refine ⟨6609206122735607959531549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812274830314143946042065 6609206122735607959531549)
              ·
                refine ⟨2478452296025852984824331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6609206122735607959531549 2478452296025852984824331)
                ·
                  refine ⟨3717678444038779477236497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478452296025852984824331 3717678444038779477236497)
                  ·
                    refine ⟨2788258833029084607927373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3717678444038779477236497 2788258833029084607927373)
                    ·
                      refine ⟨1045597062385906727972765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2788258833029084607927373 1045597062385906727972765)
                      ·
                        rfl

theorem cell23_2036293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_2036293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036293 prefixEnd_2036293 := by exact prefixLift 2036293
  have htrace : WordTrace (prefixWord ++ tailWord_2036293) baseStart_2036293 baseEnd_2036293 := by
    simpa [prefixWord, tailWord_2036293, baseEnd_2036293] using wordTrace_append hprefix tailTrace_2036293
  have hstable : (prefixWord ++ tailWord_2036293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036293).length < 2 ^ (prefixWord ++ tailWord_2036293).sum := by decide
  have hdescent : baseEnd_2036293 < baseStart_2036293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036329 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 8]
def baseStart_2036329 : Nat := 118140960795 + 2036329 * 2 ^ 59
def prefixEnd_2036329 : Nat := 4983230072969 + 3 ^ 40 * 2036329 * 2
def baseEnd_2036329 : Nat := 1045615547689468587122599

theorem tailTrace_2036329 : CollatzResearch.WordTrace tailWord_2036329 prefixEnd_2036329 1045615547689468587122599 := by
  unfold tailWord_2036329
  simp only [CollatzResearch.WordTrace]
  refine ⟨74271020239735285150344041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49514013493156856766896027 74271020239735285150344041)
  ·
    refine ⟨55703265179801463862758031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74271020239735285150344041 55703265179801463862758031)
    ·
      refine ⟨83554897769702195794137047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55703265179801463862758031 83554897769702195794137047)
      ·
        refine ⟨125332346654553293691205571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83554897769702195794137047 125332346654553293691205571)
        ·
          refine ⟨187998519981829940536808357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125332346654553293691205571 187998519981829940536808357)
          ·
            refine ⟨35249722496593113850651567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 187998519981829940536808357 35249722496593113850651567)
            ·
              refine ⟨52874583744889670775977351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35249722496593113850651567 52874583744889670775977351)
              ·
                refine ⟨79311875617334506163966027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52874583744889670775977351 79311875617334506163966027)
                ·
                  refine ⟨118967813426001759245949041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79311875617334506163966027 118967813426001759245949041)
                  ·
                    refine ⟨89225860069501319434461781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 118967813426001759245949041 89225860069501319434461781)
                    ·
                      refine ⟨1045615547689468587122599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 89225860069501319434461781 1045615547689468587122599)
                      ·
                        rfl

theorem cell23_2036329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_2036329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036329 prefixEnd_2036329 := by exact prefixLift 2036329
  have htrace : WordTrace (prefixWord ++ tailWord_2036329) baseStart_2036329 baseEnd_2036329 := by
    simpa [prefixWord, tailWord_2036329, baseEnd_2036329] using wordTrace_append hprefix tailTrace_2036329
  have hstable : (prefixWord ++ tailWord_2036329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036329).length < 2 ^ (prefixWord ++ tailWord_2036329).sum := by decide
  have hdescent : baseEnd_2036329 < baseStart_2036329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036339 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 3, 8]
def baseStart_2036339 : Nat := 118140960795 + 2036339 * 2 ^ 59
def prefixEnd_2036339 : Nat := 4983230072969 + 3 ^ 40 * 2036339 * 2
def baseEnd_2036339 : Nat := 348540227498671182665851

theorem tailTrace_2036339 : CollatzResearch.WordTrace tailWord_2036339 prefixEnd_2036339 348540227498671182665851 := by
  unfold tailWord_2036339
  simp only [CollatzResearch.WordTrace]
  refine ⟨74271384969699056858208071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49514256646466037905472047 74271384969699056858208071)
  ·
    refine ⟨111407077454548585287312107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74271384969699056858208071 111407077454548585287312107)
    ·
      refine ⟨167110616181822877930968161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111407077454548585287312107 167110616181822877930968161)
      ·
        refine ⟨125332962136367158448226121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167110616181822877930968161 125332962136367158448226121)
        ·
          refine ⟨93999721602275368836169591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125332962136367158448226121 93999721602275368836169591)
          ·
            refine ⟨140999582403413053254254387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93999721602275368836169591 140999582403413053254254387)
            ·
              refine ⟨211499373605119579881381581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140999582403413053254254387 211499373605119579881381581)
              ·
                refine ⟨79312265101919842455518093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211499373605119579881381581 79312265101919842455518093)
                ·
                  refine ⟨29742099413219940920819285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79312265101919842455518093 29742099413219940920819285)
                  ·
                    refine ⟨348540227498671182665851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29742099413219940920819285 348540227498671182665851)
                    ·
                      rfl

theorem cell23_2036339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 8].length) (baseStart_2036339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036339 prefixEnd_2036339 := by exact prefixLift 2036339
  have htrace : WordTrace (prefixWord ++ tailWord_2036339) baseStart_2036339 baseEnd_2036339 := by
    simpa [prefixWord, tailWord_2036339, baseEnd_2036339] using wordTrace_append hprefix tailTrace_2036339
  have hstable : (prefixWord ++ tailWord_2036339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036339).length < 2 ^ (prefixWord ++ tailWord_2036339).sum := by decide
  have hdescent : baseEnd_2036339 < baseStart_2036339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036380 : List Nat := [2, 2, 3, 2, 2, 1, 1, 3, 1, 4, 2]
def baseStart_2036380 : Nat := 118140960795 + 2036380 * 2 ^ 59
def prefixEnd_2036380 : Nat := 4983230072969 + 3 ^ 40 * 2036380 * 2
def baseEnd_2036380 : Nat := 1045641735202847887584865

theorem tailTrace_2036380 : CollatzResearch.WordTrace tailWord_2036380 prefixEnd_2036380 1045641735202847887584865 := by
  unfold tailWord_2036380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37136440181275260430225297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49515253575033680573633729 37136440181275260430225297)
  ·
    refine ⟨27852330135956445322668973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37136440181275260430225297 27852330135956445322668973)
    ·
      refine ⟨10444623800983666996000865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27852330135956445322668973 10444623800983666996000865)
      ·
        refine ⟨7833467850737750247000649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10444623800983666996000865 7833467850737750247000649)
        ·
          refine ⟨5875100888053312685250487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7833467850737750247000649 5875100888053312685250487)
          ·
            refine ⟨8812651332079969027875731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5875100888053312685250487 8812651332079969027875731)
            ·
              refine ⟨13218976998119953541813597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812651332079969027875731 13218976998119953541813597)
              ·
                refine ⟨4957116374294982578180099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13218976998119953541813597 4957116374294982578180099)
                ·
                  refine ⟨7435674561442473867270149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957116374294982578180099 7435674561442473867270149)
                  ·
                    refine ⟨1394188980270463850113153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7435674561442473867270149 1394188980270463850113153)
                    ·
                      refine ⟨1045641735202847887584865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394188980270463850113153 1045641735202847887584865)
                      ·
                        rfl

theorem cell23_2036380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_2036380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036380 prefixEnd_2036380 := by exact prefixLift 2036380
  have htrace : WordTrace (prefixWord ++ tailWord_2036380) baseStart_2036380 baseEnd_2036380 := by
    simpa [prefixWord, tailWord_2036380, baseEnd_2036380] using wordTrace_append hprefix tailTrace_2036380
  have hstable : (prefixWord ++ tailWord_2036380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036380).length < 2 ^ (prefixWord ++ tailWord_2036380).sum := by decide
  have hdescent : baseEnd_2036380 < baseStart_2036380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036401 : List Nat := [1, 2, 2, 6, 1, 2, 2, 1, 1, 3, 2]
def baseStart_2036401 : Nat := 118140960795 + 2036401 * 2 ^ 59
def prefixEnd_2036401 : Nat := 4983230072969 + 3 ^ 40 * 2036401 * 2
def baseEnd_2036401 : Nat := 1045652518296592305422269

theorem tailTrace_2036401 : CollatzResearch.WordTrace tailWord_2036401 prefixEnd_2036401 1045652518296592305422269 := by
  unfold tailWord_2036401
  simp only [CollatzResearch.WordTrace]
  refine ⟨74273646295474441446965057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49515764196982960964643371 74273646295474441446965057)
  ·
    refine ⟨55705234721605831085223793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74273646295474441446965057 55705234721605831085223793)
    ·
      refine ⟨41778926041204373313917845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55705234721605831085223793 41778926041204373313917845)
      ·
        refine ⟨1958387158181454999089899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41778926041204373313917845 1958387158181454999089899)
        ·
          refine ⟨2937580737272182498634849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1958387158181454999089899 2937580737272182498634849)
          ·
            refine ⟨2203185552954136873976137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937580737272182498634849 2203185552954136873976137)
            ·
              refine ⟨1652389164715602655482103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2203185552954136873976137 1652389164715602655482103)
              ·
                refine ⟨2478583747073403983223155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1652389164715602655482103 2478583747073403983223155)
                ·
                  refine ⟨3717875620610105974834733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2478583747073403983223155 3717875620610105974834733)
                  ·
                    refine ⟨1394203357728789740563025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3717875620610105974834733 1394203357728789740563025)
                    ·
                      refine ⟨1045652518296592305422269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394203357728789740563025 1045652518296592305422269)
                      ·
                        rfl

theorem cell23_2036401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_2036401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036401 prefixEnd_2036401 := by exact prefixLift 2036401
  have htrace : WordTrace (prefixWord ++ tailWord_2036401) baseStart_2036401 baseEnd_2036401 := by
    simpa [prefixWord, tailWord_2036401, baseEnd_2036401] using wordTrace_append hprefix tailTrace_2036401
  have hstable : (prefixWord ++ tailWord_2036401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036401).length < 2 ^ (prefixWord ++ tailWord_2036401).sum := by decide
  have hdescent : baseEnd_2036401 < baseStart_2036401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036403 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 5]
def baseStart_2036403 : Nat := 118140960795 + 2036403 * 2 ^ 59
def prefixEnd_2036403 : Nat := 4983230072969 + 3 ^ 40 * 2036403 * 2
def baseEnd_2036403 : Nat := 116183727250877921955251

theorem tailTrace_2036403 : CollatzResearch.WordTrace tailWord_2036403 prefixEnd_2036403 116183727250877921955251 := by
  unfold tailWord_2036403
  simp only [CollatzResearch.WordTrace]
  refine ⟨74273719241467195788537863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49515812827644797192358575 74273719241467195788537863)
  ·
    refine ⟨111410578862200793682806795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74273719241467195788537863 111410578862200793682806795)
    ·
      refine ⟨167115868293301190524210193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111410578862200793682806795 167115868293301190524210193)
      ·
        refine ⟨125336901219975892893157645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167115868293301190524210193 125336901219975892893157645)
        ·
          refine ⟨47001337957490959834934117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125336901219975892893157645 47001337957490959834934117)
          ·
            refine ⟨8812750867029554969050147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47001337957490959834934117 8812750867029554969050147)
            ·
              refine ⟨13219126300544332453575221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812750867029554969050147 13219126300544332453575221)
              ·
                refine ⟨1239293090676031167522677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13219126300544332453575221 1239293090676031167522677)
                ·
                  refine ⟨116183727250877921955251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239293090676031167522677 116183727250877921955251)
                  ·
                    rfl

theorem cell23_2036403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 5].length) (baseStart_2036403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036403 prefixEnd_2036403 := by exact prefixLift 2036403
  have htrace : WordTrace (prefixWord ++ tailWord_2036403) baseStart_2036403 baseEnd_2036403 := by
    simpa [prefixWord, tailWord_2036403, baseEnd_2036403] using wordTrace_append hprefix tailTrace_2036403
  have hstable : (prefixWord ++ tailWord_2036403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036403).length < 2 ^ (prefixWord ++ tailWord_2036403).sum := by decide
  have hdescent : baseEnd_2036403 < baseStart_2036403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036413 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 3]
def baseStart_2036413 : Nat := 118140960795 + 2036413 * 2 ^ 59
def prefixEnd_2036413 : Nat := 4983230072969 + 3 ^ 40 * 2036413 * 2
def baseEnd_2036413 : Nat := 1045658680064446258472213

theorem tailTrace_2036413 : CollatzResearch.WordTrace tailWord_2036413 prefixEnd_2036413 1045658680064446258472213 := by
  unfold tailWord_2036413
  simp only [CollatzResearch.WordTrace]
  refine ⟨74274083971430967496401893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49516055980953978330934595 74274083971430967496401893)
  ·
    refine ⟨13926390744643306405575355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74274083971430967496401893 13926390744643306405575355)
    ·
      refine ⟨20889586116964959608363033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13926390744643306405575355 20889586116964959608363033)
      ·
        refine ⟨15667189587723719706272275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20889586116964959608363033 15667189587723719706272275)
        ·
          refine ⟨23500784381585579559408413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667189587723719706272275 23500784381585579559408413)
          ·
            refine ⟨8812794143094592334778155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23500784381585579559408413 8812794143094592334778155)
            ·
              refine ⟨13219191214641888502167233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8812794143094592334778155 13219191214641888502167233)
              ·
                refine ⟨9914393410981416376625425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13219191214641888502167233 9914393410981416376625425)
                ·
                  refine ⟨7435795058236062282469069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9914393410981416376625425 7435795058236062282469069)
                  ·
                    refine ⟨2788423146838523355925901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7435795058236062282469069 2788423146838523355925901)
                    ·
                      refine ⟨1045658680064446258472213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2788423146838523355925901 1045658680064446258472213)
                      ·
                        rfl

theorem cell23_2036413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_2036413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036413 prefixEnd_2036413 := by exact prefixLift 2036413
  have htrace : WordTrace (prefixWord ++ tailWord_2036413) baseStart_2036413 baseEnd_2036413 := by
    simpa [prefixWord, tailWord_2036413, baseEnd_2036413] using wordTrace_append hprefix tailTrace_2036413
  have hstable : (prefixWord ++ tailWord_2036413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036413).length < 2 ^ (prefixWord ++ tailWord_2036413).sum := by decide
  have hdescent : baseEnd_2036413 < baseStart_2036413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036420 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 5]
def baseStart_2036420 : Nat := 118140960795 + 2036420 * 2 ^ 59
def prefixEnd_2036420 : Nat := 4983230072969 + 3 ^ 40 * 2036420 * 2
def baseEnd_2036420 : Nat := 116184697158780859009409

theorem tailTrace_2036420 : CollatzResearch.WordTrace tailWord_2036420 prefixEnd_2036420 116184697158780859009409 := by
  unfold tailWord_2036420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37137169641202803845953357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49516226188270405127937809 37137169641202803845953357)
  ·
    refine ⟨13926438615451051442232509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37137169641202803845953357 13926438615451051442232509)
    ·
      refine ⟨5222414480794144290837191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13926438615451051442232509 5222414480794144290837191)
      ·
        refine ⟨7833621721191216436255787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5222414480794144290837191 7833621721191216436255787)
        ·
          refine ⟨11750432581786824654383681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833621721191216436255787 11750432581786824654383681)
          ·
            refine ⟨8812824436340118490787761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11750432581786824654383681 8812824436340118490787761)
            ·
              refine ⟨6609618327255088868090821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812824436340118490787761 6609618327255088868090821)
              ·
                refine ⟨1239303436360329162767029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6609618327255088868090821 1239303436360329162767029)
                ·
                  refine ⟨116184697158780859009409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239303436360329162767029 116184697158780859009409)
                  ·
                    rfl

theorem cell23_2036420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 5].length) (baseStart_2036420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036420 prefixEnd_2036420 := by exact prefixLift 2036420
  have htrace : WordTrace (prefixWord ++ tailWord_2036420) baseStart_2036420 baseEnd_2036420 := by
    simpa [prefixWord, tailWord_2036420, baseEnd_2036420] using wordTrace_append hprefix tailTrace_2036420
  have hstable : (prefixWord ++ tailWord_2036420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036420).length < 2 ^ (prefixWord ++ tailWord_2036420).sum := by decide
  have hdescent : baseEnd_2036420 < baseStart_2036420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036423 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 2, 5, 2]
def baseStart_2036423 : Nat := 118140960795 + 2036423 * 2 ^ 59
def prefixEnd_2036423 : Nat := 4983230072969 + 3 ^ 40 * 2036423 * 2
def baseEnd_2036423 : Nat := 1045663814870991219347167

theorem tailTrace_2036423 : CollatzResearch.WordTrace tailWord_2036423 prefixEnd_2036423 1045663814870991219347167 := by
  unfold tailWord_2036423
  simp only [CollatzResearch.WordTrace]
  refine ⟨74274448701394739204265923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49516299134263159469510615 74274448701394739204265923)
  ·
    refine ⟨111411673052092108806398885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74274448701394739204265923 111411673052092108806398885)
    ·
      refine ⟨20889688697267270401199791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111411673052092108806398885 20889688697267270401199791)
      ·
        refine ⟨31334533045900905601799687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20889688697267270401199791 31334533045900905601799687)
        ·
          refine ⟨47001799568851358402699531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31334533045900905601799687 47001799568851358402699531)
          ·
            refine ⟨70502699353277037604049297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47001799568851358402699531 70502699353277037604049297)
            ·
              refine ⟨52877024514957778203036973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70502699353277037604049297 52877024514957778203036973)
              ·
                refine ⟨19828884193109166826138865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52877024514957778203036973 19828884193109166826138865)
                ·
                  refine ⟨14871663144831875119604149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19828884193109166826138865 14871663144831875119604149)
                  ·
                    refine ⟨1394218419827988292462889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14871663144831875119604149 1394218419827988292462889)
                    ·
                      refine ⟨1045663814870991219347167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394218419827988292462889 1045663814870991219347167)
                      ·
                        rfl

theorem cell23_2036423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_2036423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036423 prefixEnd_2036423 := by exact prefixLift 2036423
  have htrace : WordTrace (prefixWord ++ tailWord_2036423) baseStart_2036423 baseEnd_2036423 := by
    simpa [prefixWord, tailWord_2036423, baseEnd_2036423] using wordTrace_append hprefix tailTrace_2036423
  have hstable : (prefixWord ++ tailWord_2036423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036423).length < 2 ^ (prefixWord ++ tailWord_2036423).sum := by decide
  have hdescent : baseEnd_2036423 < baseStart_2036423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036453 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2036453 : Nat := 118140960795 + 2036453 * 2 ^ 59
def prefixEnd_2036453 : Nat := 4983230072969 + 3 ^ 40 * 2036453 * 2
def baseEnd_2036453 : Nat := 1045679219290626101972029

theorem tailTrace_2036453 : CollatzResearch.WordTrace tailWord_2036453 prefixEnd_2036453 1045679219290626101972029 := by
  unfold tailWord_2036453
  simp only [CollatzResearch.WordTrace]
  refine ⟨74275542891286054327858013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49517028594190702885238675 74275542891286054327858013)
  ·
    refine ⟨27853328584232270372946755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74275542891286054327858013 27853328584232270372946755)
    ·
      refine ⟨41779992876348405559420133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27853328584232270372946755 41779992876348405559420133)
      ·
        refine ⟨7833748664315326042391275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41779992876348405559420133 7833748664315326042391275)
        ·
          refine ⟨11750622996472989063586913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7833748664315326042391275 11750622996472989063586913)
          ·
            refine ⟨8812967247354741797690185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11750622996472989063586913 8812967247354741797690185)
            ·
              refine ⟨6609725435516056348267639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8812967247354741797690185 6609725435516056348267639)
              ·
                refine ⟨9914588153274084522401459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6609725435516056348267639 9914588153274084522401459)
                ·
                  refine ⟨14871882229911126783602189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9914588153274084522401459 14871882229911126783602189)
                  ·
                    refine ⟨5576955836216672543850821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14871882229911126783602189 5576955836216672543850821)
                    ·
                      refine ⟨1045679219290626101972029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5576955836216672543850821 1045679219290626101972029)
                      ·
                        rfl

theorem cell23_2036453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2036453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036453 prefixEnd_2036453 := by exact prefixLift 2036453
  have htrace : WordTrace (prefixWord ++ tailWord_2036453) baseStart_2036453 baseEnd_2036453 := by
    simpa [prefixWord, tailWord_2036453, baseEnd_2036453] using wordTrace_append hprefix tailTrace_2036453
  have hstable : (prefixWord ++ tailWord_2036453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036453).length < 2 ^ (prefixWord ++ tailWord_2036453).sum := by decide
  have hdescent : baseEnd_2036453 < baseStart_2036453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036470 : List Nat := [5, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_2036470 : Nat := 118140960795 + 2036470 * 2 ^ 59
def prefixEnd_2036470 : Nat := 4983230072969 + 3 ^ 40 * 2036470 * 2
def baseEnd_2036470 : Nat := 1045687948461752535459451

theorem tailTrace_2036470 : CollatzResearch.WordTrace tailWord_2036470 prefixEnd_2036470 1045687948461752535459451 := by
  unfold tailWord_2036470
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642260183264029139451679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49517441954816310820817909 4642260183264029139451679)
  ·
    refine ⟨6963390274896043709177519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4642260183264029139451679 6963390274896043709177519)
    ·
      refine ⟨10445085412344065563766279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6963390274896043709177519 10445085412344065563766279)
      ·
        refine ⟨15667628118516098345649419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10445085412344065563766279 15667628118516098345649419)
        ·
          refine ⟨23501442177774147518474129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15667628118516098345649419 23501442177774147518474129)
          ·
            refine ⟨17626081633330610638855597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23501442177774147518474129 17626081633330610638855597)
            ·
              refine ⟨6609780612498978989570849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17626081633330610638855597 6609780612498978989570849)
              ·
                refine ⟨4957335459374234242178137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6609780612498978989570849 4957335459374234242178137)
                ·
                  refine ⟨3718001594530675681633603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957335459374234242178137 3718001594530675681633603)
                  ·
                    refine ⟨5577002391796013522450405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3718001594530675681633603 5577002391796013522450405)
                    ·
                      refine ⟨1045687948461752535459451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5577002391796013522450405 1045687948461752535459451)
                      ·
                        rfl

theorem cell23_2036470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_2036470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036470 prefixEnd_2036470 := by exact prefixLift 2036470
  have htrace : WordTrace (prefixWord ++ tailWord_2036470) baseStart_2036470 baseEnd_2036470 := by
    simpa [prefixWord, tailWord_2036470, baseEnd_2036470] using wordTrace_append hprefix tailTrace_2036470
  have hstable : (prefixWord ++ tailWord_2036470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036470).length < 2 ^ (prefixWord ++ tailWord_2036470).sum := by decide
  have hdescent : baseEnd_2036470 < baseStart_2036470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036553 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 1, 6]
def baseStart_2036553 : Nat := 118140960795 + 2036553 * 2 ^ 59
def prefixEnd_2036553 : Nat := 4983230072969 + 3 ^ 40 * 2036553 * 2
def baseEnd_2036553 : Nat := 348576855785358570240523

theorem tailTrace_2036553 : CollatzResearch.WordTrace tailWord_2036553 prefixEnd_2036553 348576855785358570240523 := by
  unfold tailWord_2036553
  simp only [CollatzResearch.WordTrace]
  refine ⟨74279190190923771406498313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49519460127282514270998875 74279190190923771406498313)
  ·
    refine ⟨55709392643192828554873735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74279190190923771406498313 55709392643192828554873735)
    ·
      refine ⟨83564088964789242832310603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55709392643192828554873735 83564088964789242832310603)
      ·
        refine ⟨125346133447183864248465905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83564088964789242832310603 125346133447183864248465905)
        ·
          refine ⟨94009600085387898186349429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125346133447183864248465905 94009600085387898186349429)
          ·
            refine ⟨8813400008005115454970259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94009600085387898186349429 8813400008005115454970259)
            ·
              refine ⟨13220100012007673182455389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8813400008005115454970259 13220100012007673182455389)
              ·
                refine ⟨4957537504502877443420771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13220100012007673182455389 4957537504502877443420771)
                ·
                  refine ⟨7436306256754316165131157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4957537504502877443420771 7436306256754316165131157)
                  ·
                    refine ⟨348576855785358570240523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7436306256754316165131157 348576855785358570240523)
                    ·
                      rfl

theorem cell23_2036553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 6].length) (baseStart_2036553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036553 prefixEnd_2036553 := by exact prefixLift 2036553
  have htrace : WordTrace (prefixWord ++ tailWord_2036553) baseStart_2036553 baseEnd_2036553 := by
    simpa [prefixWord, tailWord_2036553, baseEnd_2036553] using wordTrace_append hprefix tailTrace_2036553
  have hstable : (prefixWord ++ tailWord_2036553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036553).length < 2 ^ (prefixWord ++ tailWord_2036553).sum := by decide
  have hdescent : baseEnd_2036553 < baseStart_2036553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036583 : List Nat := [1, 1, 5, 1, 2, 3, 10]
def baseStart_2036583 : Nat := 118140960795 + 2036583 * 2 ^ 59
def prefixEnd_2036583 : Nat := 4983230072969 + 3 ^ 40 * 2036583 * 2
def baseEnd_2036583 : Nat := 12910444095996427078351

theorem tailTrace_2036583 : CollatzResearch.WordTrace tailWord_2036583 prefixEnd_2036583 12910444095996427078351 := by
  unfold tailWord_2036583
  simp only [CollatzResearch.WordTrace]
  refine ⟨74280284380815086530090403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49520189587210057686726935 74280284380815086530090403)
  ·
    refine ⟨111420426571222629795135605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74280284380815086530090403 111420426571222629795135605)
    ·
      refine ⟨10445664991052121543293963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111420426571222629795135605 10445664991052121543293963)
      ·
        refine ⟨15668497486578182314940945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10445664991052121543293963 15668497486578182314940945)
        ·
          refine ⟨11751373114933636736205709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15668497486578182314940945 11751373114933636736205709)
          ·
            refine ⟨4406764918100113776077141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11751373114933636736205709 4406764918100113776077141)
            ·
              refine ⟨12910444095996427078351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4406764918100113776077141 12910444095996427078351)
              ·
                rfl

theorem cell23_2036583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 10].length) (baseStart_2036583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036583 prefixEnd_2036583 := by exact prefixLift 2036583
  have htrace : WordTrace (prefixWord ++ tailWord_2036583) baseStart_2036583 baseEnd_2036583 := by
    simpa [prefixWord, tailWord_2036583, baseEnd_2036583] using wordTrace_append hprefix tailTrace_2036583
  have hstable : (prefixWord ++ tailWord_2036583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036583).length < 2 ^ (prefixWord ++ tailWord_2036583).sum := by decide
  have hdescent : baseEnd_2036583 < baseStart_2036583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036633 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 4]
def baseStart_2036633 : Nat := 118140960795 + 2036633 * 2 ^ 59
def prefixEnd_2036633 : Nat := 4983230072969 + 3 ^ 40 * 2036633 * 2
def baseEnd_2036633 : Nat := 1045771645808435397721201

theorem tailTrace_2036633 : CollatzResearch.WordTrace tailWord_2036633 prefixEnd_2036633 1045771645808435397721201 := by
  unfold tailWord_2036633
  simp only [CollatzResearch.WordTrace]
  refine ⟨74282108030633945069410553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49521405353755963379607035 74282108030633945069410553)
  ·
    refine ⟨55711581022975458802057915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74282108030633945069410553 55711581022975458802057915)
    ·
      refine ⟨83567371534463188203086873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55711581022975458802057915 83567371534463188203086873)
      ·
        refine ⟨62675528650847391152315155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83567371534463188203086873 62675528650847391152315155)
        ·
          refine ⟨94013292976271086728472733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62675528650847391152315155 94013292976271086728472733)
          ·
            refine ⟨35254984866101657523177275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94013292976271086728472733 35254984866101657523177275)
            ·
              refine ⟨52882477299152486284765913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35254984866101657523177275 52882477299152486284765913)
              ·
                refine ⟨39661857974364364713574435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52882477299152486284765913 39661857974364364713574435)
                ·
                  refine ⟨59492786961546547070361653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39661857974364364713574435 59492786961546547070361653)
                  ·
                    refine ⟨5577448777644988787846405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59492786961546547070361653 5577448777644988787846405)
                    ·
                      refine ⟨1045771645808435397721201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5577448777644988787846405 1045771645808435397721201)
                      ·
                        rfl

theorem cell23_2036633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_2036633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036633 prefixEnd_2036633 := by exact prefixLift 2036633
  have htrace : WordTrace (prefixWord ++ tailWord_2036633) baseStart_2036633 baseEnd_2036633 := by
    simpa [prefixWord, tailWord_2036633, baseEnd_2036633] using wordTrace_append hprefix tailTrace_2036633
  have hstable : (prefixWord ++ tailWord_2036633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036633).length < 2 ^ (prefixWord ++ tailWord_2036633).sum := by decide
  have hdescent : baseEnd_2036633 < baseStart_2036633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036643 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 4, 6]
def baseStart_2036643 : Nat := 118140960795 + 2036643 * 2 ^ 59
def prefixEnd_2036643 : Nat := 4983230072969 + 3 ^ 40 * 2036643 * 2
def baseEnd_2036643 : Nat := 348592260204993452865385

theorem tailTrace_2036643 : CollatzResearch.WordTrace tailWord_2036643 prefixEnd_2036643 348592260204993452865385 := by
  unfold tailWord_2036643
  simp only [CollatzResearch.WordTrace]
  refine ⟨74282472760597716777274583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49521648507065144518183055 74282472760597716777274583)
  ·
    refine ⟨111423709140896575165911875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74282472760597716777274583 111423709140896575165911875)
    ·
      refine ⟨167135563711344862748867813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111423709140896575165911875 167135563711344862748867813)
      ·
        refine ⟨31337918195877161765412715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167135563711344862748867813 31337918195877161765412715)
        ·
          refine ⟨47006877293815742648119073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31337918195877161765412715 47006877293815742648119073)
          ·
            refine ⟨35255157970361806986089305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47006877293815742648119073 35255157970361806986089305)
            ·
              refine ⟨26441368477771355239566979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35255157970361806986089305 26441368477771355239566979)
              ·
                refine ⟨39662052716657032859350469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26441368477771355239566979 39662052716657032859350469)
                ·
                  refine ⟨7436634884373193661128213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39662052716657032859350469 7436634884373193661128213)
                  ·
                    refine ⟨348592260204993452865385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7436634884373193661128213 348592260204993452865385)
                    ·
                      rfl

theorem cell23_2036643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 4, 6].length) (baseStart_2036643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036643 prefixEnd_2036643 := by exact prefixLift 2036643
  have htrace : WordTrace (prefixWord ++ tailWord_2036643) baseStart_2036643 baseEnd_2036643 := by
    simpa [prefixWord, tailWord_2036643, baseEnd_2036643] using wordTrace_append hprefix tailTrace_2036643
  have hstable : (prefixWord ++ tailWord_2036643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036643).length < 2 ^ (prefixWord ++ tailWord_2036643).sum := by decide
  have hdescent : baseEnd_2036643 < baseStart_2036643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036670 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2036670 : Nat := 118140960795 + 2036670 * 2 ^ 59
def prefixEnd_2036670 : Nat := 4983230072969 + 3 ^ 40 * 2036670 * 2
def baseEnd_2036670 : Nat := 1045790644592651752958531

theorem tailTrace_2036670 : CollatzResearch.WordTrace tailWord_2036670 prefixEnd_2036670 1045790644592651752958531 := by
  unfold tailWord_2036670
  simp only [CollatzResearch.WordTrace]
  refine ⟨9285432191437487548563433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49522305020999933592338309 9285432191437487548563433)
  ·
    refine ⟨6964074143578115661422575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9285432191437487548563433 6964074143578115661422575)
    ·
      refine ⟨10446111215367173492133863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6964074143578115661422575 10446111215367173492133863)
      ·
        refine ⟨15669166823050760238200795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446111215367173492133863 15669166823050760238200795)
        ·
          refine ⟨23503750234576140357301193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15669166823050760238200795 23503750234576140357301193)
          ·
            refine ⟨17627812675932105267975895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23503750234576140357301193 17627812675932105267975895)
            ·
              refine ⟨26441719013898157901963843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17627812675932105267975895 26441719013898157901963843)
              ·
                refine ⟨39662578520847236852945765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26441719013898157901963843 39662578520847236852945765)
                ·
                  refine ⟨7436733472658856909927331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39662578520847236852945765 7436733472658856909927331)
                  ·
                    refine ⟨11155100208988285364890997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7436733472658856909927331 11155100208988285364890997)
                    ·
                      refine ⟨1045790644592651752958531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11155100208988285364890997 1045790644592651752958531)
                      ·
                        rfl

theorem cell23_2036670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2036670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036670 prefixEnd_2036670 := by exact prefixLift 2036670
  have htrace : WordTrace (prefixWord ++ tailWord_2036670) baseStart_2036670 baseEnd_2036670 := by
    simpa [prefixWord, tailWord_2036670, baseEnd_2036670] using wordTrace_append hprefix tailTrace_2036670
  have hstable : (prefixWord ++ tailWord_2036670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036670).length < 2 ^ (prefixWord ++ tailWord_2036670).sum := by decide
  have hdescent : baseEnd_2036670 < baseStart_2036670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036701 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 2, 2, 2]
def baseStart_2036701 : Nat := 118140960795 + 2036701 * 2 ^ 59
def prefixEnd_2036701 : Nat := 4983230072969 + 3 ^ 40 * 2036701 * 2
def baseEnd_2036701 : Nat := 1045806562492941131670889

theorem tailTrace_2036701 : CollatzResearch.WordTrace tailWord_2036701 prefixEnd_2036701 1045806562492941131670889 := by
  unfold tailWord_2036701
  simp only [CollatzResearch.WordTrace]
  refine ⟨74284588194387592682885957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49523058796258395121923971 74284588194387592682885957)
  ·
    refine ⟨13928360286447673628041117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74284588194387592682885957 13928360286447673628041117)
    ·
      refine ⟨5223135107417877610515419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13928360286447673628041117 5223135107417877610515419)
      ·
        refine ⟨7834702661126816415773129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5223135107417877610515419 7834702661126816415773129)
        ·
          refine ⟨5876026995845112311829847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7834702661126816415773129 5876026995845112311829847)
          ·
            refine ⟨8814040493767668467744771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876026995845112311829847 8814040493767668467744771)
            ·
              refine ⟨13221060740651502701617157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814040493767668467744771 13221060740651502701617157)
              ·
                refine ⟨2478948888872156756553217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13221060740651502701617157 2478948888872156756553217)
                ·
                  refine ⟨1859211666654117567414913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2478948888872156756553217 1859211666654117567414913)
                  ·
                    refine ⟨1394408749990588175561185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859211666654117567414913 1394408749990588175561185)
                    ·
                      refine ⟨1045806562492941131670889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394408749990588175561185 1045806562492941131670889)
                      ·
                        rfl

theorem cell23_2036701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_2036701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036701 prefixEnd_2036701 := by exact prefixLift 2036701
  have htrace : WordTrace (prefixWord ++ tailWord_2036701) baseStart_2036701 baseEnd_2036701 := by
    simpa [prefixWord, tailWord_2036701, baseEnd_2036701] using wordTrace_append hprefix tailTrace_2036701
  have hstable : (prefixWord ++ tailWord_2036701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036701).length < 2 ^ (prefixWord ++ tailWord_2036701).sum := by decide
  have hdescent : baseEnd_2036701 < baseStart_2036701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036707 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 5]
def baseStart_2036707 : Nat := 118140960795 + 2036707 * 2 ^ 59
def prefixEnd_2036707 : Nat := 4983230072969 + 3 ^ 40 * 2036707 * 2
def baseEnd_2036707 : Nat := 116201071486318678688429

theorem tailTrace_2036707 : CollatzResearch.WordTrace tailWord_2036707 prefixEnd_2036707 116201071486318678688429 := by
  unfold tailWord_2036707
  simp only [CollatzResearch.WordTrace]
  refine ⟨74284807032365855707604375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49523204688243903805069583 74284807032365855707604375)
  ·
    refine ⟨111427210548548783561406563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74284807032365855707604375 111427210548548783561406563)
    ·
      refine ⟨167140815822823175342109845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111427210548548783561406563 167140815822823175342109845)
      ·
        refine ⟨7834725741694836344161399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167140815822823175342109845 7834725741694836344161399)
        ·
          refine ⟨11752088612542254516242099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7834725741694836344161399 11752088612542254516242099)
          ·
            refine ⟨17628132918813381774363149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11752088612542254516242099 17628132918813381774363149)
            ·
              refine ⟨6610549844555018165386181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17628132918813381774363149 6610549844555018165386181)
              ·
                refine ⟨1239478095854065906009909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6610549844555018165386181 1239478095854065906009909)
                ·
                  refine ⟨116201071486318678688429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1239478095854065906009909 116201071486318678688429)
                  ·
                    rfl

theorem cell23_2036707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 5].length) (baseStart_2036707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036707 prefixEnd_2036707 := by exact prefixLift 2036707
  have htrace : WordTrace (prefixWord ++ tailWord_2036707) baseStart_2036707 baseEnd_2036707 := by
    simpa [prefixWord, tailWord_2036707, baseEnd_2036707] using wordTrace_append hprefix tailTrace_2036707
  have hstable : (prefixWord ++ tailWord_2036707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036707).length < 2 ^ (prefixWord ++ tailWord_2036707).sum := by decide
  have hdescent : baseEnd_2036707 < baseStart_2036707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036737 : List Nat := [1, 2, 4, 1, 2, 2, 3, 1, 2, 5]
def baseStart_2036737 : Nat := 118140960795 + 2036737 * 2 ^ 59
def prefixEnd_2036737 : Nat := 4983230072969 + 3 ^ 40 * 2036737 * 2
def baseEnd_2036737 : Nat := 348608349265500996940241

theorem tailTrace_2036737 : CollatzResearch.WordTrace tailWord_2036737 prefixEnd_2036737 348608349265500996940241 := by
  unfold tailWord_2036737
  simp only [CollatzResearch.WordTrace]
  refine ⟨74285901222257170831196465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49523934148171447220797643 74285901222257170831196465)
  ·
    refine ⟨55714425916692878123397349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74285901222257170831196465 55714425916692878123397349)
    ·
      refine ⟨10446454859379914648137003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55714425916692878123397349 10446454859379914648137003)
      ·
        refine ⟨15669682289069871972205505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446454859379914648137003 15669682289069871972205505)
        ·
          refine ⟨11752261716802403979154129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15669682289069871972205505 11752261716802403979154129)
          ·
            refine ⟨8814196287601802984365597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11752261716802403979154129 8814196287601802984365597)
            ·
              refine ⟨3305323607850676119137099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8814196287601802984365597 3305323607850676119137099)
              ·
                refine ⟨4957985411776014178705649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305323607850676119137099 4957985411776014178705649)
                ·
                  refine ⟨3718489058832010634029237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4957985411776014178705649 3718489058832010634029237)
                  ·
                    refine ⟨348608349265500996940241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3718489058832010634029237 348608349265500996940241)
                    ·
                      rfl

theorem cell23_2036737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_2036737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036737 prefixEnd_2036737 := by exact prefixLift 2036737
  have htrace : WordTrace (prefixWord ++ tailWord_2036737) baseStart_2036737 baseEnd_2036737 := by
    simpa [prefixWord, tailWord_2036737, baseEnd_2036737] using wordTrace_append hprefix tailTrace_2036737
  have hstable : (prefixWord ++ tailWord_2036737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036737).length < 2 ^ (prefixWord ++ tailWord_2036737).sum := by decide
  have hdescent : baseEnd_2036737 < baseStart_2036737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036767 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 3, 4]
def baseStart_2036767 : Nat := 118140960795 + 2036767 * 2 ^ 59
def prefixEnd_2036767 : Nat := 4983230072969 + 3 ^ 40 * 2036767 * 2
def baseEnd_2036767 : Nat := 348613484072045957815195

theorem tailTrace_2036767 : CollatzResearch.WordTrace tailWord_2036767 prefixEnd_2036767 348613484072045957815195 := by
  unfold tailWord_2036767
  simp only [CollatzResearch.WordTrace]
  refine ⟨74286995412148485954788555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49524663608098990636525703 74286995412148485954788555)
  ·
    refine ⟨111430493118222728932182833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74286995412148485954788555 111430493118222728932182833)
    ·
      refine ⟨83572869838667046699137125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111430493118222728932182833 83572869838667046699137125)
      ·
        refine ⟨15669913094750071256088211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83572869838667046699137125 15669913094750071256088211)
        ·
          refine ⟨23504869642125106884132317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15669913094750071256088211 23504869642125106884132317)
          ·
            refine ⟨8814326115796915081549619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23504869642125106884132317 8814326115796915081549619)
            ·
              refine ⟨13221489173695372622324429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8814326115796915081549619 13221489173695372622324429)
              ·
                refine ⟨4958058440135764733371661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13221489173695372622324429 4958058440135764733371661)
                ·
                  refine ⟨1859271915050911775014373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4958058440135764733371661 1859271915050911775014373)
                  ·
                    refine ⟨348613484072045957815195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859271915050911775014373 348613484072045957815195)
                    ·
                      rfl

theorem cell23_2036767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 4].length) (baseStart_2036767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036767 prefixEnd_2036767 := by exact prefixLift 2036767
  have htrace : WordTrace (prefixWord ++ tailWord_2036767) baseStart_2036767 baseEnd_2036767 := by
    simpa [prefixWord, tailWord_2036767, baseEnd_2036767] using wordTrace_append hprefix tailTrace_2036767
  have hstable : (prefixWord ++ tailWord_2036767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036767).length < 2 ^ (prefixWord ++ tailWord_2036767).sum := by decide
  have hdescent : baseEnd_2036767 < baseStart_2036767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036818 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_2036818 : Nat := 118140960795 + 2036818 * 2 ^ 59
def prefixEnd_2036818 : Nat := 4983230072969 + 3 ^ 40 * 2036818 * 2
def baseEnd_2036818 : Nat := 348622213243172391302617

theorem tailTrace_2036818 : CollatzResearch.WordTrace tailWord_2036818 prefixEnd_2036818 348622213243172391302617 := by
  unfold tailWord_2036818
  simp only [CollatzResearch.WordTrace]
  refine ⟨18572213883740930416223777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49525903689975814443263405 18572213883740930416223777)
  ·
    refine ⟨13929160412805697812167833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18572213883740930416223777 13929160412805697812167833)
    ·
      refine ⟨10446870309604273359125875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13929160412805697812167833 10446870309604273359125875)
      ·
        refine ⟨15670305464406410038688813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10446870309604273359125875 15670305464406410038688813)
        ·
          refine ⟨5876364549152403764508305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15670305464406410038688813 5876364549152403764508305)
          ·
            refine ⟨4407273411864302823381229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5876364549152403764508305 4407273411864302823381229)
            ·
              refine ⟨1652727529449113558767961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4407273411864302823381229 1652727529449113558767961)
              ·
                refine ⟨1239545647086835169075971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1652727529449113558767961 1239545647086835169075971)
                ·
                  refine ⟨1859318470630252753613957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239545647086835169075971 1859318470630252753613957)
                  ·
                    refine ⟨348622213243172391302617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859318470630252753613957 348622213243172391302617)
                    ·
                      rfl

theorem cell23_2036818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_2036818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036818 prefixEnd_2036818 := by exact prefixLift 2036818
  have htrace : WordTrace (prefixWord ++ tailWord_2036818) baseStart_2036818 baseEnd_2036818 := by
    simpa [prefixWord, tailWord_2036818, baseEnd_2036818] using wordTrace_append hprefix tailTrace_2036818
  have hstable : (prefixWord ++ tailWord_2036818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036818).length < 2 ^ (prefixWord ++ tailWord_2036818).sum := by decide
  have hdescent : baseEnd_2036818 < baseStart_2036818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036847 : List Nat := [1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 4]
def baseStart_2036847 : Nat := 118140960795 + 2036847 * 2 ^ 59
def prefixEnd_2036847 : Nat := 4983230072969 + 3 ^ 40 * 2036847 * 2
def baseEnd_2036847 : Nat := 1045881530668497560445217

theorem tailTrace_2036847 : CollatzResearch.WordTrace tailWord_2036847 prefixEnd_2036847 1045881530668497560445217 := by
  unfold tailWord_2036847
  simp only [CollatzResearch.WordTrace]
  refine ⟨74289913251858659617700795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49526608834572439745133863 74289913251858659617700795)
  ·
    refine ⟨111434869877787989426551193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74289913251858659617700795 111434869877787989426551193)
    ·
      refine ⟨83576152408340992069913395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111434869877787989426551193 83576152408340992069913395)
      ·
        refine ⟨125364228612511488104870093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83576152408340992069913395 125364228612511488104870093)
        ·
          refine ⟨47011585729691808039326285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125364228612511488104870093 47011585729691808039326285)
          ·
            refine ⟨17629344648634428014747357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47011585729691808039326285 17629344648634428014747357)
            ·
              refine ⟨6611004243237910505530259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17629344648634428014747357 6611004243237910505530259)
              ·
                refine ⟨9916506364856865758295389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6611004243237910505530259 9916506364856865758295389)
                ·
                  refine ⟨3718689886821324659360771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9916506364856865758295389 3718689886821324659360771)
                  ·
                    refine ⟨5578034830231986989041157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3718689886821324659360771 5578034830231986989041157)
                    ·
                      refine ⟨1045881530668497560445217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5578034830231986989041157 1045881530668497560445217)
                      ·
                        rfl

theorem cell23_2036847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 4].length) (baseStart_2036847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036847 prefixEnd_2036847 := by exact prefixLift 2036847
  have htrace : WordTrace (prefixWord ++ tailWord_2036847) baseStart_2036847 baseEnd_2036847 := by
    simpa [prefixWord, tailWord_2036847, baseEnd_2036847] using wordTrace_append hprefix tailTrace_2036847
  have hstable : (prefixWord ++ tailWord_2036847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036847).length < 2 ^ (prefixWord ++ tailWord_2036847).sum := by decide
  have hdescent : baseEnd_2036847 < baseStart_2036847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036880 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7]
def baseStart_2036880 : Nat := 118140960795 + 2036880 * 2 ^ 59
def prefixEnd_2036880 : Nat := 4983230072969 + 3 ^ 40 * 2036880 * 2
def baseEnd_2036880 : Nat := 1045898475530095931332565

theorem tailTrace_2036880 : CollatzResearch.WordTrace tailWord_2036880 prefixEnd_2036880 1045898475530095931332565 := by
  unfold tailWord_2036880
  simp only [CollatzResearch.WordTrace]
  refine ⟨37145558430369553126826047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49527411240492737502434729 37145558430369553126826047)
  ·
    refine ⟨55718337645554329690239071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37145558430369553126826047 55718337645554329690239071)
    ·
      refine ⟨83577506468331494535358607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55718337645554329690239071 83577506468331494535358607)
      ·
        refine ⟨125366259702497241803037911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83577506468331494535358607 125366259702497241803037911)
        ·
          refine ⟨188049389553745862704556867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125366259702497241803037911 188049389553745862704556867)
          ·
            refine ⟨282074084330618794056835301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188049389553745862704556867 282074084330618794056835301)
            ·
              refine ⟨52888890811991023885656619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282074084330618794056835301 52888890811991023885656619)
              ·
                refine ⟨79333336217986535828484929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52888890811991023885656619 79333336217986535828484929)
                ·
                  refine ⟨59500002163489901871363697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79333336217986535828484929 59500002163489901871363697)
                  ·
                    refine ⟨44625001622617426403522773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59500002163489901871363697 44625001622617426403522773)
                    ·
                      refine ⟨1045898475530095931332565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44625001622617426403522773 1045898475530095931332565)
                      ·
                        rfl

theorem cell23_2036880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_2036880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036880 prefixEnd_2036880 := by exact prefixLift 2036880
  have htrace : WordTrace (prefixWord ++ tailWord_2036880) baseStart_2036880 baseEnd_2036880 := by
    simpa [prefixWord, tailWord_2036880, baseEnd_2036880] using wordTrace_append hprefix tailTrace_2036880
  have hstable : (prefixWord ++ tailWord_2036880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036880).length < 2 ^ (prefixWord ++ tailWord_2036880).sum := by decide
  have hdescent : baseEnd_2036880 < baseStart_2036880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036887 : List Nat := [1, 1, 3, 3, 3, 1, 3, 8]
def baseStart_2036887 : Nat := 118140960795 + 2036887 * 2 ^ 59
def prefixEnd_2036887 : Nat := 4983230072969 + 3 ^ 40 * 2036887 * 2
def baseEnd_2036887 : Nat := 38737113699802866812779

theorem tailTrace_2036887 : CollatzResearch.WordTrace tailWord_2036887 prefixEnd_2036887 38737113699802866812779 := by
  unfold tailWord_2036887
  simp only [CollatzResearch.WordTrace]
  refine ⟨74291372171713746449156915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49527581447809164299437943 74291372171713746449156915)
  ·
    refine ⟨111437058257570619673735373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74291372171713746449156915 111437058257570619673735373)
    ·
      refine ⟨41788896846588982377650765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111437058257570619673735373 41788896846588982377650765)
      ·
        refine ⟨15670836317470868391619037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41788896846588982377650765 15670836317470868391619037)
        ·
          refine ⟨5876563619051575646857139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15670836317470868391619037 5876563619051575646857139)
          ·
            refine ⟨8814845428577363470285709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5876563619051575646857139 8814845428577363470285709)
            ·
              refine ⟨3305567035716511301357141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8814845428577363470285709 3305567035716511301357141)
              ·
                refine ⟨38737113699802866812779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3305567035716511301357141 38737113699802866812779)
                ·
                  rfl

theorem cell23_2036887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 8].length) (baseStart_2036887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036887 prefixEnd_2036887 := by exact prefixLift 2036887
  have htrace : WordTrace (prefixWord ++ tailWord_2036887) baseStart_2036887 baseEnd_2036887 := by
    simpa [prefixWord, tailWord_2036887, baseEnd_2036887] using wordTrace_append hprefix tailTrace_2036887
  have hstable : (prefixWord ++ tailWord_2036887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036887).length < 2 ^ (prefixWord ++ tailWord_2036887).sum := by decide
  have hdescent : baseEnd_2036887 < baseStart_2036887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036914 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_2036914 : Nat := 118140960795 + 2036914 * 2 ^ 59
def prefixEnd_2036914 : Nat := 4983230072969 + 3 ^ 40 * 2036914 * 2
def baseEnd_2036914 : Nat := 1045915933872348798307409

theorem tailTrace_2036914 : CollatzResearch.WordTrace tailWord_2036914 prefixEnd_2036914 1045915933872348798307409 := by
  unfold tailWord_2036914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18573089235653982515097449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49528237961743953373593197 18573089235653982515097449)
  ·
    refine ⟨13929816926740486886323087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18573089235653982515097449 13929816926740486886323087)
    ·
      refine ⟨20894725390110730329484631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13929816926740486886323087 20894725390110730329484631)
      ·
        refine ⟨31342088085166095494226947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20894725390110730329484631 31342088085166095494226947)
        ·
          refine ⟨47013132127749143241340421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31342088085166095494226947 47013132127749143241340421)
          ·
            refine ⟨8814962273952964357751329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47013132127749143241340421 8814962273952964357751329)
            ·
              refine ⟨6611221705464723268313497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8814962273952964357751329 6611221705464723268313497)
              ·
                refine ⟨4958416279098542451235123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6611221705464723268313497 4958416279098542451235123)
                ·
                  refine ⟨7437624418647813676852685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4958416279098542451235123 7437624418647813676852685)
                  ·
                    refine ⟨2789109156992930128819757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7437624418647813676852685 2789109156992930128819757)
                    ·
                      refine ⟨1045915933872348798307409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2789109156992930128819757 1045915933872348798307409)
                      ·
                        rfl

theorem cell23_2036914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_2036914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036914 prefixEnd_2036914 := by exact prefixLift 2036914
  have htrace : WordTrace (prefixWord ++ tailWord_2036914) baseStart_2036914 baseEnd_2036914 := by
    simpa [prefixWord, tailWord_2036914, baseEnd_2036914] using wordTrace_append hprefix tailTrace_2036914
  have hstable : (prefixWord ++ tailWord_2036914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036914).length < 2 ^ (prefixWord ++ tailWord_2036914).sum := by decide
  have hdescent : baseEnd_2036914 < baseStart_2036914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2036971 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 4, 2, 2]
def baseStart_2036971 : Nat := 118140960795 + 2036971 * 2 ^ 59
def prefixEnd_2036971 : Nat := 4983230072969 + 3 ^ 40 * 2036971 * 2
def baseEnd_2036971 : Nat := 1045945202269655075294647

theorem tailTrace_2036971 : CollatzResearch.WordTrace tailWord_2036971 prefixEnd_2036971 1045945202269655075294647 := by
  unfold tailWord_2036971
  simp only [CollatzResearch.WordTrace]
  refine ⟨74294435903409428795214767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49529623935606285863476511 74294435903409428795214767)
  ·
    refine ⟨111441653855114143192822151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74294435903409428795214767 111441653855114143192822151)
    ·
      refine ⟨167162480782671214789233227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111441653855114143192822151 167162480782671214789233227)
      ·
        refine ⟨250743721174006822183849841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167162480782671214789233227 250743721174006822183849841)
        ·
          refine ⟨188057790880505116637887381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250743721174006822183849841 188057790880505116637887381)
          ·
            refine ⟨8815208947523677342400971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188057790880505116637887381 8815208947523677342400971)
            ·
              refine ⟨13222813421285516013601457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815208947523677342400971 13222813421285516013601457)
              ·
                refine ⟨9917110065964137010201093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13222813421285516013601457 9917110065964137010201093)
                ·
                  refine ⟨1859458137368275689412705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9917110065964137010201093 1859458137368275689412705)
                  ·
                    refine ⟨1394593603026206767059529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859458137368275689412705 1394593603026206767059529)
                    ·
                      refine ⟨1045945202269655075294647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394593603026206767059529 1045945202269655075294647)
                      ·
                        rfl

theorem cell23_2036971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4, 2, 2].length) (baseStart_2036971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2036971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2036971 prefixEnd_2036971 := by exact prefixLift 2036971
  have htrace : WordTrace (prefixWord ++ tailWord_2036971) baseStart_2036971 baseEnd_2036971 := by
    simpa [prefixWord, tailWord_2036971, baseEnd_2036971] using wordTrace_append hprefix tailTrace_2036971
  have hstable : (prefixWord ++ tailWord_2036971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2036971).length < 2 ^ (prefixWord ++ tailWord_2036971).sum := by decide
  have hdescent : baseEnd_2036971 < baseStart_2036971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2036971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037064 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 1, 4, 3]
def baseStart_2037064 : Nat := 118140960795 + 2037064 * 2 ^ 59
def prefixEnd_2037064 : Nat := 4983230072969 + 3 ^ 40 * 2037064 * 2
def baseEnd_2037064 : Nat := 1045992955970523211431719

theorem tailTrace_2037064 : CollatzResearch.WordTrace tailWord_2037064 prefixEnd_2037064 1045992955970523211431719 := by
  unfold tailWord_2037064
  simp only [CollatzResearch.WordTrace]
  refine ⟨37148913946036252839175123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49531885261381670452233497 37148913946036252839175123)
  ·
    refine ⟨55723370919054379258762685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37148913946036252839175123 55723370919054379258762685)
    ·
      refine ⟨20896264094645392222036007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55723370919054379258762685 20896264094645392222036007)
      ·
        refine ⟨31344396141968088333054011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20896264094645392222036007 31344396141968088333054011)
        ·
          refine ⟨47016594212952132499581017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31344396141968088333054011 47016594212952132499581017)
          ·
            refine ⟨35262445659714099374685763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47016594212952132499581017 35262445659714099374685763)
            ·
              refine ⟨52893668489571149062028645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35262445659714099374685763 52893668489571149062028645)
              ·
                refine ⟨9917562841794590449130371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52893668489571149062028645 9917562841794590449130371)
                ·
                  refine ⟨14876344262691885673695557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9917562841794590449130371 14876344262691885673695557)
                  ·
                    refine ⟨2789314549254728563817917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14876344262691885673695557 2789314549254728563817917)
                    ·
                      refine ⟨1045992955970523211431719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2789314549254728563817917 1045992955970523211431719)
                      ·
                        rfl

theorem cell23_2037064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_2037064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037064 prefixEnd_2037064 := by exact prefixLift 2037064
  have htrace : WordTrace (prefixWord ++ tailWord_2037064) baseStart_2037064 baseEnd_2037064 := by
    simpa [prefixWord, tailWord_2037064, baseEnd_2037064] using wordTrace_append hprefix tailTrace_2037064
  have hstable : (prefixWord ++ tailWord_2037064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037064).length < 2 ^ (prefixWord ++ tailWord_2037064).sum := by decide
  have hdescent : baseEnd_2037064 < baseStart_2037064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037081 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 3]
def baseStart_2037081 : Nat := 118140960795 + 2037081 * 2 ^ 59
def prefixEnd_2037081 : Nat := 4983230072969 + 3 ^ 40 * 2037081 * 2
def baseEnd_2037081 : Nat := 1046001685141649644919141

theorem tailTrace_2037081 : CollatzResearch.WordTrace tailWord_2037081 prefixEnd_2037081 1046001685141649644919141 := by
  unfold tailWord_2037081
  simp only [CollatzResearch.WordTrace]
  refine ⟨74298447933010917581719097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49532298622007278387812731 74298447933010917581719097)
  ·
    refine ⟨55723835949758188186289323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74298447933010917581719097 55723835949758188186289323)
    ·
      refine ⟨83585753924637282279433985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55723835949758188186289323 83585753924637282279433985)
      ·
        refine ⟨62689315443477961709575489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83585753924637282279433985 62689315443477961709575489)
        ·
          refine ⟨47016986582608471282181617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62689315443477961709575489 47016986582608471282181617)
          ·
            refine ⟨35262739936956353461636213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47016986582608471282181617 35262739936956353461636213)
            ·
              refine ⟨3305881869089658137028395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35262739936956353461636213 3305881869089658137028395)
              ·
                refine ⟨4958822803634487205542593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3305881869089658137028395 4958822803634487205542593)
                ·
                  refine ⟨3719117102725865404156945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4958822803634487205542593 3719117102725865404156945)
                  ·
                    refine ⟨2789337827044399053117709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3719117102725865404156945 2789337827044399053117709)
                    ·
                      refine ⟨1046001685141649644919141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2789337827044399053117709 1046001685141649644919141)
                      ·
                        rfl

theorem cell23_2037081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_2037081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037081 prefixEnd_2037081 := by exact prefixLift 2037081
  have htrace : WordTrace (prefixWord ++ tailWord_2037081) baseStart_2037081 baseEnd_2037081 := by
    simpa [prefixWord, tailWord_2037081, baseEnd_2037081] using wordTrace_append hprefix tailTrace_2037081
  have hstable : (prefixWord ++ tailWord_2037081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037081).length < 2 ^ (prefixWord ++ tailWord_2037081).sum := by decide
  have hdescent : baseEnd_2037081 < baseStart_2037081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037088 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 1, 4]
def baseStart_2037088 : Nat := 118140960795 + 2037088 * 2 ^ 59
def prefixEnd_2037088 : Nat := 4983230072969 + 3 ^ 40 * 2037088 * 2
def baseEnd_2037088 : Nat := 348668426502077039177203

theorem tailTrace_2037088 : CollatzResearch.WordTrace tailWord_2037088 prefixEnd_2037088 348668426502077039177203 := by
  unfold tailWord_2037088
  simp only [CollatzResearch.WordTrace]
  refine ⟨37149351621992778888611959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49532468829323705184815945 37149351621992778888611959)
  ·
    refine ⟨55724027432989168332917939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37149351621992778888611959 55724027432989168332917939)
    ·
      refine ⟨83586041149483752499376909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55724027432989168332917939 83586041149483752499376909)
      ·
        refine ⟨31344765431056407187266341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83586041149483752499376909 31344765431056407187266341)
        ·
          refine ⟨5877143518323076347612439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31344765431056407187266341 5877143518323076347612439)
          ·
            refine ⟨8815715277484614521418659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877143518323076347612439 8815715277484614521418659)
            ·
              refine ⟨13223572916226921782127989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8815715277484614521418659 13223572916226921782127989)
              ·
                refine ⟨1239709960896273917074499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13223572916226921782127989 1239709960896273917074499)
                ·
                  refine ⟨1859564941344410875611749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239709960896273917074499 1859564941344410875611749)
                  ·
                    refine ⟨348668426502077039177203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1859564941344410875611749 348668426502077039177203)
                    ·
                      rfl

theorem cell23_2037088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 1, 4].length) (baseStart_2037088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037088 prefixEnd_2037088 := by exact prefixLift 2037088
  have htrace : WordTrace (prefixWord ++ tailWord_2037088) baseStart_2037088 baseEnd_2037088 := by
    simpa [prefixWord, tailWord_2037088, baseEnd_2037088] using wordTrace_append hprefix tailTrace_2037088
  have hstable : (prefixWord ++ tailWord_2037088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037088).length < 2 ^ (prefixWord ++ tailWord_2037088).sum := by decide
  have hdescent : baseEnd_2037088 < baseStart_2037088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037101 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 6]
def baseStart_2037101 : Nat := 118140960795 + 2037101 * 2 ^ 59
def prefixEnd_2037101 : Nat := 4983230072969 + 3 ^ 40 * 2037101 * 2
def baseEnd_2037101 : Nat := 116223550528304396296561

theorem tailTrace_2037101 : CollatzResearch.WordTrace tailWord_2037101 prefixEnd_2037101 116223550528304396296561 := by
  unfold tailWord_2037101
  simp only [CollatzResearch.WordTrace]
  refine ⟨74299177392938460997447157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49532784928625640664964771 74299177392938460997447157)
  ·
    refine ⟨6965547880587980718510671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74299177392938460997447157 6965547880587980718510671)
    ·
      refine ⟨10448321820881971077766007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6965547880587980718510671 10448321820881971077766007)
      ·
        refine ⟨15672482731322956616649011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10448321820881971077766007 15672482731322956616649011)
        ·
          refine ⟨23508724096984434924973517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15672482731322956616649011 23508724096984434924973517)
          ·
            refine ⟨8815771536369163096865069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23508724096984434924973517 8815771536369163096865069)
            ·
              refine ⟨3305914326138436161324401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8815771536369163096865069 3305914326138436161324401)
              ·
                refine ⟨2479435744603827120993301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3305914326138436161324401 2479435744603827120993301)
                ·
                  refine ⟨116223550528304396296561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2479435744603827120993301 116223550528304396296561)
                  ·
                    rfl

theorem cell23_2037101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_2037101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037101 prefixEnd_2037101 := by exact prefixLift 2037101
  have htrace : WordTrace (prefixWord ++ tailWord_2037101) baseStart_2037101 baseEnd_2037101 := by
    simpa [prefixWord, tailWord_2037101, baseEnd_2037101] using wordTrace_append hprefix tailTrace_2037101
  have hstable : (prefixWord ++ tailWord_2037101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037101).length < 2 ^ (prefixWord ++ tailWord_2037101).sum := by decide
  have hdescent : baseEnd_2037101 < baseStart_2037101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037128 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2037128 : Nat := 118140960795 + 2037128 * 2 ^ 59
def prefixEnd_2037128 : Nat := 4983230072969 + 3 ^ 40 * 2037128 * 2
def baseEnd_2037128 : Nat := 1046025818732410961031425

theorem tailTrace_2037128 : CollatzResearch.WordTrace tailWord_2037128 prefixEnd_2037128 1046025818732410961031425 := by
  unfold tailWord_2037128
  simp only [CollatzResearch.WordTrace]
  refine ⟨37150081081920322304340019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49533441442560429739120025 37150081081920322304340019)
  ·
    refine ⟨55725121622880483456510029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37150081081920322304340019 55725121622880483456510029)
    ·
      refine ⟨20896920608580181296191261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55725121622880483456510029 20896920608580181296191261)
      ·
        refine ⟨7836345228217567986071723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20896920608580181296191261 7836345228217567986071723)
        ·
          refine ⟨11754517842326351979107585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836345228217567986071723 11754517842326351979107585)
          ·
            refine ⟨8815888381744763984330689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11754517842326351979107585 8815888381744763984330689)
            ·
              refine ⟨6611916286308572988248017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8815888381744763984330689 6611916286308572988248017)
              ·
                refine ⟨4958937214731429741186013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6611916286308572988248017 4958937214731429741186013)
                ·
                  refine ⟨1859601455524286152944755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4958937214731429741186013 1859601455524286152944755)
                  ·
                    refine ⟨2789402183286429229417133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1859601455524286152944755 2789402183286429229417133)
                    ·
                      refine ⟨1046025818732410961031425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2789402183286429229417133 1046025818732410961031425)
                      ·
                        rfl

theorem cell23_2037128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2037128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037128 prefixEnd_2037128 := by exact prefixLift 2037128
  have htrace : WordTrace (prefixWord ++ tailWord_2037128) baseStart_2037128 baseEnd_2037128 := by
    simpa [prefixWord, tailWord_2037128, baseEnd_2037128] using wordTrace_append hprefix tailTrace_2037128
  have hstable : (prefixWord ++ tailWord_2037128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037128).length < 2 ^ (prefixWord ++ tailWord_2037128).sum := by decide
  have hdescent : baseEnd_2037128 < baseStart_2037128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037131 : List Nat := [1, 1, 1, 1, 4, 3, 4, 2, 1, 5]
def baseStart_2037131 : Nat := 118140960795 + 2037131 * 2 ^ 59
def prefixEnd_2037131 : Nat := 4983230072969 + 3 ^ 40 * 2037131 * 2
def baseEnd_2037131 : Nat := 348675786391458149764637

theorem tailTrace_2037131 : CollatzResearch.WordTrace tailWord_2037131 prefixEnd_2037131 348675786391458149764637 := by
  unfold tailWord_2037131
  simp only [CollatzResearch.WordTrace]
  refine ⟨74300271582829776121039247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49533514388553184080692831 74300271582829776121039247)
  ·
    refine ⟨111450407374244664181558871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74300271582829776121039247 111450407374244664181558871)
    ·
      refine ⟨167175611061366996272338307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111450407374244664181558871 167175611061366996272338307)
      ·
        refine ⟨250763416592050494408507461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167175611061366996272338307 250763416592050494408507461)
        ·
          refine ⟨47018140611009467701595149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250763416592050494408507461 47018140611009467701595149)
          ·
            refine ⟨17631802729128550388098181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47018140611009467701595149 17631802729128550388098181)
            ·
              refine ⟨3305963011711603197768409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17631802729128550388098181 3305963011711603197768409)
              ·
                refine ⟨2479472258783702398326307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3305963011711603197768409 2479472258783702398326307)
                ·
                  refine ⟨3719208388175553597489461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479472258783702398326307 3719208388175553597489461)
                  ·
                    refine ⟨348675786391458149764637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3719208388175553597489461 348675786391458149764637)
                    ·
                      rfl

theorem cell23_2037131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 2, 1, 5].length) (baseStart_2037131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037131 prefixEnd_2037131 := by exact prefixLift 2037131
  have htrace : WordTrace (prefixWord ++ tailWord_2037131) baseStart_2037131 baseEnd_2037131 := by
    simpa [prefixWord, tailWord_2037131, baseEnd_2037131] using wordTrace_append hprefix tailTrace_2037131
  have hstable : (prefixWord ++ tailWord_2037131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037131).length < 2 ^ (prefixWord ++ tailWord_2037131).sum := by decide
  have hdescent : baseEnd_2037131 < baseStart_2037131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037145 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 1, 1, 3]
def baseStart_2037145 : Nat := 118140960795 + 2037145 * 2 ^ 59
def prefixEnd_2037145 : Nat := 4983230072969 + 3 ^ 40 * 2037145 * 2
def baseEnd_2037145 : Nat := 1046034547903537394518847

theorem tailTrace_2037145 : CollatzResearch.WordTrace tailWord_2037145 prefixEnd_2037145 1046034547903537394518847 := by
  unfold tailWord_2037145
  simp only [CollatzResearch.WordTrace]
  refine ⟨74300782204779056512048889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49533854803186037674699259 74300782204779056512048889)
  ·
    refine ⟨55725586653584292384036667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74300782204779056512048889 55725586653584292384036667)
    ·
      refine ⟨83588379980376438576055001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55725586653584292384036667 83588379980376438576055001)
      ·
        refine ⟨62691284985282328932041251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83588379980376438576055001 62691284985282328932041251)
        ·
          refine ⟨94036927477923493398061877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62691284985282328932041251 94036927477923493398061877)
          ·
            refine ⟨8815961951055327506068301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94036927477923493398061877 8815961951055327506068301)
            ·
              refine ⟨3305985731645747814775613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8815961951055327506068301 3305985731645747814775613)
              ·
                refine ⟨1239744649367155430540855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3305985731645747814775613 1239744649367155430540855)
                ·
                  refine ⟨1859616974050733145811283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239744649367155430540855 1859616974050733145811283)
                  ·
                    refine ⟨2789425461076099718716925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1859616974050733145811283 2789425461076099718716925)
                    ·
                      refine ⟨1046034547903537394518847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2789425461076099718716925 1046034547903537394518847)
                      ·
                        rfl

theorem cell23_2037145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 1, 3].length) (baseStart_2037145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037145 prefixEnd_2037145 := by exact prefixLift 2037145
  have htrace : WordTrace (prefixWord ++ tailWord_2037145) baseStart_2037145 baseEnd_2037145 := by
    simpa [prefixWord, tailWord_2037145, baseEnd_2037145] using wordTrace_append hprefix tailTrace_2037145
  have hstable : (prefixWord ++ tailWord_2037145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037145).length < 2 ^ (prefixWord ++ tailWord_2037145).sum := by decide
  have hdescent : baseEnd_2037145 < baseStart_2037145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037164 : List Nat := [2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_2037164 : Nat := 118140960795 + 2037164 * 2 ^ 59
def prefixEnd_2037164 : Nat := 4983230072969 + 3 ^ 40 * 2037164 * 2
def baseEnd_2037164 : Nat := 1046044304035972820181259

theorem tailTrace_2037164 : CollatzResearch.WordTrace tailWord_2037164 prefixEnd_2037164 1046044304035972820181259 := by
  unfold tailWord_2037164
  simp only [CollatzResearch.WordTrace]
  refine ⟨37150737595855111378495273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49534316794473481837993697 37150737595855111378495273)
  ·
    refine ⟨27863053196891333533871455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37150737595855111378495273 27863053196891333533871455)
    ·
      refine ⟨41794579795337000300807183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27863053196891333533871455 41794579795337000300807183)
      ·
        refine ⟨62691869693005500451210775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41794579795337000300807183 62691869693005500451210775)
        ·
          refine ⟨94037804539508250676816163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62691869693005500451210775 94037804539508250676816163)
          ·
            refine ⟨141056706809262376015224245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94037804539508250676816163 141056706809262376015224245)
            ·
              refine ⟨13224066263368347751427273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141056706809262376015224245 13224066263368347751427273)
              ·
                refine ⟨9918049697526260813570455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13224066263368347751427273 9918049697526260813570455)
                ·
                  refine ⟨14877074546289391220355683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918049697526260813570455 14877074546289391220355683)
                  ·
                    refine ⟨22315611819434086830533525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14877074546289391220355683 22315611819434086830533525)
                    ·
                      refine ⟨1046044304035972820181259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22315611819434086830533525 1046044304035972820181259)
                      ·
                        rfl

theorem cell23_2037164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_2037164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037164 prefixEnd_2037164 := by exact prefixLift 2037164
  have htrace : WordTrace (prefixWord ++ tailWord_2037164) baseStart_2037164 baseEnd_2037164 := by
    simpa [prefixWord, tailWord_2037164, baseEnd_2037164] using wordTrace_append hprefix tailTrace_2037164
  have hstable : (prefixWord ++ tailWord_2037164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037164).length < 2 ^ (prefixWord ++ tailWord_2037164).sum := by decide
  have hdescent : baseEnd_2037164 < baseStart_2037164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037168 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 3, 2, 2]
def baseStart_2037168 : Nat := 118140960795 + 2037168 * 2 ^ 59
def prefixEnd_2037168 : Nat := 4983230072969 + 3 ^ 40 * 2037168 * 2
def baseEnd_2037168 : Nat := 1046046357958590804531241

theorem tailTrace_2037168 : CollatzResearch.WordTrace tailWord_2037168 prefixEnd_2037168 1046046357958590804531241 := by
  unfold tailWord_2037168
  simp only [CollatzResearch.WordTrace]
  refine ⟨37150810541847865720068079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49534414055797154293424105 37150810541847865720068079)
  ·
    refine ⟨55726215812771798580102119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37150810541847865720068079 55726215812771798580102119)
    ·
      refine ⟨83589323719157697870153179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55726215812771798580102119 83589323719157697870153179)
      ·
        refine ⟨125383985578736546805229769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83589323719157697870153179 125383985578736546805229769)
        ·
          refine ⟨94037989184052410103922327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125383985578736546805229769 94037989184052410103922327)
          ·
            refine ⟨141056983776078615155883491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94037989184052410103922327 141056983776078615155883491)
            ·
              refine ⟨211585475664117922733825237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141056983776078615155883491 211585475664117922733825237)
              ·
                refine ⟨4959034585877763814074029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 211585475664117922733825237 4959034585877763814074029)
                ·
                  refine ⟨1859637969704161430277761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4959034585877763814074029 1859637969704161430277761)
                  ·
                    refine ⟨1394728477278121072708321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859637969704161430277761 1394728477278121072708321)
                    ·
                      refine ⟨1046046357958590804531241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394728477278121072708321 1046046357958590804531241)
                      ·
                        rfl

theorem cell23_2037168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3, 2, 2].length) (baseStart_2037168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037168 prefixEnd_2037168 := by exact prefixLift 2037168
  have htrace : WordTrace (prefixWord ++ tailWord_2037168) baseStart_2037168 baseEnd_2037168 := by
    simpa [prefixWord, tailWord_2037168, baseEnd_2037168] using wordTrace_append hprefix tailTrace_2037168
  have hstable : (prefixWord ++ tailWord_2037168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037168).length < 2 ^ (prefixWord ++ tailWord_2037168).sum := by decide
  have hdescent : baseEnd_2037168 < baseStart_2037168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037181 : List Nat := [1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 4]
def baseStart_2037181 : Nat := 118140960795 + 2037181 * 2 ^ 59
def prefixEnd_2037181 : Nat := 4983230072969 + 3 ^ 40 * 2037181 * 2
def baseEnd_2037181 : Nat := 1046053033207099253668681

theorem tailTrace_2037181 : CollatzResearch.WordTrace tailWord_2037181 prefixEnd_2037181 1046053033207099253668681 := by
  unfold tailWord_2037181
  simp only [CollatzResearch.WordTrace]
  refine ⟨74302095232648634660359397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49534730155099089773572931 74302095232648634660359397)
  ·
    refine ⟨13931642856121618998817387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74302095232648634660359397 13931642856121618998817387)
    ·
      refine ⟨20897464284182428498226081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13931642856121618998817387 20897464284182428498226081)
      ·
        refine ⟨15673098213136821373669561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20897464284182428498226081 15673098213136821373669561)
        ·
          refine ⟨11754823659852616030252171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15673098213136821373669561 11754823659852616030252171)
          ·
            refine ⟨17632235489778924045378257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11754823659852616030252171 17632235489778924045378257)
            ·
              refine ⟨13224176617334193034033693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17632235489778924045378257 13224176617334193034033693)
              ·
                refine ⟨4959066231500322387762635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13224176617334193034033693 4959066231500322387762635)
                ·
                  refine ⟨7438599347250483581643953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959066231500322387762635 7438599347250483581643953)
                  ·
                    refine ⟨5578949510437862686232965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7438599347250483581643953 5578949510437862686232965)
                    ·
                      refine ⟨1046053033207099253668681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5578949510437862686232965 1046053033207099253668681)
                      ·
                        rfl

theorem cell23_2037181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_2037181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037181 prefixEnd_2037181 := by exact prefixLift 2037181
  have htrace : WordTrace (prefixWord ++ tailWord_2037181) baseStart_2037181 baseEnd_2037181 := by
    simpa [prefixWord, tailWord_2037181, baseEnd_2037181] using wordTrace_append hprefix tailTrace_2037181
  have hstable : (prefixWord ++ tailWord_2037181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037181).length < 2 ^ (prefixWord ++ tailWord_2037181).sum := by decide
  have hdescent : baseEnd_2037181 < baseStart_2037181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037205 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_2037205 : Nat := 118140960795 + 2037205 * 2 ^ 59
def prefixEnd_2037205 : Nat := 4983230072969 + 3 ^ 40 * 2037205 * 2
def baseEnd_2037205 : Nat := 1046065356742807159768571

theorem tailTrace_2037205 : CollatzResearch.WordTrace tailWord_2037205 prefixEnd_2037205 1046065356742807159768571 := by
  unfold tailWord_2037205
  simp only [CollatzResearch.WordTrace]
  refine ⟨74302970584561686759233069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49535313723041124506155379 74302970584561686759233069)
  ·
    refine ⟨27863613969210632534712401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74302970584561686759233069 27863613969210632534712401)
    ·
      refine ⟨20897710476907974401034301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27863613969210632534712401 20897710476907974401034301)
      ·
        refine ⟨7836641428840490400387863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20897710476907974401034301 7836641428840490400387863)
        ·
          refine ⟨11754962143260735600581795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7836641428840490400387863 11754962143260735600581795)
          ·
            refine ⟨17632443214891103400872693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11754962143260735600581795 17632443214891103400872693)
            ·
              refine ⟨1653041551396040943831815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17632443214891103400872693 1653041551396040943831815)
              ·
                refine ⟨2479562327094061415747723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653041551396040943831815 2479562327094061415747723)
                ·
                  refine ⟨3719343490641092123621585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479562327094061415747723 3719343490641092123621585)
                  ·
                    refine ⟨2789507617980819092716189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3719343490641092123621585 2789507617980819092716189)
                    ·
                      refine ⟨1046065356742807159768571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2789507617980819092716189 1046065356742807159768571)
                      ·
                        rfl

theorem cell23_2037205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_2037205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037205 prefixEnd_2037205 := by exact prefixLift 2037205
  have htrace : WordTrace (prefixWord ++ tailWord_2037205) baseStart_2037205 baseEnd_2037205 := by
    simpa [prefixWord, tailWord_2037205, baseEnd_2037205] using wordTrace_append hprefix tailTrace_2037205
  have hstable : (prefixWord ++ tailWord_2037205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037205).length < 2 ^ (prefixWord ++ tailWord_2037205).sum := by decide
  have hdescent : baseEnd_2037205 < baseStart_2037205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037219 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 1, 2, 2]
def baseStart_2037219 : Nat := 118140960795 + 2037219 * 2 ^ 59
def prefixEnd_2037219 : Nat := 4983230072969 + 3 ^ 40 * 2037219 * 2
def baseEnd_2037219 : Nat := 1046072545471970104993507

theorem tailTrace_2037219 : CollatzResearch.WordTrace tailWord_2037219 prefixEnd_2037219 1046072545471970104993507 := by
  unfold tailWord_2037219
  simp only [CollatzResearch.WordTrace]
  refine ⟨74303481206510967150242711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49535654137673978100161807 74303481206510967150242711)
  ·
    refine ⟨111455221809766450725364067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74303481206510967150242711 111455221809766450725364067)
    ·
      refine ⟨167182832714649676088046101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111455221809766450725364067 167182832714649676088046101)
      ·
        refine ⟨7836695283499203566627161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 167182832714649676088046101 7836695283499203566627161)
        ·
          refine ⟨5877521462624402674970371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7836695283499203566627161 5877521462624402674970371)
          ·
            refine ⟨8816282193936604012455557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877521462624402674970371 8816282193936604012455557)
            ·
              refine ⟨1653052911363113252335417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8816282193936604012455557 1653052911363113252335417)
              ·
                refine ⟨1239789683522334939251563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653052911363113252335417 1239789683522334939251563)
                ·
                  refine ⟨1859684525283502408877345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1239789683522334939251563 1859684525283502408877345)
                  ·
                    refine ⟨1394763393962626806658009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859684525283502408877345 1394763393962626806658009)
                    ·
                      refine ⟨1046072545471970104993507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394763393962626806658009 1046072545471970104993507)
                      ·
                        rfl

theorem cell23_2037219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_2037219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037219 prefixEnd_2037219 := by exact prefixLift 2037219
  have htrace : WordTrace (prefixWord ++ tailWord_2037219) baseStart_2037219 baseEnd_2037219 := by
    simpa [prefixWord, tailWord_2037219, baseEnd_2037219] using wordTrace_append hprefix tailTrace_2037219
  have hstable : (prefixWord ++ tailWord_2037219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037219).length < 2 ^ (prefixWord ++ tailWord_2037219).sum := by decide
  have hdescent : baseEnd_2037219 < baseStart_2037219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037221 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 2, 7]
def baseStart_2037221 : Nat := 118140960795 + 2037221 * 2 ^ 59
def prefixEnd_2037221 : Nat := 4983230072969 + 3 ^ 40 * 2037221 * 2
def baseEnd_2037221 : Nat := 348691190811093032389499

theorem tailTrace_2037221 : CollatzResearch.WordTrace tailWord_2037221 prefixEnd_2037221 348691190811093032389499 := by
  unfold tailWord_2037221
  simp only [CollatzResearch.WordTrace]
  refine ⟨74303554152503721491815517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49535702768335814327877011 74303554152503721491815517)
  ·
    refine ⟨27863832807188895559430819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74303554152503721491815517 27863832807188895559430819)
    ·
      refine ⟨41795749210783343339146229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27863832807188895559430819 41795749210783343339146229)
      ·
        refine ⟨3918351488510938438044959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41795749210783343339146229 3918351488510938438044959)
        ·
          refine ⟨5877527232766407657067439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918351488510938438044959 5877527232766407657067439)
          ·
            refine ⟨8816290849149611485601159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877527232766407657067439 8816290849149611485601159)
            ·
              refine ⟨13224436273724417228401739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816290849149611485601159 13224436273724417228401739)
              ·
                refine ⟨19836654410586625842602609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13224436273724417228401739 19836654410586625842602609)
                ·
                  refine ⟨14877490807939969381951957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19836654410586625842602609 14877490807939969381951957)
                  ·
                    refine ⟨348691190811093032389499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14877490807939969381951957 348691190811093032389499)
                    ·
                      rfl

theorem cell23_2037221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_2037221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037221 prefixEnd_2037221 := by exact prefixLift 2037221
  have htrace : WordTrace (prefixWord ++ tailWord_2037221) baseStart_2037221 baseEnd_2037221 := by
    simpa [prefixWord, tailWord_2037221, baseEnd_2037221] using wordTrace_append hprefix tailTrace_2037221
  have hstable : (prefixWord ++ tailWord_2037221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037221).length < 2 ^ (prefixWord ++ tailWord_2037221).sum := by decide
  have hdescent : baseEnd_2037221 < baseStart_2037221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037262 : List Nat := [4, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2]
def baseStart_2037262 : Nat := 118140960795 + 2037262 * 2 ^ 59
def prefixEnd_2037262 : Nat := 4983230072969 + 3 ^ 40 * 2037262 * 2
def baseEnd_2037262 : Nat := 1046094625140113436755809

theorem tailTrace_2037262 : CollatzResearch.WordTrace tailWord_2037262 prefixEnd_2037262 1046094625140113436755809 := by
  unfold tailWord_2037262
  simp only [CollatzResearch.WordTrace]
  refine ⟨9288131193169398186757255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49536699696903456996038693 9288131193169398186757255)
  ·
    refine ⟨13932196789754097280135883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9288131193169398186757255 13932196789754097280135883)
    ·
      refine ⟨20898295184631145920203825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13932196789754097280135883 20898295184631145920203825)
      ·
        refine ⟨15673721388473359440152869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20898295184631145920203825 15673721388473359440152869)
        ·
          refine ⟨2938822760338754895028663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15673721388473359440152869 2938822760338754895028663)
          ·
            refine ⟨4408234140508132342542995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938822760338754895028663 4408234140508132342542995)
            ·
              refine ⟨6612351210762198513814493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408234140508132342542995 6612351210762198513814493)
              ·
                refine ⟨2479631704035824442680435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6612351210762198513814493 2479631704035824442680435)
                ·
                  refine ⟨3719447556053736664020653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479631704035824442680435 3719447556053736664020653)
                  ·
                    refine ⟨1394792833520151249007745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719447556053736664020653 1394792833520151249007745)
                    ·
                      refine ⟨1046094625140113436755809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394792833520151249007745 1046094625140113436755809)
                      ·
                        rfl

theorem cell23_2037262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_2037262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037262 prefixEnd_2037262 := by exact prefixLift 2037262
  have htrace : WordTrace (prefixWord ++ tailWord_2037262) baseStart_2037262 baseEnd_2037262 := by
    simpa [prefixWord, tailWord_2037262, baseEnd_2037262] using wordTrace_append hprefix tailTrace_2037262
  have hstable : (prefixWord ++ tailWord_2037262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037262).length < 2 ^ (prefixWord ++ tailWord_2037262).sum := by decide
  have hdescent : baseEnd_2037262 < baseStart_2037262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037281 : List Nat := [1, 2, 3, 2, 2, 2, 1, 3, 7]
def baseStart_2037281 : Nat := 118140960795 + 2037281 * 2 ^ 59
def prefixEnd_2037281 : Nat := 4983230072969 + 3 ^ 40 * 2037281 * 2
def baseEnd_2037281 : Nat := 116233820141394318046469

theorem tailTrace_2037281 : CollatzResearch.WordTrace tailWord_2037281 prefixEnd_2037281 116233820141394318046469 := by
  unfold tailWord_2037281
  simp only [CollatzResearch.WordTrace]
  refine ⟨74305742532286351738999697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49537161688190901159333131 74305742532286351738999697)
  ·
    refine ⟨55729306899214763804249773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74305742532286351738999697 55729306899214763804249773)
    ·
      refine ⟨20898490087205536426593665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55729306899214763804249773 20898490087205536426593665)
      ·
        refine ⟨15673867565404152319945249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20898490087205536426593665 15673867565404152319945249)
        ·
          refine ⟨11755400674053114239958937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15673867565404152319945249 11755400674053114239958937)
          ·
            refine ⟨8816550505539835679969203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11755400674053114239958937 8816550505539835679969203)
            ·
              refine ⟨13224825758309753519953805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816550505539835679969203 13224825758309753519953805)
              ·
                refine ⟨4959309659366157569982677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13224825758309753519953805 4959309659366157569982677)
                ·
                  refine ⟨116233820141394318046469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4959309659366157569982677 116233820141394318046469)
                  ·
                    rfl

theorem cell23_2037281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 3, 7].length) (baseStart_2037281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037281 prefixEnd_2037281 := by exact prefixLift 2037281
  have htrace : WordTrace (prefixWord ++ tailWord_2037281) baseStart_2037281 baseEnd_2037281 := by
    simpa [prefixWord, tailWord_2037281, baseEnd_2037281] using wordTrace_append hprefix tailTrace_2037281
  have hstable : (prefixWord ++ tailWord_2037281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037281).length < 2 ^ (prefixWord ++ tailWord_2037281).sum := by decide
  have hdescent : baseEnd_2037281 < baseStart_2037281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037311 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 1, 7]
def baseStart_2037311 : Nat := 118140960795 + 2037311 * 2 ^ 59
def prefixEnd_2037311 : Nat := 4983230072969 + 3 ^ 40 * 2037311 * 2
def baseEnd_2037311 : Nat := 348706595230727915014361

theorem tailTrace_2037311 : CollatzResearch.WordTrace tailWord_2037311 prefixEnd_2037311 348706595230727915014361 := by
  unfold tailWord_2037311
  simp only [CollatzResearch.WordTrace]
  refine ⟨74306836722177666862591787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49537891148118444575061191 74306836722177666862591787)
  ·
    refine ⟨111460255083266500293887681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74306836722177666862591787 111460255083266500293887681)
    ·
      refine ⟨83595191312449875220415761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111460255083266500293887681 83595191312449875220415761)
      ·
        refine ⟨62696393484337406415311821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83595191312449875220415761 62696393484337406415311821)
        ·
          refine ⟨23511147556626527405741933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62696393484337406415311821 23511147556626527405741933)
          ·
            refine ⟨8816680333734947777153225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23511147556626527405741933 8816680333734947777153225)
            ·
              refine ⟨6612510250301210832864919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816680333734947777153225 6612510250301210832864919)
              ·
                refine ⟨9918765375451816249297379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612510250301210832864919 9918765375451816249297379)
                ·
                  refine ⟨14878148063177724373946069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918765375451816249297379 14878148063177724373946069)
                  ·
                    refine ⟨348706595230727915014361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14878148063177724373946069 348706595230727915014361)
                    ·
                      rfl

theorem cell23_2037311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 1, 7].length) (baseStart_2037311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037311 prefixEnd_2037311 := by exact prefixLift 2037311
  have htrace : WordTrace (prefixWord ++ tailWord_2037311) baseStart_2037311 baseEnd_2037311 := by
    simpa [prefixWord, tailWord_2037311, baseEnd_2037311] using wordTrace_append hprefix tailTrace_2037311
  have hstable : (prefixWord ++ tailWord_2037311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037311).length < 2 ^ (prefixWord ++ tailWord_2037311).sum := by decide
  have hdescent : baseEnd_2037311 < baseStart_2037311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037361 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 4]
def baseStart_2037361 : Nat := 118140960795 + 2037361 * 2 ^ 59
def prefixEnd_2037361 : Nat := 4983230072969 + 3 ^ 40 * 2037361 * 2
def baseEnd_2037361 : Nat := 1046145459724908549417853

theorem tailTrace_2037361 : CollatzResearch.WordTrace tailWord_2037361 prefixEnd_2037361 1046145459724908549417853 := by
  unfold tailWord_2037361
  simp only [CollatzResearch.WordTrace]
  refine ⟨74308660371996525401911937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49539106914664350267941291 74308660371996525401911937)
  ·
    refine ⟨55731495278997394051433953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74308660371996525401911937 55731495278997394051433953)
    ·
      refine ⟨41798621459248045538575465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55731495278997394051433953 41798621459248045538575465)
      ·
        refine ⟨31348966094436034153931599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41798621459248045538575465 31348966094436034153931599)
        ·
          refine ⟨47023449141654051230897399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31348966094436034153931599 47023449141654051230897399)
          ·
            refine ⟨70535173712481076846346099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47023449141654051230897399 70535173712481076846346099)
            ·
              refine ⟨105802760568721615269519149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70535173712481076846346099 105802760568721615269519149)
              ·
                refine ⟨39676035213270605726069681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105802760568721615269519149 39676035213270605726069681)
                ·
                  refine ⟨29757026409952954294552261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39676035213270605726069681 29757026409952954294552261)
                  ·
                    refine ⟨5579442451866178930228549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29757026409952954294552261 5579442451866178930228549)
                    ·
                      refine ⟨1046145459724908549417853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5579442451866178930228549 1046145459724908549417853)
                      ·
                        rfl

theorem cell23_2037361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_2037361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037361 prefixEnd_2037361 := by exact prefixLift 2037361
  have htrace : WordTrace (prefixWord ++ tailWord_2037361) baseStart_2037361 baseEnd_2037361 := by
    simpa [prefixWord, tailWord_2037361, baseEnd_2037361] using wordTrace_append hprefix tailTrace_2037361
  have hstable : (prefixWord ++ tailWord_2037361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037361).length < 2 ^ (prefixWord ++ tailWord_2037361).sum := by decide
  have hdescent : baseEnd_2037361 < baseStart_2037361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037365 : List Nat := [1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_2037365 : Nat := 118140960795 + 2037365 * 2 ^ 59
def prefixEnd_2037365 : Nat := 4983230072969 + 3 ^ 40 * 2037365 * 2
def baseEnd_2037365 : Nat := 1046147513647526533767835

theorem tailTrace_2037365 : CollatzResearch.WordTrace tailWord_2037365 prefixEnd_2037365 1046147513647526533767835 := by
  unfold tailWord_2037365
  simp only [CollatzResearch.WordTrace]
  refine ⟨74308806263982034085057549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49539204175988022723371699 74308806263982034085057549)
  ·
    refine ⟨27865802348993262781896581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74308806263982034085057549 27865802348993262781896581)
    ·
      refine ⟨5224837940436236771605609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27865802348993262781896581 5224837940436236771605609)
      ·
        refine ⟨3918628455327177578704207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5224837940436236771605609 3918628455327177578704207)
        ·
          refine ⟨5877942682990766368056311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3918628455327177578704207 5877942682990766368056311)
          ·
            refine ⟨8816914024486149552084467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877942682990766368056311 8816914024486149552084467)
            ·
              refine ⟨13225371036729224328126701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816914024486149552084467 13225371036729224328126701)
              ·
                refine ⟨4959514138773459123047513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13225371036729224328126701 4959514138773459123047513)
                ·
                  refine ⟨3719635604080094342285635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4959514138773459123047513 3719635604080094342285635)
                  ·
                    refine ⟨5579453406120141513428453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3719635604080094342285635 5579453406120141513428453)
                    ·
                      refine ⟨1046147513647526533767835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5579453406120141513428453 1046147513647526533767835)
                      ·
                        rfl

theorem cell23_2037365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_2037365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037365 prefixEnd_2037365 := by exact prefixLift 2037365
  have htrace : WordTrace (prefixWord ++ tailWord_2037365) baseStart_2037365 baseEnd_2037365 := by
    simpa [prefixWord, tailWord_2037365, baseEnd_2037365] using wordTrace_append hprefix tailTrace_2037365
  have hstable : (prefixWord ++ tailWord_2037365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037365).length < 2 ^ (prefixWord ++ tailWord_2037365).sum := by decide
  have hdescent : baseEnd_2037365 < baseStart_2037365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037388 : List Nat := [2, 2, 1, 2, 1, 1, 6, 2, 6]
def baseStart_2037388 : Nat := 118140960795 + 2037388 * 2 ^ 59
def prefixEnd_2037388 : Nat := 4983230072969 + 3 ^ 40 * 2037388 * 2
def baseEnd_2037388 : Nat := 116239924855842215975581

theorem tailTrace_2037388 : CollatzResearch.WordTrace tailWord_2037388 prefixEnd_2037388 116239924855842215975581 := by
  unfold tailWord_2037388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37154822571449354506572409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49539763428599139342096545 37154822571449354506572409)
  ·
    refine ⟨27866116928587015879929307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37154822571449354506572409 27866116928587015879929307)
    ·
      refine ⟨41799175392880523819893961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27866116928587015879929307 41799175392880523819893961)
      ·
        refine ⟨31349381544660392864920471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41799175392880523819893961 31349381544660392864920471)
        ·
          refine ⟨47024072316990589297380707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31349381544660392864920471 47024072316990589297380707)
          ·
            refine ⟨70536108475485883946071061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47024072316990589297380707 70536108475485883946071061)
            ·
              refine ⟨3306380084788400809972081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70536108475485883946071061 3306380084788400809972081)
              ·
                refine ⟨2479785063591300607479061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306380084788400809972081 2479785063591300607479061)
                ·
                  refine ⟨116239924855842215975581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2479785063591300607479061 116239924855842215975581)
                  ·
                    rfl

theorem cell23_2037388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_2037388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037388 prefixEnd_2037388 := by exact prefixLift 2037388
  have htrace : WordTrace (prefixWord ++ tailWord_2037388) baseStart_2037388 baseEnd_2037388 := by
    simpa [prefixWord, tailWord_2037388, baseEnd_2037388] using wordTrace_append hprefix tailTrace_2037388
  have hstable : (prefixWord ++ tailWord_2037388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037388).length < 2 ^ (prefixWord ++ tailWord_2037388).sum := by decide
  have hdescent : baseEnd_2037388 < baseStart_2037388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037411 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2037411 : Nat := 118140960795 + 2037411 * 2 ^ 59
def prefixEnd_2037411 : Nat := 4983230072969 + 3 ^ 40 * 2037411 * 2
def baseEnd_2037411 : Nat := 1046171133757633353792623

theorem tailTrace_2037411 : CollatzResearch.WordTrace tailWord_2037411 prefixEnd_2037411 1046171133757633353792623 := by
  unfold tailWord_2037411
  simp only [CollatzResearch.WordTrace]
  refine ⟨74310484021815383941232087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49540322681210255960821391 74310484021815383941232087)
  ·
    refine ⟨111465726032723075911848131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74310484021815383941232087 111465726032723075911848131)
    ·
      refine ⟨167198589049084613867772197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111465726032723075911848131 167198589049084613867772197)
      ·
        refine ⟨31349735446703365100207287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167198589049084613867772197 31349735446703365100207287)
        ·
          refine ⟨47024603170055047650310931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31349735446703365100207287 47024603170055047650310931)
          ·
            refine ⟨70536904755082571475466397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47024603170055047650310931 70536904755082571475466397)
            ·
              refine ⟨26451339283155964303299899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70536904755082571475466397 26451339283155964303299899)
              ·
                refine ⟨39677008924733946454949849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26451339283155964303299899 39677008924733946454949849)
                ·
                  refine ⟨29757756693550459841212387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39677008924733946454949849 29757756693550459841212387)
                  ·
                    refine ⟨44636635040325689761818581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29757756693550459841212387 44636635040325689761818581)
                    ·
                      refine ⟨1046171133757633353792623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44636635040325689761818581 1046171133757633353792623)
                      ·
                        rfl

theorem cell23_2037411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2037411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037411 prefixEnd_2037411 := by exact prefixLift 2037411
  have htrace : WordTrace (prefixWord ++ tailWord_2037411) baseStart_2037411 baseEnd_2037411 := by
    simpa [prefixWord, tailWord_2037411, baseEnd_2037411] using wordTrace_append hprefix tailTrace_2037411
  have hstable : (prefixWord ++ tailWord_2037411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037411).length < 2 ^ (prefixWord ++ tailWord_2037411).sum := by decide
  have hdescent : baseEnd_2037411 < baseStart_2037411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037416 : List Nat := [2, 1, 7, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2037416 : Nat := 118140960795 + 2037416 * 2 ^ 59
def prefixEnd_2037416 : Nat := 4983230072969 + 3 ^ 40 * 2037416 * 2
def baseEnd_2037416 : Nat := 1046173701160905834230101

theorem tailTrace_2037416 : CollatzResearch.WordTrace tailWord_2037416 prefixEnd_2037416 1046173701160905834230101 := by
  unfold tailWord_2037416
  simp only [CollatzResearch.WordTrace]
  refine ⟨37155333193398634897582051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49540444257864846530109401 37155333193398634897582051)
  ·
    refine ⟨55732999790097952346373077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37155333193398634897582051 55732999790097952346373077)
    ·
      refine ⟨1306242182580420758118119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 55732999790097952346373077 1306242182580420758118119)
      ·
        refine ⟨1959363273870631137177179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306242182580420758118119 1959363273870631137177179)
        ·
          refine ⟨2939044910805946705765769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959363273870631137177179 2939044910805946705765769)
          ·
            refine ⟨2204283683104460029324327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2939044910805946705765769 2204283683104460029324327)
            ·
              refine ⟨3306425524656690043986491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204283683104460029324327 3306425524656690043986491)
              ·
                refine ⟨4959638286985035065979737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306425524656690043986491 4959638286985035065979737)
                ·
                  refine ⟨3719728715238776299484803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4959638286985035065979737 3719728715238776299484803)
                  ·
                    refine ⟨5579593072858164449227205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3719728715238776299484803 5579593072858164449227205)
                    ·
                      refine ⟨1046173701160905834230101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5579593072858164449227205 1046173701160905834230101)
                      ·
                        rfl

theorem cell23_2037416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2037416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037416 prefixEnd_2037416 := by exact prefixLift 2037416
  have htrace : WordTrace (prefixWord ++ tailWord_2037416) baseStart_2037416 baseEnd_2037416 := by
    simpa [prefixWord, tailWord_2037416, baseEnd_2037416] using wordTrace_append hprefix tailTrace_2037416
  have hstable : (prefixWord ++ tailWord_2037416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037416).length < 2 ^ (prefixWord ++ tailWord_2037416).sum := by decide
  have hdescent : baseEnd_2037416 < baseStart_2037416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037465 : List Nat := [1, 2, 1, 2, 3, 5, 1, 1, 1, 6]
def baseStart_2037465 : Nat := 118140960795 + 2037465 * 2 ^ 59
def prefixEnd_2037465 : Nat := 4983230072969 + 3 ^ 40 * 2037465 * 2
def baseEnd_2037465 : Nat := 348732953904325380839125

theorem tailTrace_2037465 : CollatzResearch.WordTrace tailWord_2037465 prefixEnd_2037465 348732953904325380839125 := by
  unfold tailWord_2037465
  simp only [CollatzResearch.WordTrace]
  refine ⟨74312453563619751163697849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49541635709079834109131899 74312453563619751163697849)
  ·
    refine ⟨55734340172714813372773387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74312453563619751163697849 55734340172714813372773387)
    ·
      refine ⟨83601510259072220059160081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55734340172714813372773387 83601510259072220059160081)
      ·
        refine ⟨62701132694304165044370061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83601510259072220059160081 62701132694304165044370061)
        ·
          refine ⟨23512924760364061891638773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62701132694304165044370061 23512924760364061891638773)
          ·
            refine ⟨2204336696284130802341135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23512924760364061891638773 2204336696284130802341135)
            ·
              refine ⟨3306505044426196203511703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204336696284130802341135 3306505044426196203511703)
              ·
                refine ⟨4959757566639294305267555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3306505044426196203511703 4959757566639294305267555)
                ·
                  refine ⟨7439636349958941457901333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959757566639294305267555 7439636349958941457901333)
                  ·
                    refine ⟨348732953904325380839125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7439636349958941457901333 348732953904325380839125)
                    ·
                      rfl

theorem cell23_2037465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 1, 6].length) (baseStart_2037465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037465 prefixEnd_2037465 := by exact prefixLift 2037465
  have htrace : WordTrace (prefixWord ++ tailWord_2037465) baseStart_2037465 baseEnd_2037465 := by
    simpa [prefixWord, tailWord_2037465, baseEnd_2037465] using wordTrace_append hprefix tailTrace_2037465
  have hstable : (prefixWord ++ tailWord_2037465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037465).length < 2 ^ (prefixWord ++ tailWord_2037465).sum := by decide
  have hdescent : baseEnd_2037465 < baseStart_2037465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037469 : List Nat := [1, 4, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_2037469 : Nat := 118140960795 + 2037469 * 2 ^ 59
def prefixEnd_2037469 : Nat := 4983230072969 + 3 ^ 40 * 2037469 * 2
def baseEnd_2037469 : Nat := 348733638545198042289119

theorem tailTrace_2037469 : CollatzResearch.WordTrace tailWord_2037469 prefixEnd_2037469 348733638545198042289119 := by
  unfold tailWord_2037469
  simp only [CollatzResearch.WordTrace]
  refine ⟨74312599455605259846843461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49541732970403506564562307 74312599455605259846843461)
  ·
    refine ⟨13933612397925986221283149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74312599455605259846843461 13933612397925986221283149)
    ·
      refine ⟨5225104649222244832981181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13933612397925986221283149 5225104649222244832981181)
      ·
        refine ⟨1959414243458341812367943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5225104649222244832981181 1959414243458341812367943)
        ·
          refine ⟨2939121365187512718551915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1959414243458341812367943 2939121365187512718551915)
          ·
            refine ⟨4408682047781269077827873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939121365187512718551915 4408682047781269077827873)
            ·
              refine ⟨3306511535835951808370905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408682047781269077827873 3306511535835951808370905)
              ·
                refine ⟨2479883651876963856278179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306511535835951808370905 2479883651876963856278179)
                ·
                  refine ⟨3719825477815445784417269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479883651876963856278179 3719825477815445784417269)
                  ·
                    refine ⟨348733638545198042289119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3719825477815445784417269 348733638545198042289119)
                    ·
                      rfl

theorem cell23_2037469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_2037469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037469 prefixEnd_2037469 := by exact prefixLift 2037469
  have htrace : WordTrace (prefixWord ++ tailWord_2037469) baseStart_2037469 baseEnd_2037469 := by
    simpa [prefixWord, tailWord_2037469, baseEnd_2037469] using wordTrace_append hprefix tailTrace_2037469
  have hstable : (prefixWord ++ tailWord_2037469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037469).length < 2 ^ (prefixWord ++ tailWord_2037469).sum := by decide
  have hdescent : baseEnd_2037469 < baseStart_2037469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037472 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 3, 2, 2]
def baseStart_2037472 : Nat := 118140960795 + 2037472 * 2 ^ 59
def prefixEnd_2037472 : Nat := 4983230072969 + 3 ^ 40 * 2037472 * 2
def baseEnd_2037472 : Nat := 1046202456077557615129843

theorem tailTrace_2037472 : CollatzResearch.WordTrace tailWord_2037472 prefixEnd_2037472 1046202456077557615129843 := by
  unfold tailWord_2037472
  simp only [CollatzResearch.WordTrace]
  refine ⟨37156354437297195679601335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49541805916396260906135113 37156354437297195679601335)
  ·
    refine ⟨55734531655945793519402003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37156354437297195679601335 55734531655945793519402003)
    ·
      refine ⟨83601797483918690279103005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55734531655945793519402003 83601797483918690279103005)
      ·
        refine ⟨31350674056469508854663627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83601797483918690279103005 31350674056469508854663627)
        ·
          refine ⟨47026011084704263281995441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31350674056469508854663627 47026011084704263281995441)
          ·
            refine ⟨35269508313528197461496581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47026011084704263281995441 35269508313528197461496581)
            ·
              refine ⟨6613032808786537024030609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35269508313528197461496581 6613032808786537024030609)
              ·
                refine ⟨4959774606589902768022957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6613032808786537024030609 4959774606589902768022957)
                ·
                  refine ⟨1859915477471213538008609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4959774606589902768022957 1859915477471213538008609)
                  ·
                    refine ⟨1394936608103410153506457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1859915477471213538008609 1394936608103410153506457)
                    ·
                      refine ⟨1046202456077557615129843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394936608103410153506457 1046202456077557615129843)
                      ·
                        rfl

theorem cell23_2037472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 3, 2, 2].length) (baseStart_2037472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037472 prefixEnd_2037472 := by exact prefixLift 2037472
  have htrace : WordTrace (prefixWord ++ tailWord_2037472) baseStart_2037472 baseEnd_2037472 := by
    simpa [prefixWord, tailWord_2037472, baseEnd_2037472] using wordTrace_append hprefix tailTrace_2037472
  have hstable : (prefixWord ++ tailWord_2037472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037472).length < 2 ^ (prefixWord ++ tailWord_2037472).sum := by decide
  have hdescent : baseEnd_2037472 < baseStart_2037472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037532 : List Nat := [2, 2, 3, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_2037532 : Nat := 118140960795 + 2037532 * 2 ^ 59
def prefixEnd_2037532 : Nat := 4983230072969 + 3 ^ 40 * 2037532 * 2
def baseEnd_2037532 : Nat := 1046233264916827380379567

theorem tailTrace_2037532 : CollatzResearch.WordTrace tailWord_2037532 prefixEnd_2037532 1046233264916827380379567 := by
  unfold tailWord_2037532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37157448627188510803193425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49543264836251347737591233 37157448627188510803193425)
  ·
    refine ⟨27868086470391383102395069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37157448627188510803193425 27868086470391383102395069)
    ·
      refine ⟨10450532426396768663398151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27868086470391383102395069 10450532426396768663398151)
      ·
        refine ⟨15675798639595152995097227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450532426396768663398151 15675798639595152995097227)
        ·
          refine ⟨23513697959392729492645841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15675798639595152995097227 23513697959392729492645841)
          ·
            refine ⟨17635273469544547119484381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23513697959392729492645841 17635273469544547119484381)
            ·
              refine ⟨6613227551079205169806643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17635273469544547119484381 6613227551079205169806643)
              ·
                refine ⟨9919841326618807754709965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613227551079205169806643 9919841326618807754709965)
                ·
                  refine ⟨3719940497482052908016237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9919841326618807754709965 3719940497482052908016237)
                  ·
                    refine ⟨1394977686555769840506089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3719940497482052908016237 1394977686555769840506089)
                    ·
                      refine ⟨1046233264916827380379567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1394977686555769840506089 1046233264916827380379567)
                      ·
                        rfl

theorem cell23_2037532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_2037532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037532 prefixEnd_2037532 := by exact prefixLift 2037532
  have htrace : WordTrace (prefixWord ++ tailWord_2037532) baseStart_2037532 baseEnd_2037532 := by
    simpa [prefixWord, tailWord_2037532, baseEnd_2037532] using wordTrace_append hprefix tailTrace_2037532
  have hstable : (prefixWord ++ tailWord_2037532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037532).length < 2 ^ (prefixWord ++ tailWord_2037532).sum := by decide
  have hdescent : baseEnd_2037532 < baseStart_2037532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037556 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_2037556 : Nat := 118140960795 + 2037556 * 2 ^ 59
def prefixEnd_2037556 : Nat := 4983230072969 + 3 ^ 40 * 2037556 * 2
def baseEnd_2037556 : Nat := 1046245588452535286479457

theorem tailTrace_2037556 : CollatzResearch.WordTrace tailWord_2037556 prefixEnd_2037556 1046245588452535286479457 := by
  unfold tailWord_2037556
  simp only [CollatzResearch.WordTrace]
  refine ⟨37157886303145036852630261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49543848404193382470173681 37157886303145036852630261)
  ·
    refine ⟨3483551840919847204934087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37157886303145036852630261 3483551840919847204934087)
    ·
      refine ⟨5225327761379770807401131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483551840919847204934087 5225327761379770807401131)
      ·
        refine ⟨7837991642069656211101697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225327761379770807401131 7837991642069656211101697)
        ·
          refine ⟨5878493731552242158326273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7837991642069656211101697 5878493731552242158326273)
          ·
            refine ⟨4408870298664181618744705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878493731552242158326273 4408870298664181618744705)
            ·
              refine ⟨3306652723998136214058529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4408870298664181618744705 3306652723998136214058529)
              ·
                refine ⟨2479989542998602160543897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306652723998136214058529 2479989542998602160543897)
                ·
                  refine ⟨1859992157248951620407923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2479989542998602160543897 1859992157248951620407923)
                  ·
                    refine ⟨2789988235873427430611885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1859992157248951620407923 2789988235873427430611885)
                    ·
                      refine ⟨1046245588452535286479457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2789988235873427430611885 1046245588452535286479457)
                      ·
                        rfl

theorem cell23_2037556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_2037556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037556 prefixEnd_2037556 := by exact prefixLift 2037556
  have htrace : WordTrace (prefixWord ++ tailWord_2037556) baseStart_2037556 baseEnd_2037556 := by
    simpa [prefixWord, tailWord_2037556, baseEnd_2037556] using wordTrace_append hprefix tailTrace_2037556
  have hstable : (prefixWord ++ tailWord_2037556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037556).length < 2 ^ (prefixWord ++ tailWord_2037556).sum := by decide
  have hdescent : baseEnd_2037556 < baseStart_2037556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037585 : List Nat := [1, 2, 2, 1, 5, 2, 1, 2, 7]
def baseStart_2037585 : Nat := 118140960795 + 2037585 * 2 ^ 59
def prefixEnd_2037585 : Nat := 4983230072969 + 3 ^ 40 * 2037585 * 2
def baseEnd_2037585 : Nat := 116251164376835074779647

theorem tailTrace_2037585 : CollatzResearch.WordTrace tailWord_2037585 prefixEnd_2037585 116251164376835074779647 := by
  unfold tailWord_2037585
  simp only [CollatzResearch.WordTrace]
  refine ⟨74316830323185011658066209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49544553548790007772044139 74316830323185011658066209)
  ·
    refine ⟨55737622742388758743549657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74316830323185011658066209 55737622742388758743549657)
    ·
      refine ⟨41803217056791569057662243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55737622742388758743549657 41803217056791569057662243)
      ·
        refine ⟨62704825585187353586493365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41803217056791569057662243 62704825585187353586493365)
        ·
          refine ⟨5878577398611314398733753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62704825585187353586493365 5878577398611314398733753)
          ·
            refine ⟨4408933048958485799050315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878577398611314398733753 4408933048958485799050315)
            ·
              refine ⟨6613399573437728698575473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408933048958485799050315 6613399573437728698575473)
              ·
                refine ⟨4960049680078296523931605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6613399573437728698575473 4960049680078296523931605)
                ·
                  refine ⟨116251164376835074779647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4960049680078296523931605 116251164376835074779647)
                  ·
                    rfl

theorem cell23_2037585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 7].length) (baseStart_2037585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037585 prefixEnd_2037585 := by exact prefixLift 2037585
  have htrace : WordTrace (prefixWord ++ tailWord_2037585) baseStart_2037585 baseEnd_2037585 := by
    simpa [prefixWord, tailWord_2037585, baseEnd_2037585] using wordTrace_append hprefix tailTrace_2037585
  have hstable : (prefixWord ++ tailWord_2037585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037585).length < 2 ^ (prefixWord ++ tailWord_2037585).sum := by decide
  have hdescent : baseEnd_2037585 < baseStart_2037585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037630 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2037630 : Nat := 118140960795 + 2037630 * 2 ^ 59
def prefixEnd_2037630 : Nat := 4983230072969 + 3 ^ 40 * 2037630 * 2
def baseEnd_2037630 : Nat := 1046283586020967996954117

theorem tailTrace_2037630 : CollatzResearch.WordTrace tailWord_2037630 prefixEnd_2037630 1046283586020967996954117 := by
  unfold tailWord_2037630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9289808951002748042931793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49545647738681322895636229 9289808951002748042931793)
  ·
    refine ⟨6967356713252061032198845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9289808951002748042931793 6967356713252061032198845)
    ·
      refine ⟨2612758767469522887074567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6967356713252061032198845 2612758767469522887074567)
      ·
        refine ⟨3919138151204284330611851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2612758767469522887074567 3919138151204284330611851)
        ·
          refine ⟨5878707226806426495917777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919138151204284330611851 5878707226806426495917777)
          ·
            refine ⟨4409030420104819871938333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878707226806426495917777 4409030420104819871938333)
            ·
              refine ⟨1653386407539307451976875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4409030420104819871938333 1653386407539307451976875)
              ·
                refine ⟨2480079611308961177965313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653386407539307451976875 2480079611308961177965313)
                ·
                  refine ⟨1860059708481720883473985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480079611308961177965313 1860059708481720883473985)
                  ·
                    refine ⟨1395044781361290662605489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860059708481720883473985 1395044781361290662605489)
                    ·
                      refine ⟨1046283586020967996954117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395044781361290662605489 1046283586020967996954117)
                      ·
                        rfl

theorem cell23_2037630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2037630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037630 prefixEnd_2037630 := by exact prefixLift 2037630
  have htrace : WordTrace (prefixWord ++ tailWord_2037630) baseStart_2037630 baseEnd_2037630 := by
    simpa [prefixWord, tailWord_2037630, baseEnd_2037630] using wordTrace_append hprefix tailTrace_2037630
  have hstable : (prefixWord ++ tailWord_2037630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037630).length < 2 ^ (prefixWord ++ tailWord_2037630).sum := by decide
  have hdescent : baseEnd_2037630 < baseStart_2037630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037635 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4]
def baseStart_2037635 : Nat := 118140960795 + 2037635 * 2 ^ 59
def prefixEnd_2037635 : Nat := 4983230072969 + 3 ^ 40 * 2037635 * 2
def baseEnd_2037635 : Nat := 1046286153424240477391593

theorem tailTrace_2037635 : CollatzResearch.WordTrace tailWord_2037635 prefixEnd_2037635 1046286153424240477391593 := by
  unfold tailWord_2037635
  simp only [CollatzResearch.WordTrace]
  refine ⟨74318653973003870197386359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49545769315335913464924239 74318653973003870197386359)
  ·
    refine ⟨111477980959505805296079539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74318653973003870197386359 111477980959505805296079539)
    ·
      refine ⟨167216971439258707944119309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111477980959505805296079539 167216971439258707944119309)
      ·
        refine ⟨62706364289722015479044741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167216971439258707944119309 62706364289722015479044741)
        ·
          refine ⟨11757443304322877902320889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62706364289722015479044741 11757443304322877902320889)
          ·
            refine ⟨8818082478242158426740667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11757443304322877902320889 8818082478242158426740667)
            ·
              refine ⟨13227123717363237640111001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8818082478242158426740667 13227123717363237640111001)
              ·
                refine ⟨9920342788022428230083251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13227123717363237640111001 9920342788022428230083251)
                ·
                  refine ⟨14880514182033642345124877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920342788022428230083251 14880514182033642345124877)
                  ·
                    refine ⟨5580192818262615879421829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14880514182033642345124877 5580192818262615879421829)
                    ·
                      refine ⟨1046286153424240477391593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5580192818262615879421829 1046286153424240477391593)
                      ·
                        rfl

theorem cell23_2037635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_2037635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037635 prefixEnd_2037635 := by exact prefixLift 2037635
  have htrace : WordTrace (prefixWord ++ tailWord_2037635) baseStart_2037635 baseEnd_2037635 := by
    simpa [prefixWord, tailWord_2037635, baseEnd_2037635] using wordTrace_append hprefix tailTrace_2037635
  have hstable : (prefixWord ++ tailWord_2037635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037635).length < 2 ^ (prefixWord ++ tailWord_2037635).sum := by decide
  have hdescent : baseEnd_2037635 < baseStart_2037635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037652 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2037652 : Nat := 118140960795 + 2037652 * 2 ^ 59
def prefixEnd_2037652 : Nat := 4983230072969 + 3 ^ 40 * 2037652 * 2
def baseEnd_2037652 : Nat := 1046294882595366910879015

theorem tailTrace_2037652 : CollatzResearch.WordTrace tailWord_2037652 prefixEnd_2037652 1046294882595366910879015 := by
  unfold tailWord_2037652
  simp only [CollatzResearch.WordTrace]
  refine ⟨37159637006971141050377605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49546182675961521400503473 37159637006971141050377605)
  ·
    refine ⟨6967431938807088946945801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37159637006971141050377605 6967431938807088946945801)
    ·
      refine ⟨5225573954105316710209351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6967431938807088946945801 5225573954105316710209351)
      ·
        refine ⟨7838360931157975065314027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225573954105316710209351 7838360931157975065314027)
        ·
          refine ⟨11757541396736962597971041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838360931157975065314027 11757541396736962597971041)
          ·
            refine ⟨8818156047552721948478281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11757541396736962597971041 8818156047552721948478281)
            ·
              refine ⟨6613617035664541461358711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8818156047552721948478281 6613617035664541461358711)
              ·
                refine ⟨9920425553496812192038067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613617035664541461358711 9920425553496812192038067)
                ·
                  refine ⟨14880638330245218288057101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920425553496812192038067 14880638330245218288057101)
                  ·
                    refine ⟨5580239373841956858021413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14880638330245218288057101 5580239373841956858021413)
                    ·
                      refine ⟨1046294882595366910879015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5580239373841956858021413 1046294882595366910879015)
                      ·
                        rfl

theorem cell23_2037652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2037652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037652 prefixEnd_2037652 := by exact prefixLift 2037652
  have htrace : WordTrace (prefixWord ++ tailWord_2037652) baseStart_2037652 baseEnd_2037652 := by
    simpa [prefixWord, tailWord_2037652, baseEnd_2037652] using wordTrace_append hprefix tailTrace_2037652
  have hstable : (prefixWord ++ tailWord_2037652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037652).length < 2 ^ (prefixWord ++ tailWord_2037652).sum := by decide
  have hdescent : baseEnd_2037652 < baseStart_2037652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037705 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 3, 5]
def baseStart_2037705 : Nat := 118140960795 + 2037705 * 2 ^ 59
def prefixEnd_2037705 : Nat := 4983230072969 + 3 ^ 40 * 2037705 * 2
def baseEnd_2037705 : Nat := 348774032356685067838757

theorem tailTrace_2037705 : CollatzResearch.WordTrace tailWord_2037705 prefixEnd_2037705 348774032356685067838757 := by
  unfold tailWord_2037705
  simp only [CollatzResearch.WordTrace]
  refine ⟨74321207082750272152434569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49547471388500181434956379 74321207082750272152434569)
  ·
    refine ⟨55740905312062704114325927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74321207082750272152434569 55740905312062704114325927)
    ·
      refine ⟨83611357968094056171488891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55740905312062704114325927 83611357968094056171488891)
      ·
        refine ⟨125417036952141084257233337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83611357968094056171488891 125417036952141084257233337)
        ·
          refine ⟨94062777714105813192925003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125417036952141084257233337 94062777714105813192925003)
          ·
            refine ⟨141094166571158719789387505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94062777714105813192925003 141094166571158719789387505)
            ·
              refine ⟨105820624928369039842040629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141094166571158719789387505 105820624928369039842040629)
              ·
                refine ⟨9920683587034597485191309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105820624928369039842040629 9920683587034597485191309)
                ·
                  refine ⟨3720256345137974056946741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9920683587034597485191309 3720256345137974056946741)
                  ·
                    refine ⟨348774032356685067838757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3720256345137974056946741 348774032356685067838757)
                    ·
                      rfl

theorem cell23_2037705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 3, 5].length) (baseStart_2037705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037705 prefixEnd_2037705 := by exact prefixLift 2037705
  have htrace : WordTrace (prefixWord ++ tailWord_2037705) baseStart_2037705 baseEnd_2037705 := by
    simpa [prefixWord, tailWord_2037705, baseEnd_2037705] using wordTrace_append hprefix tailTrace_2037705
  have hstable : (prefixWord ++ tailWord_2037705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037705).length < 2 ^ (prefixWord ++ tailWord_2037705).sum := by decide
  have hdescent : baseEnd_2037705 < baseStart_2037705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037712 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 1, 5, 2]
def baseStart_2037712 : Nat := 118140960795 + 2037712 * 2 ^ 59
def prefixEnd_2037712 : Nat := 4983230072969 + 3 ^ 40 * 2037712 * 2
def baseEnd_2037712 : Nat := 1046325691434636676128739

theorem tailTrace_2037712 : CollatzResearch.WordTrace tailWord_2037712 prefixEnd_2037712 1046325691434636676128739 := by
  unfold tailWord_2037712
  simp only [CollatzResearch.WordTrace]
  refine ⟨37160731196862456173969695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49547641595816608231959593 37160731196862456173969695)
  ·
    refine ⟨55741096795293684260954543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37160731196862456173969695 55741096795293684260954543)
    ·
      refine ⟨83611645192940526391431815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55741096795293684260954543 83611645192940526391431815)
      ·
        refine ⟨125417467789410789587147723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83611645192940526391431815 125417467789410789587147723)
        ·
          refine ⟨188126201684116184380721585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125417467789410789587147723 188126201684116184380721585)
          ·
            refine ⟨141094651263087138285541189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188126201684116184380721585 141094651263087138285541189)
            ·
              refine ⟨26455247111828838428538973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141094651263087138285541189 26455247111828838428538973)
              ·
                refine ⟨9920717666935814410702115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26455247111828838428538973 9920717666935814410702115)
                ·
                  refine ⟨14881076500403721616053173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920717666935814410702115 14881076500403721616053173)
                  ·
                    refine ⟨1395100921912848901504985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14881076500403721616053173 1395100921912848901504985)
                    ·
                      refine ⟨1046325691434636676128739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395100921912848901504985 1046325691434636676128739)
                      ·
                        rfl

theorem cell23_2037712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 1, 5, 2].length) (baseStart_2037712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037712 prefixEnd_2037712 := by exact prefixLift 2037712
  have htrace : WordTrace (prefixWord ++ tailWord_2037712) baseStart_2037712 baseEnd_2037712 := by
    simpa [prefixWord, tailWord_2037712, baseEnd_2037712] using wordTrace_append hprefix tailTrace_2037712
  have hstable : (prefixWord ++ tailWord_2037712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037712).length < 2 ^ (prefixWord ++ tailWord_2037712).sum := by decide
  have hdescent : baseEnd_2037712 < baseStart_2037712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037729 : List Nat := [1, 2, 3, 1, 2, 1, 4, 2, 2, 3, 2]
def baseStart_2037729 : Nat := 118140960795 + 2037729 * 2 ^ 59
def prefixEnd_2037729 : Nat := 4983230072969 + 3 ^ 40 * 2037729 * 2
def baseEnd_2037729 : Nat := 1046334420605763109616161

theorem tailTrace_2037729 : CollatzResearch.WordTrace tailWord_2037729 prefixEnd_2037729 1046334420605763109616161 := by
  unfold tailWord_2037729
  simp only [CollatzResearch.WordTrace]
  refine ⟨74322082434663324251308241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49548054956442216167538827 74322082434663324251308241)
  ·
    refine ⟨55741561825997493188481181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74322082434663324251308241 55741561825997493188481181)
    ·
      refine ⟨20903085684749059945680443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55741561825997493188481181 20903085684749059945680443)
      ·
        refine ⟨31354628527123589918520665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20903085684749059945680443 31354628527123589918520665)
        ·
          refine ⟨23515971395342692438890499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31354628527123589918520665 23515971395342692438890499)
          ·
            refine ⟨35273957093014038658335749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23515971395342692438890499 35273957093014038658335749)
            ·
              refine ⟨6613866954940132248437953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35273957093014038658335749 6613866954940132248437953)
              ·
                refine ⟨4960400216205099186328465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6613866954940132248437953 4960400216205099186328465)
                ·
                  refine ⟨3720300162153824389746349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960400216205099186328465 3720300162153824389746349)
                  ·
                    refine ⟨1395112560807684146154881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720300162153824389746349 1395112560807684146154881)
                    ·
                      refine ⟨1046334420605763109616161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395112560807684146154881 1046334420605763109616161)
                      ·
                        rfl

theorem cell23_2037729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_2037729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037729 prefixEnd_2037729 := by exact prefixLift 2037729
  have htrace : WordTrace (prefixWord ++ tailWord_2037729) baseStart_2037729 baseEnd_2037729 := by
    simpa [prefixWord, tailWord_2037729, baseEnd_2037729] using wordTrace_append hprefix tailTrace_2037729
  have hstable : (prefixWord ++ tailWord_2037729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037729).length < 2 ^ (prefixWord ++ tailWord_2037729).sum := by decide
  have hdescent : baseEnd_2037729 < baseStart_2037729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037755 : List Nat := [1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6]
def baseStart_2037755 : Nat := 118140960795 + 2037755 * 2 ^ 59
def prefixEnd_2037755 : Nat := 4983230072969 + 3 ^ 40 * 2037755 * 2
def baseEnd_2037755 : Nat := 1046347771102780007891041

theorem tailTrace_2037755 : CollatzResearch.WordTrace tailWord_2037755 prefixEnd_2037755 1046347771102780007891041 := by
  unfold tailWord_2037755
  simp only [CollatzResearch.WordTrace]
  refine ⟨74323030732569130691754719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49548687155046087127836479 74323030732569130691754719)
  ·
    refine ⟨111484546098853696037632079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74323030732569130691754719 111484546098853696037632079)
    ·
      refine ⟨167226819148280544056448119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111484546098853696037632079 167226819148280544056448119)
      ·
        refine ⟨250840228722420816084672179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167226819148280544056448119 250840228722420816084672179)
        ·
          refine ⟨376260343083631224127008269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250840228722420816084672179 376260343083631224127008269)
          ·
            refine ⟨141097628656361709047628101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376260343083631224127008269 141097628656361709047628101)
            ·
              refine ⟨26455805373067820446430269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141097628656361709047628101 26455805373067820446430269)
              ·
                refine ⟨9920927014900432667411351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26455805373067820446430269 9920927014900432667411351)
                ·
                  refine ⟨14881390522350649001117027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920927014900432667411351 14881390522350649001117027)
                  ·
                    refine ⟨22322085783525973501675541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14881390522350649001117027 22322085783525973501675541)
                    ·
                      refine ⟨1046347771102780007891041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22322085783525973501675541 1046347771102780007891041)
                      ·
                        rfl

theorem cell23_2037755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_2037755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037755 prefixEnd_2037755 := by exact prefixLift 2037755
  have htrace : WordTrace (prefixWord ++ tailWord_2037755) baseStart_2037755 baseEnd_2037755 := by
    simpa [prefixWord, tailWord_2037755, baseEnd_2037755] using wordTrace_append hprefix tailTrace_2037755
  have hstable : (prefixWord ++ tailWord_2037755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037755).length < 2 ^ (prefixWord ++ tailWord_2037755).sum := by decide
  have hdescent : baseEnd_2037755 < baseStart_2037755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037772 : List Nat := [2, 2, 1, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_2037772 : Nat := 118140960795 + 2037772 * 2 ^ 59
def prefixEnd_2037772 : Nat := 4983230072969 + 3 ^ 40 * 2037772 * 2
def baseEnd_2037772 : Nat := 1046356500273906441378463

theorem tailTrace_2037772 : CollatzResearch.WordTrace tailWord_2037772 prefixEnd_2037772 1046356500273906441378463 := by
  unfold tailWord_2037772
  simp only [CollatzResearch.WordTrace]
  refine ⟨37161825386753771297561785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49549100515671695063415713 37161825386753771297561785)
  ·
    refine ⟨27871369040065328473171339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37161825386753771297561785 27871369040065328473171339)
    ·
      refine ⟨41807053560097992709757009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27871369040065328473171339 41807053560097992709757009)
      ·
        refine ⟨31355290170073494532317757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41807053560097992709757009 31355290170073494532317757)
        ·
          refine ⟨11758233813777560449619159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31355290170073494532317757 11758233813777560449619159)
          ·
            refine ⟨17637350720666340674428739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758233813777560449619159 17637350720666340674428739)
            ·
              refine ⟨26456026080999511011643109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17637350720666340674428739 26456026080999511011643109)
              ·
                refine ⟨4960504890187408314683083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26456026080999511011643109 4960504890187408314683083)
                ·
                  refine ⟨7440757335281112472024625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960504890187408314683083 7440757335281112472024625)
                  ·
                    refine ⟨5580568001460834354018469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440757335281112472024625 5580568001460834354018469)
                    ·
                      refine ⟨1046356500273906441378463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5580568001460834354018469 1046356500273906441378463)
                      ·
                        rfl

theorem cell23_2037772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_2037772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037772 prefixEnd_2037772 := by exact prefixLift 2037772
  have htrace : WordTrace (prefixWord ++ tailWord_2037772) baseStart_2037772 baseEnd_2037772 := by
    simpa [prefixWord, tailWord_2037772, baseEnd_2037772] using wordTrace_append hprefix tailTrace_2037772
  have hstable : (prefixWord ++ tailWord_2037772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037772).length < 2 ^ (prefixWord ++ tailWord_2037772).sum := by decide
  have hdescent : baseEnd_2037772 < baseStart_2037772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037785 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 6]
def baseStart_2037785 : Nat := 118140960795 + 2037785 * 2 ^ 59
def prefixEnd_2037785 : Nat := 4983230072969 + 3 ^ 40 * 2037785 * 2
def baseEnd_2037785 : Nat := 1046363175522414890515903

theorem tailTrace_2037785 : CollatzResearch.WordTrace tailWord_2037785 prefixEnd_2037785 1046363175522414890515903 := by
  unfold tailWord_2037785
  simp only [CollatzResearch.WordTrace]
  refine ⟨74324124922460445815346809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49549416614973630543564539 74324124922460445815346809)
  ·
    refine ⟨55743093691845334361510107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74324124922460445815346809 55743093691845334361510107)
    ·
      refine ⟨83614640537768001542265161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55743093691845334361510107 83614640537768001542265161)
      ·
        refine ⟨62710980403326001156698871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83614640537768001542265161 62710980403326001156698871)
        ·
          refine ⟨94066470604989001735048307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62710980403326001156698871 94066470604989001735048307)
          ·
            refine ⟨141099705907483502602572461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94066470604989001735048307 141099705907483502602572461)
            ·
              refine ⟨52912389715306313475964673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141099705907483502602572461 52912389715306313475964673)
              ·
                refine ⟨39684292286479735106973505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52912389715306313475964673 39684292286479735106973505)
                ·
                  refine ⟨29763219214859801330230129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39684292286479735106973505 29763219214859801330230129)
                  ·
                    refine ⟨22322414411144850997672597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29763219214859801330230129 22322414411144850997672597)
                    ·
                      refine ⟨1046363175522414890515903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22322414411144850997672597 1046363175522414890515903)
                      ·
                        rfl

theorem cell23_2037785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_2037785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037785 prefixEnd_2037785 := by exact prefixLift 2037785
  have htrace : WordTrace (prefixWord ++ tailWord_2037785) baseStart_2037785 baseEnd_2037785 := by
    simpa [prefixWord, tailWord_2037785, baseEnd_2037785] using wordTrace_append hprefix tailTrace_2037785
  have hstable : (prefixWord ++ tailWord_2037785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037785).length < 2 ^ (prefixWord ++ tailWord_2037785).sum := by decide
  have hdescent : baseEnd_2037785 < baseStart_2037785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037786 : List Nat := [3, 1, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_2037786 : Nat := 118140960795 + 2037786 * 2 ^ 59
def prefixEnd_2037786 : Nat := 4983230072969 + 3 ^ 40 * 2037786 * 2
def baseEnd_2037786 : Nat := 348787896334356462201133

theorem tailTrace_2037786 : CollatzResearch.WordTrace tailWord_2037786 prefixEnd_2037786 348787896334356462201133 := by
  unfold tailWord_2037786
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581040348864205746533303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49549440930304548657422141 18581040348864205746533303)
  ·
    refine ⟨27871560523296308619799955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18581040348864205746533303 27871560523296308619799955)
    ·
      refine ⟨41807340784944462929699933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27871560523296308619799955 41807340784944462929699933)
      ·
        refine ⟨15677752794354173598637475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41807340784944462929699933 15677752794354173598637475)
        ·
          refine ⟨23516629191531260397956213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15677752794354173598637475 23516629191531260397956213)
          ·
            refine ⟨2204683986706055662308395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23516629191531260397956213 2204683986706055662308395)
            ·
              refine ⟨3307025980059083493462593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204683986706055662308395 3307025980059083493462593)
              ·
                refine ⟨2480269485044312620096945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307025980059083493462593 2480269485044312620096945)
                ·
                  refine ⟨1860202113783234465072709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480269485044312620096945 1860202113783234465072709)
                  ·
                    refine ⟨348787896334356462201133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860202113783234465072709 348787896334356462201133)
                    ·
                      rfl

theorem cell23_2037786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_2037786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037786 prefixEnd_2037786 := by exact prefixLift 2037786
  have htrace : WordTrace (prefixWord ++ tailWord_2037786) baseStart_2037786 baseEnd_2037786 := by
    simpa [prefixWord, tailWord_2037786, baseEnd_2037786] using wordTrace_append hprefix tailTrace_2037786
  have hstable : (prefixWord ++ tailWord_2037786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037786).length < 2 ^ (prefixWord ++ tailWord_2037786).sum := by decide
  have hdescent : baseEnd_2037786 < baseStart_2037786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037793 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 3, 2, 2]
def baseStart_2037793 : Nat := 118140960795 + 2037793 * 2 ^ 59
def prefixEnd_2037793 : Nat := 4983230072969 + 3 ^ 40 * 2037793 * 2
def baseEnd_2037793 : Nat := 1046367283367650859215867

theorem tailTrace_2037793 : CollatzResearch.WordTrace tailWord_2037793 prefixEnd_2037793 1046367283367650859215867 := by
  unfold tailWord_2037793
  simp only [CollatzResearch.WordTrace]
  refine ⟨74324416706431463181638033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49549611137620975454425355 74324416706431463181638033)
  ·
    refine ⟨55743312529823597386228525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74324416706431463181638033 55743312529823597386228525)
    ·
      refine ⟨20903742198683849019835697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55743312529823597386228525 20903742198683849019835697)
      ·
        refine ⟨15677806649012886764876773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20903742198683849019835697 15677806649012886764876773)
        ·
          refine ⟨2939588746689916268414395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15677806649012886764876773 2939588746689916268414395)
          ·
            refine ⟨4409383120034874402621593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939588746689916268414395 4409383120034874402621593)
            ·
              refine ⟨3307037340026155801966195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409383120034874402621593 3307037340026155801966195)
              ·
                refine ⟨4960556010039233702949293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307037340026155801966195 4960556010039233702949293)
                ·
                  refine ⟨1860208503764712638605985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4960556010039233702949293 1860208503764712638605985)
                  ·
                    refine ⟨1395156377823534478954489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860208503764712638605985 1395156377823534478954489)
                    ·
                      refine ⟨1046367283367650859215867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395156377823534478954489 1046367283367650859215867)
                      ·
                        rfl

theorem cell23_2037793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_2037793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037793 prefixEnd_2037793 := by exact prefixLift 2037793
  have htrace : WordTrace (prefixWord ++ tailWord_2037793) baseStart_2037793 baseEnd_2037793 := by
    simpa [prefixWord, tailWord_2037793, baseEnd_2037793] using wordTrace_append hprefix tailTrace_2037793
  have hstable : (prefixWord ++ tailWord_2037793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037793).length < 2 ^ (prefixWord ++ tailWord_2037793).sum := by decide
  have hdescent : baseEnd_2037793 < baseStart_2037793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037806 : List Nat := [4, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2037806 : Nat := 118140960795 + 2037806 * 2 ^ 59
def prefixEnd_2037806 : Nat := 4983230072969 + 3 ^ 40 * 2037806 * 2
def baseEnd_2037806 : Nat := 1046373958616159308353307

theorem tailTrace_2037806 : CollatzResearch.WordTrace tailWord_2037806 prefixEnd_2037806 1046373958616159308353307 := by
  unfold tailWord_2037806
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290611356923045800232659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49549927236922910934574181 9290611356923045800232659)
  ·
    refine ⟨13935917035384568700348989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9290611356923045800232659 13935917035384568700348989)
    ·
      refine ⟨5225968888269213262630871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13935917035384568700348989 5225968888269213262630871)
      ·
        refine ⟨7838953332403819893946307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225968888269213262630871 7838953332403819893946307)
        ·
          refine ⟨11758429998605729840919461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838953332403819893946307 11758429998605729840919461)
          ·
            refine ⟨2204705624738574345172399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11758429998605729840919461 2204705624738574345172399)
            ·
              refine ⟨3307058437107861517758599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2204705624738574345172399 3307058437107861517758599)
              ·
                refine ⟨4960587655661792276637899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307058437107861517758599 4960587655661792276637899)
                ·
                  refine ⟨7440881483492688414956849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960587655661792276637899 7440881483492688414956849)
                  ·
                    refine ⟨5580661112619516311217637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440881483492688414956849 5580661112619516311217637)
                    ·
                      refine ⟨1046373958616159308353307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5580661112619516311217637 1046373958616159308353307)
                      ·
                        rfl

theorem cell23_2037806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2037806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037806 prefixEnd_2037806 := by exact prefixLift 2037806
  have htrace : WordTrace (prefixWord ++ tailWord_2037806) baseStart_2037806 baseEnd_2037806 := by
    simpa [prefixWord, tailWord_2037806, baseEnd_2037806] using wordTrace_append hprefix tailTrace_2037806
  have hstable : (prefixWord ++ tailWord_2037806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037806).length < 2 ^ (prefixWord ++ tailWord_2037806).sum := by decide
  have hdescent : baseEnd_2037806 < baseStart_2037806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037809 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 3]
def baseStart_2037809 : Nat := 118140960795 + 2037809 * 2 ^ 59
def prefixEnd_2037809 : Nat := 4983230072969 + 3 ^ 40 * 2037809 * 2
def baseEnd_2037809 : Nat := 1046375499058122796615793

theorem tailTrace_2037809 : CollatzResearch.WordTrace tailWord_2037809 prefixEnd_2037809 1046375499058122796615793 := by
  unfold tailWord_2037809
  simp only [CollatzResearch.WordTrace]
  refine ⟨74325000274373497914220481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49550000182915665276146987 74325000274373497914220481)
  ·
    refine ⟨55743750205780123435665361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74325000274373497914220481 55743750205780123435665361)
    ·
      refine ⟨41807812654335092576749021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55743750205780123435665361 41807812654335092576749021)
      ·
        refine ⟨15677929745375659716280883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41807812654335092576749021 15677929745375659716280883)
        ·
          refine ⟨23516894618063489574421325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15677929745375659716280883 23516894618063489574421325)
          ·
            refine ⟨8818835481773808590407997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23516894618063489574421325 8818835481773808590407997)
            ·
              refine ⟨3307063305665178221402999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8818835481773808590407997 3307063305665178221402999)
              ·
                refine ⟨4960594958497767332104499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307063305665178221402999 4960594958497767332104499)
                ·
                  refine ⟨7440892437746650998156749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960594958497767332104499 7440892437746650998156749)
                  ·
                    refine ⟨2790334664154994124308781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7440892437746650998156749 2790334664154994124308781)
                    ·
                      refine ⟨1046375499058122796615793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2790334664154994124308781 1046375499058122796615793)
                      ·
                        rfl

theorem cell23_2037809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_2037809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037809 prefixEnd_2037809 := by exact prefixLift 2037809
  have htrace : WordTrace (prefixWord ++ tailWord_2037809) baseStart_2037809 baseEnd_2037809 := by
    simpa [prefixWord, tailWord_2037809, baseEnd_2037809] using wordTrace_append hprefix tailTrace_2037809
  have hstable : (prefixWord ++ tailWord_2037809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037809).length < 2 ^ (prefixWord ++ tailWord_2037809).sum := by decide
  have hdescent : baseEnd_2037809 < baseStart_2037809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037816 : List Nat := [2, 1, 2, 1, 7, 1, 2, 7]
def baseStart_2037816 : Nat := 118140960795 + 2037816 * 2 ^ 59
def prefixEnd_2037816 : Nat := 4983230072969 + 3 ^ 40 * 2037816 * 2
def baseEnd_2037816 : Nat := 38754781237877935897343

theorem tailTrace_2037816 : CollatzResearch.WordTrace tailWord_2037816 prefixEnd_2037816 38754781237877935897343 := by
  unfold tailWord_2037816
  simp only [CollatzResearch.WordTrace]
  refine ⟨37162627792674069054862651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49550170390232092073150201 37162627792674069054862651)
  ·
    refine ⟨55743941689011103582293977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37162627792674069054862651 55743941689011103582293977)
    ·
      refine ⟨41807956266758327686720483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55743941689011103582293977 41807956266758327686720483)
      ·
        refine ⟨62711934400137491530080725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41807956266758327686720483 62711934400137491530080725)
        ·
          refine ⟨1469810962503222457736267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 62711934400137491530080725 1469810962503222457736267)
          ·
            refine ⟨2204716443754833686604401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469810962503222457736267 2204716443754833686604401)
            ·
              refine ⟨1653537332816125264953301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204716443754833686604401 1653537332816125264953301)
              ·
                refine ⟨38754781237877935897343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1653537332816125264953301 38754781237877935897343)
                ·
                  rfl

theorem cell23_2037816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 2, 7].length) (baseStart_2037816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037816 prefixEnd_2037816 := by exact prefixLift 2037816
  have htrace : WordTrace (prefixWord ++ tailWord_2037816) baseStart_2037816 baseEnd_2037816 := by
    simpa [prefixWord, tailWord_2037816, baseEnd_2037816] using wordTrace_append hprefix tailTrace_2037816
  have hstable : (prefixWord ++ tailWord_2037816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037816).length < 2 ^ (prefixWord ++ tailWord_2037816).sum := by decide
  have hdescent : baseEnd_2037816 < baseStart_2037816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037836 : List Nat := [2, 2, 1, 3, 1, 1, 4, 3, 1, 3, 2]
def baseStart_2037836 : Nat := 118140960795 + 2037836 * 2 ^ 59
def prefixEnd_2037836 : Nat := 4983230072969 + 3 ^ 40 * 2037836 * 2
def baseEnd_2037836 : Nat := 1046389363035794190978169

theorem tailTrace_2037836 : CollatzResearch.WordTrace tailWord_2037836 prefixEnd_2037836 1046389363035794190978169 := by
  unfold tailWord_2037836
  simp only [CollatzResearch.WordTrace]
  refine ⟨37162992522637840762726681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49550656696850454350302241 37162992522637840762726681)
  ·
    refine ⟨27872244391978380572045011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37162992522637840762726681 27872244391978380572045011)
    ·
      refine ⟨41808366587967570858067517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27872244391978380572045011 41808366587967570858067517)
      ·
        refine ⟨15678137470487839071775319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41808366587967570858067517 15678137470487839071775319)
        ·
          refine ⟨23517206205731758607662979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15678137470487839071775319 23517206205731758607662979)
          ·
            refine ⟨35275809308597637911494469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23517206205731758607662979 35275809308597637911494469)
            ·
              refine ⟨6614214245362057108405213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35275809308597637911494469 6614214245362057108405213)
              ·
                refine ⟨2480330342010771415651955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6614214245362057108405213 2480330342010771415651955)
                ·
                  refine ⟨3720495513016157123477933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480330342010771415651955 3720495513016157123477933)
                  ·
                    refine ⟨1395185817381058921304225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720495513016157123477933 1395185817381058921304225)
                    ·
                      refine ⟨1046389363035794190978169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395185817381058921304225 1046389363035794190978169)
                      ·
                        rfl

theorem cell23_2037836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_2037836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037836 prefixEnd_2037836 := by exact prefixLift 2037836
  have htrace : WordTrace (prefixWord ++ tailWord_2037836) baseStart_2037836 baseEnd_2037836 := by
    simpa [prefixWord, tailWord_2037836, baseEnd_2037836] using wordTrace_append hprefix tailTrace_2037836
  have hstable : (prefixWord ++ tailWord_2037836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037836).length < 2 ^ (prefixWord ++ tailWord_2037836).sum := by decide
  have hdescent : baseEnd_2037836 < baseStart_2037836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037854 : List Nat := [4, 4, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_2037854 : Nat := 118140960795 + 2037854 * 2 ^ 59
def prefixEnd_2037854 : Nat := 4983230072969 + 3 ^ 40 * 2037854 * 2
def baseEnd_2037854 : Nat := 348799535229191706851029

theorem tailTrace_2037854 : CollatzResearch.WordTrace tailWord_2037854 prefixEnd_2037854 348799535229191706851029 := by
  unfold tailWord_2037854
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290830194901308824951077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49551094372806980399739077 9290830194901308824951077)
  ·
    refine ⟨1742030661543995404678327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9290830194901308824951077 1742030661543995404678327)
    ·
      refine ⟨2613045992315993107017491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1742030661543995404678327 2613045992315993107017491)
      ·
        refine ⟨3919568988473989660526237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613045992315993107017491 3919568988473989660526237)
        ·
          refine ⟨1469838370677746122697339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3919568988473989660526237 1469838370677746122697339)
          ·
            refine ⟨2204757556016619184046009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469838370677746122697339 2204757556016619184046009)
            ·
              refine ⟨1653568167012464388034507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2204757556016619184046009 1653568167012464388034507)
              ·
                refine ⟨2480352250518696582051761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653568167012464388034507 2480352250518696582051761)
                ·
                  refine ⟨1860264187889022436538821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480352250518696582051761 1860264187889022436538821)
                  ·
                    refine ⟨348799535229191706851029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860264187889022436538821 348799535229191706851029)
                    ·
                      rfl

theorem cell23_2037854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_2037854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037854 prefixEnd_2037854 := by exact prefixLift 2037854
  have htrace : WordTrace (prefixWord ++ tailWord_2037854) baseStart_2037854 baseEnd_2037854 := by
    simpa [prefixWord, tailWord_2037854, baseEnd_2037854] using wordTrace_append hprefix tailTrace_2037854
  have hstable : (prefixWord ++ tailWord_2037854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037854).length < 2 ^ (prefixWord ++ tailWord_2037854).sum := by decide
  have hdescent : baseEnd_2037854 < baseStart_2037854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037906 : List Nat := [3, 2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_2037906 : Nat := 118140960795 + 2037906 * 2 ^ 59
def prefixEnd_2037906 : Nat := 4983230072969 + 3 ^ 40 * 2037906 * 2
def baseEnd_2037906 : Nat := 116269478520178768566983

theorem tailTrace_2037906 : CollatzResearch.WordTrace tailWord_2037906 prefixEnd_2037906 116269478520178768566983 := by
  unfold tailWord_2037906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18582134538755520870125393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49552358770014722320334381 18582134538755520870125393)
  ·
    refine ⟨13936600904066640652594045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18582134538755520870125393 13936600904066640652594045)
    ·
      refine ⟨5226225339024990244722767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13936600904066640652594045 5226225339024990244722767)
      ·
        refine ⟨7839338008537485367084151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226225339024990244722767 7839338008537485367084151)
        ·
          refine ⟨11759007012806228050626227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7839338008537485367084151 11759007012806228050626227)
          ·
            refine ⟨17638510519209342075939341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11759007012806228050626227 17638510519209342075939341)
            ·
              refine ⟨6614441444703503278477253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17638510519209342075939341 6614441444703503278477253)
              ·
                refine ⟨1240207770881906864714485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6614441444703503278477253 1240207770881906864714485)
                ·
                  refine ⟨116269478520178768566983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1240207770881906864714485 116269478520178768566983)
                  ·
                    rfl

theorem cell23_2037906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_2037906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037906 prefixEnd_2037906 := by exact prefixLift 2037906
  have htrace : WordTrace (prefixWord ++ tailWord_2037906) baseStart_2037906 baseEnd_2037906 := by
    simpa [prefixWord, tailWord_2037906, baseEnd_2037906] using wordTrace_append hprefix tailTrace_2037906
  have hstable : (prefixWord ++ tailWord_2037906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037906).length < 2 ^ (prefixWord ++ tailWord_2037906).sum := by decide
  have hdescent : baseEnd_2037906 < baseStart_2037906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037909 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_2037909 : Nat := 118140960795 + 2037909 * 2 ^ 59
def prefixEnd_2037909 : Nat := 4983230072969 + 3 ^ 40 * 2037909 * 2
def baseEnd_2037909 : Nat := 1046426847123572405365333

theorem tailTrace_2037909 : CollatzResearch.WordTrace tailWord_2037909 prefixEnd_2037909 1046426847123572405365333 := by
  unfold tailWord_2037909
  simp only [CollatzResearch.WordTrace]
  refine ⟨74328647574011214992860781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49552431716007476661907187 74328647574011214992860781)
  ·
    refine ⟨27873242840254205622322793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74328647574011214992860781 27873242840254205622322793)
    ·
      refine ⟨20904932130190654216742095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27873242840254205622322793 20904932130190654216742095)
      ·
        refine ⟨31357398195285981325113143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20904932130190654216742095 31357398195285981325113143)
        ·
          refine ⟨47036097292928971987669715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31357398195285981325113143 47036097292928971987669715)
          ·
            refine ⟨70554145939393457981504573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47036097292928971987669715 70554145939393457981504573)
            ·
              refine ⟨26457804727272546743064215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70554145939393457981504573 26457804727272546743064215)
              ·
                refine ⟨39686707090908820114596323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26457804727272546743064215 39686707090908820114596323)
                ·
                  refine ⟨59530060636363230171894485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39686707090908820114596323 59530060636363230171894485)
                  ·
                    refine ⟨1395235796164763207153777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59530060636363230171894485 1395235796164763207153777)
                    ·
                      refine ⟨1046426847123572405365333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395235796164763207153777 1046426847123572405365333)
                      ·
                        rfl

theorem cell23_2037909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_2037909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037909 prefixEnd_2037909 := by exact prefixLift 2037909
  have htrace : WordTrace (prefixWord ++ tailWord_2037909) baseStart_2037909 baseEnd_2037909 := by
    simpa [prefixWord, tailWord_2037909, baseEnd_2037909] using wordTrace_append hprefix tailTrace_2037909
  have hstable : (prefixWord ++ tailWord_2037909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037909).length < 2 ^ (prefixWord ++ tailWord_2037909).sum := by decide
  have hdescent : baseEnd_2037909 < baseStart_2037909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037939 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 6, 2]
def baseStart_2037939 : Nat := 118140960795 + 2037939 * 2 ^ 59
def prefixEnd_2037939 : Nat := 4983230072969 + 3 ^ 40 * 2037939 * 2
def baseEnd_2037939 : Nat := 1046442251543207287990195

theorem tailTrace_2037939 : CollatzResearch.WordTrace tailWord_2037939 prefixEnd_2037939 1046442251543207287990195 := by
  unfold tailWord_2037939
  simp only [CollatzResearch.WordTrace]
  refine ⟨74329741763902530116452871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49553161175935020077635247 74329741763902530116452871)
  ·
    refine ⟨111494612645853795174679307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74329741763902530116452871 111494612645853795174679307)
    ·
      refine ⟨167241918968780692762018961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111494612645853795174679307 167241918968780692762018961)
      ·
        refine ⟨125431439226585519571514221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167241918968780692762018961 125431439226585519571514221)
        ·
          refine ⟨47036789709969569839317833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125431439226585519571514221 47036789709969569839317833)
          ·
            refine ⟨35277592282477177379488375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47036789709969569839317833 35277592282477177379488375)
            ·
              refine ⟨52916388423715766069232563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35277592282477177379488375 52916388423715766069232563)
              ·
                refine ⟨79374582635573649103848845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52916388423715766069232563 79374582635573649103848845)
                ·
                  refine ⟨29765468488340118413943317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79374582635573649103848845 29765468488340118413943317)
                  ·
                    refine ⟨1395256335390943050653593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29765468488340118413943317 1395256335390943050653593)
                    ·
                      refine ⟨1046442251543207287990195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395256335390943050653593 1046442251543207287990195)
                      ·
                        rfl

theorem cell23_2037939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6, 2].length) (baseStart_2037939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037939 prefixEnd_2037939 := by exact prefixLift 2037939
  have htrace : WordTrace (prefixWord ++ tailWord_2037939) baseStart_2037939 baseEnd_2037939 := by
    simpa [prefixWord, tailWord_2037939, baseEnd_2037939] using wordTrace_append hprefix tailTrace_2037939
  have hstable : (prefixWord ++ tailWord_2037939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037939).length < 2 ^ (prefixWord ++ tailWord_2037939).sum := by decide
  have hdescent : baseEnd_2037939 < baseStart_2037939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037949 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_2037949 : Nat := 118140960795 + 2037949 * 2 ^ 59
def prefixEnd_2037949 : Nat := 4983230072969 + 3 ^ 40 * 2037949 * 2
def baseEnd_2037949 : Nat := 348815795449917416288383

theorem tailTrace_2037949 : CollatzResearch.WordTrace tailWord_2037949 prefixEnd_2037949 348815795449917416288383 := by
  unfold tailWord_2037949
  simp only [CollatzResearch.WordTrace]
  refine ⟨74330106493866301824316901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49553404329244201216211267 74330106493866301824316901)
  ·
    refine ⟨13936894967599931592059419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74330106493866301824316901 13936894967599931592059419)
    ·
      refine ⟨20905342451399897388089129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13936894967599931592059419 20905342451399897388089129)
      ·
        refine ⟨15679006838549923041066847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20905342451399897388089129 15679006838549923041066847)
        ·
          refine ⟨23518510257824884561600271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679006838549923041066847 23518510257824884561600271)
          ·
            refine ⟨35277765386737326842400407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23518510257824884561600271 35277765386737326842400407)
            ·
              refine ⟨52916648080105990263600611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35277765386737326842400407 52916648080105990263600611)
              ·
                refine ⟨79374972120158985395400917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52916648080105990263600611 79374972120158985395400917)
                ·
                  refine ⟨1860350909066226220204709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 79374972120158985395400917 1860350909066226220204709)
                  ·
                    refine ⟨348815795449917416288383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860350909066226220204709 348815795449917416288383)
                    ·
                      rfl

theorem cell23_2037949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_2037949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037949 prefixEnd_2037949 := by exact prefixLift 2037949
  have htrace : WordTrace (prefixWord ++ tailWord_2037949) baseStart_2037949 baseEnd_2037949 := by
    simpa [prefixWord, tailWord_2037949, baseEnd_2037949] using wordTrace_append hprefix tailTrace_2037949
  have hstable : (prefixWord ++ tailWord_2037949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037949).length < 2 ^ (prefixWord ++ tailWord_2037949).sum := by decide
  have hdescent : baseEnd_2037949 < baseStart_2037949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2037966 : List Nat := [4, 1, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_2037966 : Nat := 118140960795 + 2037966 * 2 ^ 59
def prefixEnd_2037966 : Nat := 4983230072969 + 3 ^ 40 * 2037966 * 2
def baseEnd_2037966 : Nat := 348818705173626227450857

theorem tailTrace_2037966 : CollatzResearch.WordTrace tailWord_2037966 prefixEnd_2037966 348818705173626227450857 := by
  unfold tailWord_2037966
  simp only [CollatzResearch.WordTrace]
  refine ⟨9291340816850589215960719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49553817689869809151790501 9291340816850589215960719)
  ·
    refine ⟨13937011225275883823941079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9291340816850589215960719 13937011225275883823941079)
    ·
      refine ⟨20905516837913825735911619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13937011225275883823941079 20905516837913825735911619)
      ·
        refine ⟨31358275256870738603867429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20905516837913825735911619 31358275256870738603867429)
        ·
          refine ⟨5879676610663263488225143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31358275256870738603867429 5879676610663263488225143)
          ·
            refine ⟨8819514915994895232337715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879676610663263488225143 8819514915994895232337715)
            ·
              refine ⟨13229272373992342848506573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819514915994895232337715 13229272373992342848506573)
              ·
                refine ⟨4960977140247128568189965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13229272373992342848506573 4960977140247128568189965)
                ·
                  refine ⟨1860366427592673213071237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4960977140247128568189965 1860366427592673213071237)
                  ·
                    refine ⟨348818705173626227450857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860366427592673213071237 348818705173626227450857)
                    ·
                      rfl

theorem cell23_2037966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_2037966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2037966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2037966 prefixEnd_2037966 := by exact prefixLift 2037966
  have htrace : WordTrace (prefixWord ++ tailWord_2037966) baseStart_2037966 baseEnd_2037966 := by
    simpa [prefixWord, tailWord_2037966, baseEnd_2037966] using wordTrace_append hprefix tailTrace_2037966
  have hstable : (prefixWord ++ tailWord_2037966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2037966).length < 2 ^ (prefixWord ++ tailWord_2037966).sum := by decide
  have hdescent : baseEnd_2037966 < baseStart_2037966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2037966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038016 : List Nat := [2, 1, 1, 2, 1, 1, 5, 1, 4, 3, 2]
def baseStart_2038016 : Nat := 118140960795 + 2038016 * 2 ^ 59
def prefixEnd_2038016 : Nat := 4983230072969 + 3 ^ 40 * 2038016 * 2
def baseEnd_2038016 : Nat := 1046481789553603486727341

theorem tailTrace_2038016 : CollatzResearch.WordTrace tailWord_2038016 prefixEnd_2038016 1046481789553603486727341 := by
  unfold tailWord_2038016
  simp only [CollatzResearch.WordTrace]
  refine ⟨37166275092311786133502951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49555033456415714844670601 37166275092311786133502951)
  ·
    refine ⟨55749412638467679200254427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37166275092311786133502951 55749412638467679200254427)
    ·
      refine ⟨83624118957701518800381641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55749412638467679200254427 83624118957701518800381641)
      ·
        refine ⟨62718089218276139100286231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83624118957701518800381641 62718089218276139100286231)
        ·
          refine ⟨94077133827414208650429347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62718089218276139100286231 94077133827414208650429347)
          ·
            refine ⟨141115700741121312975644021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94077133827414208650429347 141115700741121312975644021)
            ·
              refine ⟨13229596944480123091466627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141115700741121312975644021 13229596944480123091466627)
              ·
                refine ⟨19844395416720184637199941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13229596944480123091466627 19844395416720184637199941)
                ·
                  refine ⟨3720824140635034619474989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19844395416720184637199941 3720824140635034619474989)
                  ·
                    refine ⟨1395309052738137982303121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720824140635034619474989 1395309052738137982303121)
                    ·
                      refine ⟨1046481789553603486727341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395309052738137982303121 1046481789553603486727341)
                      ·
                        rfl

theorem cell23_2038016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 4, 3, 2].length) (baseStart_2038016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038016 prefixEnd_2038016 := by exact prefixLift 2038016
  have htrace : WordTrace (prefixWord ++ tailWord_2038016) baseStart_2038016 baseEnd_2038016 := by
    simpa [prefixWord, tailWord_2038016, baseEnd_2038016] using wordTrace_append hprefix tailTrace_2038016
  have hstable : (prefixWord ++ tailWord_2038016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038016).length < 2 ^ (prefixWord ++ tailWord_2038016).sum := by decide
  have hdescent : baseEnd_2038016 < baseStart_2038016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038049 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2038049 : Nat := 118140960795 + 2038049 * 2 ^ 59
def prefixEnd_2038049 : Nat := 4983230072969 + 3 ^ 40 * 2038049 * 2
def baseEnd_2038049 : Nat := 1046498734415201857614689

theorem tailTrace_2038049 : CollatzResearch.WordTrace tailWord_2038049 prefixEnd_2038049 1046498734415201857614689 := by
  unfold tailWord_2038049
  simp only [CollatzResearch.WordTrace]
  refine ⟨74333753793504018902957201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49555835862336012601971467 74333753793504018902957201)
  ·
    refine ⟨55750315345128014177217901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74333753793504018902957201 55750315345128014177217901)
    ·
      refine ⟨20906368254423005316456713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55750315345128014177217901 20906368254423005316456713)
      ·
        refine ⟨15679776190817253987342535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20906368254423005316456713 15679776190817253987342535)
        ·
          refine ⟨23519664286225880981013803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679776190817253987342535 23519664286225880981013803)
          ·
            refine ⟨35279496429338821471520705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23519664286225880981013803 35279496429338821471520705)
            ·
              refine ⟨26459622322004116103640529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35279496429338821471520705 26459622322004116103640529)
              ·
                refine ⟨19844716741503087077730397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26459622322004116103640529 19844716741503087077730397)
                ·
                  refine ⟨7441768778063657654148899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19844716741503087077730397 7441768778063657654148899)
                  ·
                    refine ⟨11162653167095486481223349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441768778063657654148899 11162653167095486481223349)
                    ·
                      refine ⟨1046498734415201857614689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11162653167095486481223349 1046498734415201857614689)
                      ·
                        rfl

theorem cell23_2038049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2038049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038049 prefixEnd_2038049 := by exact prefixLift 2038049
  have htrace : WordTrace (prefixWord ++ tailWord_2038049) baseStart_2038049 baseEnd_2038049 := by
    simpa [prefixWord, tailWord_2038049, baseEnd_2038049] using wordTrace_append hprefix tailTrace_2038049
  have hstable : (prefixWord ++ tailWord_2038049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038049).length < 2 ^ (prefixWord ++ tailWord_2038049).sum := by decide
  have hdescent : baseEnd_2038049 < baseStart_2038049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038050 : List Nat := [3, 3, 1, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_2038050 : Nat := 118140960795 + 2038050 * 2 ^ 59
def prefixEnd_2038050 : Nat := 4983230072969 + 3 ^ 40 * 2038050 * 2
def baseEnd_2038050 : Nat := 1046499247895856353702185

theorem tailTrace_2038050 : CollatzResearch.WordTrace tailWord_2038050 prefixEnd_2038050 1046499247895856353702185 := by
  unfold tailWord_2038050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18583447566625099018435901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49555860177666930715829069 18583447566625099018435901)
  ·
    refine ⟨6968792837484412131913463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18583447566625099018435901 6968792837484412131913463)
    ·
      refine ⟨10453189256226618197870195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6968792837484412131913463 10453189256226618197870195)
      ·
        refine ⟨15679783884339927296805293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453189256226618197870195 15679783884339927296805293)
        ·
          refine ⟨5879918956627472736301985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15679783884339927296805293 5879918956627472736301985)
          ·
            refine ⟨4409939217470604552226489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879918956627472736301985 4409939217470604552226489)
            ·
              refine ⟨3307454413102953414169867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409939217470604552226489 3307454413102953414169867)
              ·
                refine ⟨4961181619654430121254801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307454413102953414169867 4961181619654430121254801)
                ·
                  refine ⟨3720886214740822590941101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4961181619654430121254801 3720886214740822590941101)
                  ·
                    refine ⟨1395332330527808471602913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3720886214740822590941101 1395332330527808471602913)
                    ·
                      refine ⟨1046499247895856353702185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395332330527808471602913 1046499247895856353702185)
                      ·
                        rfl

theorem cell23_2038050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_2038050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038050 prefixEnd_2038050 := by exact prefixLift 2038050
  have htrace : WordTrace (prefixWord ++ tailWord_2038050) baseStart_2038050 baseEnd_2038050 := by
    simpa [prefixWord, tailWord_2038050, baseEnd_2038050] using wordTrace_append hprefix tailTrace_2038050
  have hstable : (prefixWord ++ tailWord_2038050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038050).length < 2 ^ (prefixWord ++ tailWord_2038050).sum := by decide
  have hdescent : baseEnd_2038050 < baseStart_2038050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038073 : List Nat := [1, 2, 1, 6, 1, 1, 1, 4, 2, 4]
def baseStart_2038073 : Nat := 118140960795 + 2038073 * 2 ^ 59
def prefixEnd_2038073 : Nat := 4983230072969 + 3 ^ 40 * 2038073 * 2
def baseEnd_2038073 : Nat := 348837019316969921238193

theorem tailTrace_2038073 : CollatzResearch.WordTrace tailWord_2038073 prefixEnd_2038073 348837019316969921238193 := by
  unfold tailWord_2038073
  simp only [CollatzResearch.WordTrace]
  refine ⟨74334629145417071001830873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49556419430278047334553915 74334629145417071001830873)
  ·
    refine ⟨55750971859062803251373155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74334629145417071001830873 55750971859062803251373155)
    ·
      refine ⟨83626457788594204877059733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55750971859062803251373155 83626457788594204877059733)
      ·
        refine ⟨3919990208840353353612175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83626457788594204877059733 3919990208840353353612175)
        ·
          refine ⟨5879985313260530030418263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919990208840353353612175 5879985313260530030418263)
          ·
            refine ⟨8819977969890795045627395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879985313260530030418263 8819977969890795045627395)
            ·
              refine ⟨13229966954836192568441093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819977969890795045627395 13229966954836192568441093)
              ·
                refine ⟨2480618804031786106582705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13229966954836192568441093 2480618804031786106582705)
                ·
                  refine ⟨1860464103023839579937029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480618804031786106582705 1860464103023839579937029)
                  ·
                    refine ⟨348837019316969921238193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860464103023839579937029 348837019316969921238193)
                    ·
                      rfl

theorem cell23_2038073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 4, 2, 4].length) (baseStart_2038073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038073 prefixEnd_2038073 := by exact prefixLift 2038073
  have htrace : WordTrace (prefixWord ++ tailWord_2038073) baseStart_2038073 baseEnd_2038073 := by
    simpa [prefixWord, tailWord_2038073, baseEnd_2038073] using wordTrace_append hprefix tailTrace_2038073
  have hstable : (prefixWord ++ tailWord_2038073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038073).length < 2 ^ (prefixWord ++ tailWord_2038073).sum := by decide
  have hdescent : baseEnd_2038073 < baseStart_2038073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038096 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3]
def baseStart_2038096 : Nat := 118140960795 + 2038096 * 2 ^ 59
def prefixEnd_2038096 : Nat := 4983230072969 + 3 ^ 40 * 2038096 * 2
def baseEnd_2038096 : Nat := 1046522868005963173726973

theorem tailTrace_2038096 : CollatzResearch.WordTrace tailWord_2038096 prefixEnd_2038096 1046522868005963173726973 := by
  unfold tailWord_2038096
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167734012166872964959071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49556978682889163953278761 37167734012166872964959071)
  ·
    refine ⟨55751601018250309447438607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37167734012166872964959071 55751601018250309447438607)
    ·
      refine ⟨83627401527375464171157911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55751601018250309447438607 83627401527375464171157911)
      ·
        refine ⟨125441102291063196256736867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83627401527375464171157911 125441102291063196256736867)
        ·
          refine ⟨188161653436594794385105301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125441102291063196256736867 188161653436594794385105301)
          ·
            refine ⟨8820077504840380986801811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188161653436594794385105301 8820077504840380986801811)
            ·
              refine ⟨13230116257260571480202717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820077504840380986801811 13230116257260571480202717)
              ·
                refine ⟨4961293596472714305076019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13230116257260571480202717 4961293596472714305076019)
                ·
                  refine ⟨7441940394709071457614029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961293596472714305076019 7441940394709071457614029)
                  ·
                    refine ⟨2790727648015901796605261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7441940394709071457614029 2790727648015901796605261)
                    ·
                      refine ⟨1046522868005963173726973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2790727648015901796605261 1046522868005963173726973)
                      ·
                        rfl

theorem cell23_2038096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_2038096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038096 prefixEnd_2038096 := by exact prefixLift 2038096
  have htrace : WordTrace (prefixWord ++ tailWord_2038096) baseStart_2038096 baseEnd_2038096 := by
    simpa [prefixWord, tailWord_2038096, baseEnd_2038096] using wordTrace_append hprefix tailTrace_2038096
  have hstable : (prefixWord ++ tailWord_2038096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038096).length < 2 ^ (prefixWord ++ tailWord_2038096).sum := by decide
  have hdescent : baseEnd_2038096 < baseStart_2038096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038114 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2038114 : Nat := 118140960795 + 2038114 * 2 ^ 59
def prefixEnd_2038114 : Nat := 4983230072969 + 3 ^ 40 * 2038114 * 2
def baseEnd_2038114 : Nat := 1046532110657744103301891

theorem tailTrace_2038114 : CollatzResearch.WordTrace tailWord_2038114 prefixEnd_2038114 1046532110657744103301891 := by
  unfold tailWord_2038114
  simp only [CollatzResearch.WordTrace]
  refine ⟨18584031134567133751018349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49557416358845690002715597 18584031134567133751018349)
  ·
    refine ⟨6969011675462675156631881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18584031134567133751018349 6969011675462675156631881)
    ·
      refine ⟨5226758756597006367473911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6969011675462675156631881 5226758756597006367473911)
      ·
        refine ⟨7840138134895509551210867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5226758756597006367473911 7840138134895509551210867)
        ·
          refine ⟨11760207202343264326816301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840138134895509551210867 11760207202343264326816301)
          ·
            refine ⟨4410077700878724122556113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11760207202343264326816301 4410077700878724122556113)
            ·
              refine ⟨3307558275659043091917085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410077700878724122556113 3307558275659043091917085)
              ·
                refine ⟨1240334353372141159468907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3307558275659043091917085 1240334353372141159468907)
                ·
                  refine ⟨1860501530058211739203361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240334353372141159468907 1860501530058211739203361)
                  ·
                    refine ⟨1395376147543658804402521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860501530058211739203361 1395376147543658804402521)
                    ·
                      refine ⟨1046532110657744103301891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395376147543658804402521 1046532110657744103301891)
                      ·
                        rfl

theorem cell23_2038114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2038114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038114 prefixEnd_2038114 := by exact prefixLift 2038114
  have htrace : WordTrace (prefixWord ++ tailWord_2038114) baseStart_2038114 baseEnd_2038114 := by
    simpa [prefixWord, tailWord_2038114, baseEnd_2038114] using wordTrace_append hprefix tailTrace_2038114
  have hstable : (prefixWord ++ tailWord_2038114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038114).length < 2 ^ (prefixWord ++ tailWord_2038114).sum := by decide
  have hdescent : baseEnd_2038114 < baseStart_2038114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038123 : List Nat := [1, 1, 1, 1, 2, 2, 2, 7, 1, 3, 2]
def baseStart_2038123 : Nat := 118140960795 + 2038123 * 2 ^ 59
def prefixEnd_2038123 : Nat := 4983230072969 + 3 ^ 40 * 2038123 * 2
def baseEnd_2038123 : Nat := 1046536731983634568089349

theorem tailTrace_2038123 : CollatzResearch.WordTrace tailWord_2038123 prefixEnd_2038123 1046536731983634568089349 := by
  unfold tailWord_2038123
  simp only [CollatzResearch.WordTrace]
  refine ⟨74336452795235929541151023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49557635196823953027434015 74336452795235929541151023)
  ·
    refine ⟨111504679192853894311726535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74336452795235929541151023 111504679192853894311726535)
    ·
      refine ⟨167257018789280841467589803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111504679192853894311726535 167257018789280841467589803)
      ·
        refine ⟨250885528183921262201384705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167257018789280841467589803 250885528183921262201384705)
        ·
          refine ⟨188164146137940946651038529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250885528183921262201384705 188164146137940946651038529)
          ·
            refine ⟨141123109603455709988278897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188164146137940946651038529 141123109603455709988278897)
            ·
              refine ⟨105842332202591782491209173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141123109603455709988278897 105842332202591782491209173)
              ·
                refine ⟨2480679660998244902137715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105842332202591782491209173 2480679660998244902137715)
                ·
                  refine ⟨3721019491497367353206573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480679660998244902137715 3721019491497367353206573)
                  ·
                    refine ⟨1395382309311512757452465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721019491497367353206573 1395382309311512757452465)
                    ·
                      refine ⟨1046536731983634568089349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395382309311512757452465 1046536731983634568089349)
                      ·
                        rfl

theorem cell23_2038123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 3, 2].length) (baseStart_2038123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038123 prefixEnd_2038123 := by exact prefixLift 2038123
  have htrace : WordTrace (prefixWord ++ tailWord_2038123) baseStart_2038123 baseEnd_2038123 := by
    simpa [prefixWord, tailWord_2038123, baseEnd_2038123] using wordTrace_append hprefix tailTrace_2038123
  have hstable : (prefixWord ++ tailWord_2038123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038123).length < 2 ^ (prefixWord ++ tailWord_2038123).sum := by decide
  have hdescent : baseEnd_2038123 < baseStart_2038123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038130 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2038130 : Nat := 118140960795 + 2038130 * 2 ^ 59
def prefixEnd_2038130 : Nat := 4983230072969 + 3 ^ 40 * 2038130 * 2
def baseEnd_2038130 : Nat := 1046540326348216040701817

theorem tailTrace_2038130 : CollatzResearch.WordTrace tailWord_2038130 prefixEnd_2038130 1046540326348216040701817 := by
  unfold tailWord_2038130
  simp only [CollatzResearch.WordTrace]
  refine ⟨18584177026552642434163961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49557805404140379824437229 18584177026552642434163961)
  ·
    refine ⟨13938132769914481825622971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18584177026552642434163961 13938132769914481825622971)
    ·
      refine ⟨20907199154871722738434457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13938132769914481825622971 20907199154871722738434457)
      ·
        refine ⟨15680399366153792053825843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20907199154871722738434457 15680399366153792053825843)
        ·
          refine ⟨23520599049230688080738765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15680399366153792053825843 23520599049230688080738765)
          ·
            refine ⟨8820224643461508030277037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23520599049230688080738765 8820224643461508030277037)
            ·
              refine ⟨3307584241298065511353889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8820224643461508030277037 3307584241298065511353889)
              ·
                refine ⟨2480688180973549133515417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307584241298065511353889 2480688180973549133515417)
                ·
                  refine ⟨1860516135730161850136563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480688180973549133515417 1860516135730161850136563)
                  ·
                    refine ⟨2790774203595242775204845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1860516135730161850136563 2790774203595242775204845)
                    ·
                      refine ⟨1046540326348216040701817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2790774203595242775204845 1046540326348216040701817)
                      ·
                        rfl

theorem cell23_2038130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2038130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038130 prefixEnd_2038130 := by exact prefixLift 2038130
  have htrace : WordTrace (prefixWord ++ tailWord_2038130) baseStart_2038130 baseEnd_2038130 := by
    simpa [prefixWord, tailWord_2038130, baseEnd_2038130] using wordTrace_append hprefix tailTrace_2038130
  have hstable : (prefixWord ++ tailWord_2038130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038130).length < 2 ^ (prefixWord ++ tailWord_2038130).sum := by decide
  have hdescent : baseEnd_2038130 < baseStart_2038130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038136 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 10, 2]
def baseStart_2038136 : Nat := 118140960795 + 2038136 * 2 ^ 59
def prefixEnd_2038136 : Nat := 4983230072969 + 3 ^ 40 * 2038136 * 2
def baseEnd_2038136 : Nat := 1046543407232143017226789

theorem tailTrace_2038136 : CollatzResearch.WordTrace tailWord_2038136 prefixEnd_2038136 1046543407232143017226789 := by
  unfold tailWord_2038136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37168463472094416380687131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49557951296125888507582841 37168463472094416380687131)
  ·
    refine ⟨55752695208141624571030697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37168463472094416380687131 55752695208141624571030697)
    ·
      refine ⟨41814521406106218428273023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55752695208141624571030697 41814521406106218428273023)
      ·
        refine ⟨62721782109159327642409535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41814521406106218428273023 62721782109159327642409535)
        ·
          refine ⟨94082673163738991463614303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62721782109159327642409535 94082673163738991463614303)
          ·
            refine ⟨141124009745608487195421455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94082673163738991463614303 141124009745608487195421455)
            ·
              refine ⟨211686014618412730793132183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141124009745608487195421455 211686014618412730793132183)
              ·
                refine ⟨317529021927619096189698275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211686014618412730793132183 317529021927619096189698275)
                ·
                  refine ⟨476293532891428644284547413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317529021927619096189698275 476293532891428644284547413)
                  ·
                    refine ⟨1395391209642857356302385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 476293532891428644284547413 1395391209642857356302385)
                    ·
                      refine ⟨1046543407232143017226789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395391209642857356302385 1046543407232143017226789)
                      ·
                        rfl

theorem cell23_2038136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_2038136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038136 prefixEnd_2038136 := by exact prefixLift 2038136
  have htrace : WordTrace (prefixWord ++ tailWord_2038136) baseStart_2038136 baseEnd_2038136 := by
    simpa [prefixWord, tailWord_2038136, baseEnd_2038136] using wordTrace_append hprefix tailTrace_2038136
  have hstable : (prefixWord ++ tailWord_2038136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038136).length < 2 ^ (prefixWord ++ tailWord_2038136).sum := by decide
  have hdescent : baseEnd_2038136 < baseStart_2038136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038147 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 2, 1, 3]
def baseStart_2038147 : Nat := 118140960795 + 2038147 * 2 ^ 59
def prefixEnd_2038147 : Nat := 4983230072969 + 3 ^ 40 * 2038147 * 2
def baseEnd_2038147 : Nat := 1046549055519342474189239

theorem tailTrace_2038147 : CollatzResearch.WordTrace tailWord_2038147 prefixEnd_2038147 1046549055519342474189239 := by
  unfold tailWord_2038147
  simp only [CollatzResearch.WordTrace]
  refine ⟨74337328147148981640024695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49558218764765987760016463 74337328147148981640024695)
  ·
    refine ⟨111505992220723472460037043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74337328147148981640024695 111505992220723472460037043)
    ·
      refine ⟨167258988331085208690055565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111505992220723472460037043 167258988331085208690055565)
      ·
        refine ⟨62722120624156953258770837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167258988331085208690055565 62722120624156953258770837)
        ·
          refine ⟨2940099404257357184004883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62722120624156953258770837 2940099404257357184004883)
          ·
            refine ⟨4410149106386035776007325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940099404257357184004883 4410149106386035776007325)
            ·
              refine ⟨1653805914894763416002747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4410149106386035776007325 1653805914894763416002747)
              ·
                refine ⟨2480708872342145124004121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653805914894763416002747 2480708872342145124004121)
                ·
                  refine ⟨1860531654256608843003091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480708872342145124004121 1860531654256608843003091)
                  ·
                    refine ⟨2790797481384913264504637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1860531654256608843003091 2790797481384913264504637)
                    ·
                      refine ⟨1046549055519342474189239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2790797481384913264504637 1046549055519342474189239)
                      ·
                        rfl

theorem cell23_2038147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_2038147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038147 prefixEnd_2038147 := by exact prefixLift 2038147
  have htrace : WordTrace (prefixWord ++ tailWord_2038147) baseStart_2038147 baseEnd_2038147 := by
    simpa [prefixWord, tailWord_2038147, baseEnd_2038147] using wordTrace_append hprefix tailTrace_2038147
  have hstable : (prefixWord ++ tailWord_2038147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038147).length < 2 ^ (prefixWord ++ tailWord_2038147).sum := by decide
  have hdescent : baseEnd_2038147 < baseStart_2038147 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038170 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2]
def baseStart_2038170 : Nat := 118140960795 + 2038170 * 2 ^ 59
def prefixEnd_2038170 : Nat := 4983230072969 + 3 ^ 40 * 2038170 * 2
def baseEnd_2038170 : Nat := 1046560865574395884201633

theorem tailTrace_2038170 : CollatzResearch.WordTrace tailWord_2038170 prefixEnd_2038170 1046560865574395884201633 := by
  unfold tailWord_2038170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18584541756516414142027991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49558778017377104378741309 18584541756516414142027991)
  ·
    refine ⟨27876812634774621213041987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18584541756516414142027991 27876812634774621213041987)
    ·
      refine ⟨41815218952161931819562981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27876812634774621213041987 41815218952161931819562981)
      ·
        refine ⟨7840353553530362216168059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41815218952161931819562981 7840353553530362216168059)
        ·
          refine ⟨11760530330295543324252089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840353553530362216168059 11760530330295543324252089)
          ·
            refine ⟨8820397747721657493189067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11760530330295543324252089 8820397747721657493189067)
            ·
              refine ⟨13230596621582486239783601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820397747721657493189067 13230596621582486239783601)
              ·
                refine ⟨9922947466186864679837701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13230596621582486239783601 9922947466186864679837701)
                ·
                  refine ⟨1860552649910037127469569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9922947466186864679837701 1860552649910037127469569)
                  ·
                    refine ⟨1395414487432527845602177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860552649910037127469569 1395414487432527845602177)
                    ·
                      refine ⟨1046560865574395884201633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395414487432527845602177 1046560865574395884201633)
                      ·
                        rfl

theorem cell23_2038170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_2038170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038170 prefixEnd_2038170 := by exact prefixLift 2038170
  have htrace : WordTrace (prefixWord ++ tailWord_2038170) baseStart_2038170 baseEnd_2038170 := by
    simpa [prefixWord, tailWord_2038170, baseEnd_2038170] using wordTrace_append hprefix tailTrace_2038170
  have hstable : (prefixWord ++ tailWord_2038170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038170).length < 2 ^ (prefixWord ++ tailWord_2038170).sum := by decide
  have hdescent : baseEnd_2038170 < baseStart_2038170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038173 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2038173 : Nat := 118140960795 + 2038173 * 2 ^ 59
def prefixEnd_2038173 : Nat := 4983230072969 + 3 ^ 40 * 2038173 * 2
def baseEnd_2038173 : Nat := 1046562406016359372464119

theorem tailTrace_2038173 : CollatzResearch.WordTrace tailWord_2038173 prefixEnd_2038173 1046562406016359372464119 := by
  unfold tailWord_2038173
  simp only [CollatzResearch.WordTrace]
  refine ⟨74338276445054788080471173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49558850963369858720314115 74338276445054788080471173)
  ·
    refine ⟨13938426833447772765088345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74338276445054788080471173 13938426833447772765088345)
    ·
      refine ⟨10453820125085829573816259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13938426833447772765088345 10453820125085829573816259)
      ·
        refine ⟨15680730187628744360724389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453820125085829573816259 15680730187628744360724389)
        ·
          refine ⟨2940136910180389567635823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15680730187628744360724389 2940136910180389567635823)
          ·
            refine ⟨4410205365270584351453735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940136910180389567635823 4410205365270584351453735)
            ·
              refine ⟨6615308047905876527180603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410205365270584351453735 6615308047905876527180603)
              ·
                refine ⟨9922962071858814790770905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615308047905876527180603 9922962071858814790770905)
                ·
                  refine ⟨7442221553894111093078179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9922962071858814790770905 7442221553894111093078179)
                  ·
                    refine ⟨11163332330841166639617269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442221553894111093078179 11163332330841166639617269)
                    ·
                      refine ⟨1046562406016359372464119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11163332330841166639617269 1046562406016359372464119)
                      ·
                        rfl

theorem cell23_2038173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2038173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038173 prefixEnd_2038173 := by exact prefixLift 2038173
  have htrace : WordTrace (prefixWord ++ tailWord_2038173) baseStart_2038173 baseEnd_2038173 := by
    simpa [prefixWord, tailWord_2038173, baseEnd_2038173] using wordTrace_append hprefix tailTrace_2038173
  have hstable : (prefixWord ++ tailWord_2038173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038173).length < 2 ^ (prefixWord ++ tailWord_2038173).sum := by decide
  have hdescent : baseEnd_2038173 < baseStart_2038173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038193 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 7]
def baseStart_2038193 : Nat := 118140960795 + 2038193 * 2 ^ 59
def prefixEnd_2038193 : Nat := 4983230072969 + 3 ^ 40 * 2038193 * 2
def baseEnd_2038193 : Nat := 116285852847716588246003

theorem tailTrace_2038193 : CollatzResearch.WordTrace tailWord_2038193 prefixEnd_2038193 116285852847716588246003 := by
  unfold tailWord_2038193
  simp only [CollatzResearch.WordTrace]
  refine ⟨74339005904982331496199233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49559337269988220997466155 74339005904982331496199233)
  ·
    refine ⟨55754254428736748622149425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74339005904982331496199233 55754254428736748622149425)
    ·
      refine ⟨41815690821552561466612069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55754254428736748622149425 41815690821552561466612069)
      ·
        refine ⟨7840442029041105274989763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41815690821552561466612069 7840442029041105274989763)
        ·
          refine ⟨11760663043561657912484645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7840442029041105274989763 11760663043561657912484645)
          ·
            refine ⟨2205124320667810858590871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11760663043561657912484645 2205124320667810858590871)
            ·
              refine ⟨3307686481001716287886307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205124320667810858590871 3307686481001716287886307)
              ·
                refine ⟨4961529721502574431829461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307686481001716287886307 4961529721502574431829461)
                ·
                  refine ⟨116285852847716588246003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4961529721502574431829461 116285852847716588246003)
                  ·
                    rfl

theorem cell23_2038193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 7].length) (baseStart_2038193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038193 prefixEnd_2038193 := by exact prefixLift 2038193
  have htrace : WordTrace (prefixWord ++ tailWord_2038193) baseStart_2038193 baseEnd_2038193 := by
    simpa [prefixWord, tailWord_2038193, baseEnd_2038193] using wordTrace_append hprefix tailTrace_2038193
  have hstable : (prefixWord ++ tailWord_2038193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038193).length < 2 ^ (prefixWord ++ tailWord_2038193).sum := by decide
  have hdescent : baseEnd_2038193 < baseStart_2038193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038204 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_2038204 : Nat := 118140960795 + 2038204 * 2 ^ 59
def prefixEnd_2038204 : Nat := 4983230072969 + 3 ^ 40 * 2038204 * 2
def baseEnd_2038204 : Nat := 1046578323916648751176477

theorem tailTrace_2038204 : CollatzResearch.WordTrace tailWord_2038204 prefixEnd_2038204 1046578323916648751176477 := by
  unfold tailWord_2038204
  simp only [CollatzResearch.WordTrace]
  refine ⟨37169703553971240187424833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49559604738628320249899777 37169703553971240187424833)
  ·
    refine ⟨27877277665478430140568625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37169703553971240187424833 27877277665478430140568625)
    ·
      refine ⟨20907958249108822605426469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27877277665478430140568625 20907958249108822605426469)
      ·
        refine ⟨3920242171707904238517463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20907958249108822605426469 3920242171707904238517463)
        ·
          refine ⟨5880363257561856357776195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920242171707904238517463 5880363257561856357776195)
          ·
            refine ⟨8820544886342784536664293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880363257561856357776195 8820544886342784536664293)
            ·
              refine ⟨1653852166189272100624555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8820544886342784536664293 1653852166189272100624555)
              ·
                refine ⟨2480778249283908150936833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1653852166189272100624555 2480778249283908150936833)
                ·
                  refine ⟨1860583686962931113202625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2480778249283908150936833 1860583686962931113202625)
                  ·
                    refine ⟨1395437765222198334901969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860583686962931113202625 1395437765222198334901969)
                    ·
                      refine ⟨1046578323916648751176477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395437765222198334901969 1046578323916648751176477)
                      ·
                        rfl

theorem cell23_2038204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_2038204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038204 prefixEnd_2038204 := by exact prefixLift 2038204
  have htrace : WordTrace (prefixWord ++ tailWord_2038204) baseStart_2038204 baseEnd_2038204 := by
    simpa [prefixWord, tailWord_2038204, baseEnd_2038204] using wordTrace_append hprefix tailTrace_2038204
  have hstable : (prefixWord ++ tailWord_2038204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038204).length < 2 ^ (prefixWord ++ tailWord_2038204).sum := by decide
  have hdescent : baseEnd_2038204 < baseStart_2038204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038206 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2038206 : Nat := 118140960795 + 2038206 * 2 ^ 59
def prefixEnd_2038206 : Nat := 4983230072969 + 3 ^ 40 * 2038206 * 2
def baseEnd_2038206 : Nat := 348859783625985914450489

theorem tailTrace_2038206 : CollatzResearch.WordTrace tailWord_2038206 prefixEnd_2038206 348859783625985914450489 := by
  unfold tailWord_2038206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292435006741904339552809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49559653369290156477614981 9292435006741904339552809)
  ·
    refine ⟨6969326255056428254664607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9292435006741904339552809 6969326255056428254664607)
    ·
      refine ⟨10453989382584642381996911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969326255056428254664607 10453989382584642381996911)
      ·
        refine ⟨15680984073876963572995367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453989382584642381996911 15680984073876963572995367)
        ·
          refine ⟨23521476110815445359493051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15680984073876963572995367 23521476110815445359493051)
          ·
            refine ⟨35282214166223168039239577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23521476110815445359493051 35282214166223168039239577)
            ·
              refine ⟨26461660624667376029429683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35282214166223168039239577 26461660624667376029429683)
              ·
                refine ⟨39692490937001064044144525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26461660624667376029429683 39692490937001064044144525)
                ·
                  refine ⟨14884684101375399016554197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39692490937001064044144525 14884684101375399016554197)
                  ·
                    refine ⟨348859783625985914450489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14884684101375399016554197 348859783625985914450489)
                    ·
                      rfl

theorem cell23_2038206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2038206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038206 prefixEnd_2038206 := by exact prefixLift 2038206
  have htrace : WordTrace (prefixWord ++ tailWord_2038206) baseStart_2038206 baseEnd_2038206 := by
    simpa [prefixWord, tailWord_2038206, baseEnd_2038206] using wordTrace_append hprefix tailTrace_2038206
  have hstable : (prefixWord ++ tailWord_2038206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038206).length < 2 ^ (prefixWord ++ tailWord_2038206).sum := by decide
  have hdescent : baseEnd_2038206 < baseStart_2038206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038274 : List Nat := [3, 4, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_2038274 : Nat := 118140960795 + 2038274 * 2 ^ 59
def prefixEnd_2038274 : Nat := 4983230072969 + 3 ^ 40 * 2038274 * 2
def baseEnd_2038274 : Nat := 348871422520821159100385

theorem tailTrace_2038274 : CollatzResearch.WordTrace tailWord_2038274 prefixEnd_2038274 348871422520821159100385 := by
  unfold tailWord_2038274
  simp only [CollatzResearch.WordTrace]
  refine ⟨18585490054422220582474469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49561306811792588219931917 18585490054422220582474469)
  ·
    refine ⟨3484779385204166359213963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18585490054422220582474469 3484779385204166359213963)
    ·
      refine ⟨5227169077806249538820945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3484779385204166359213963 5227169077806249538820945)
      ·
        refine ⟨3920376808354687154115709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5227169077806249538820945 3920376808354687154115709)
        ·
          refine ⟨1470141303133007682793391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3920376808354687154115709 1470141303133007682793391)
          ·
            refine ⟨2205211954699511524190087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470141303133007682793391 2205211954699511524190087)
            ·
              refine ⟨3307817932049267286285131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205211954699511524190087 3307817932049267286285131)
              ·
                refine ⟨4961726898073900929427697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307817932049267286285131 4961726898073900929427697)
                ·
                  refine ⟨3721295173555425697070773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4961726898073900929427697 3721295173555425697070773)
                  ·
                    refine ⟨348871422520821159100385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3721295173555425697070773 348871422520821159100385)
                    ·
                      rfl

theorem cell23_2038274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_2038274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038274 prefixEnd_2038274 := by exact prefixLift 2038274
  have htrace : WordTrace (prefixWord ++ tailWord_2038274) baseStart_2038274 baseEnd_2038274 := by
    simpa [prefixWord, tailWord_2038274, baseEnd_2038274] using wordTrace_append hprefix tailTrace_2038274
  have hstable : (prefixWord ++ tailWord_2038274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038274).length < 2 ^ (prefixWord ++ tailWord_2038274).sum := by decide
  have hdescent : baseEnd_2038274 < baseStart_2038274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038300 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 6]
def baseStart_2038300 : Nat := 118140960795 + 2038300 * 2 ^ 59
def prefixEnd_2038300 : Nat := 4983230072969 + 3 ^ 40 * 2038300 * 2
def baseEnd_2038300 : Nat := 116291957562164486175115

theorem tailTrace_2038300 : CollatzResearch.WordTrace tailWord_2038300 prefixEnd_2038300 116291957562164486175115 := by
  unfold tailWord_2038300
  simp only [CollatzResearch.WordTrace]
  refine ⟨37171454257797344385172177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49561939010396459180229569 37171454257797344385172177)
  ·
    refine ⟨27878590693348008288879133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37171454257797344385172177 27878590693348008288879133)
    ·
      refine ⟨10454471510005503108329675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27878590693348008288879133 10454471510005503108329675)
      ·
        refine ⟨15681707265008254662494513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454471510005503108329675 15681707265008254662494513)
        ·
          refine ⟨11761280448756190996870885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15681707265008254662494513 11761280448756190996870885)
          ·
            refine ⟨2205240084141785811913291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11761280448756190996870885 2205240084141785811913291)
            ·
              refine ⟨3307860126212678717869937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205240084141785811913291 3307860126212678717869937)
              ·
                refine ⟨2480895094659509038402453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307860126212678717869937 2480895094659509038402453)
                ·
                  refine ⟨116291957562164486175115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2480895094659509038402453 116291957562164486175115)
                  ·
                    rfl

theorem cell23_2038300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_2038300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038300 prefixEnd_2038300 := by exact prefixLift 2038300
  have htrace : WordTrace (prefixWord ++ tailWord_2038300) baseStart_2038300 baseEnd_2038300 := by
    simpa [prefixWord, tailWord_2038300, baseEnd_2038300] using wordTrace_append hprefix tailTrace_2038300
  have hstable : (prefixWord ++ tailWord_2038300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038300).length < 2 ^ (prefixWord ++ tailWord_2038300).sum := by decide
  have hdescent : baseEnd_2038300 < baseStart_2038300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038330 : List Nat := [3, 1, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_2038330 : Nat := 118140960795 + 2038330 * 2 ^ 59
def prefixEnd_2038330 : Nat := 4983230072969 + 3 ^ 40 * 2038330 * 2
def baseEnd_2038330 : Nat := 348881007493038419400299

theorem tailTrace_2038330 : CollatzResearch.WordTrace tailWord_2038330 prefixEnd_2038330 348881007493038419400299 := by
  unfold tailWord_2038330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18586000676371500973484111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49562668470324002595957629 18586000676371500973484111)
  ·
    refine ⟨27879001014557251460226167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18586000676371500973484111 27879001014557251460226167)
    ·
      refine ⟨41818501521835877190339251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27879001014557251460226167 41818501521835877190339251)
      ·
        refine ⟨62727752282753815785508877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41818501521835877190339251 62727752282753815785508877)
        ·
          refine ⟨23522907106032680919565829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62727752282753815785508877 23522907106032680919565829)
          ·
            refine ⟨4410545082381127672418593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23522907106032680919565829 4410545082381127672418593)
            ·
              refine ⟨3307908811785845754313945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410545082381127672418593 3307908811785845754313945)
              ·
                refine ⟨2480931608839384315735459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307908811785845754313945 2480931608839384315735459)
                ·
                  refine ⟨3721397413259076473603189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480931608839384315735459 3721397413259076473603189)
                  ·
                    refine ⟨348881007493038419400299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3721397413259076473603189 348881007493038419400299)
                    ·
                      rfl

theorem cell23_2038330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_2038330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038330 prefixEnd_2038330 := by exact prefixLift 2038330
  have htrace : WordTrace (prefixWord ++ tailWord_2038330) baseStart_2038330 baseEnd_2038330 := by
    simpa [prefixWord, tailWord_2038330, baseEnd_2038330] using wordTrace_append hprefix tailTrace_2038330
  have hstable : (prefixWord ++ tailWord_2038330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038330).length < 2 ^ (prefixWord ++ tailWord_2038330).sum := by decide
  have hdescent : baseEnd_2038330 < baseStart_2038330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038350 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_2038350 : Nat := 118140960795 + 2038350 * 2 ^ 59
def prefixEnd_2038350 : Nat := 4983230072969 + 3 ^ 40 * 2038350 * 2
def baseEnd_2038350 : Nat := 1046653292092205179950805

theorem tailTrace_2038350 : CollatzResearch.WordTrace tailWord_2038350 prefixEnd_2038350 1046653292092205179950805 := by
  unfold tailWord_2038350
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293091520676693413708063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49563154776942364873109669 9293091520676693413708063)
  ·
    refine ⟨13939637281015040120562095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9293091520676693413708063 13939637281015040120562095)
    ·
      refine ⟨20909455921522560180843143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13939637281015040120562095 20909455921522560180843143)
      ·
        refine ⟨31364183882283840271264715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20909455921522560180843143 31364183882283840271264715)
        ·
          refine ⟨47046275823425760406897073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31364183882283840271264715 47046275823425760406897073)
          ·
            refine ⟨35284706867569320305172805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47046275823425760406897073 35284706867569320305172805)
            ·
              refine ⟨6615882537669247557219901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35284706867569320305172805 6615882537669247557219901)
              ·
                refine ⟨2480955951625967833957463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6615882537669247557219901 2480955951625967833957463)
                ·
                  refine ⟨3721433927438951750936195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480955951625967833957463 3721433927438951750936195)
                  ·
                    refine ⟨5582150891158427626404293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721433927438951750936195 5582150891158427626404293)
                    ·
                      refine ⟨1046653292092205179950805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5582150891158427626404293 1046653292092205179950805)
                      ·
                        rfl

theorem cell23_2038350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_2038350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038350 prefixEnd_2038350 := by exact prefixLift 2038350
  have htrace : WordTrace (prefixWord ++ tailWord_2038350) baseStart_2038350 baseEnd_2038350 := by
    simpa [prefixWord, tailWord_2038350, baseEnd_2038350] using wordTrace_append hprefix tailTrace_2038350
  have hstable : (prefixWord ++ tailWord_2038350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038350).length < 2 ^ (prefixWord ++ tailWord_2038350).sum := by decide
  have hdescent : baseEnd_2038350 < baseStart_2038350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038353 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 5]
def baseStart_2038353 : Nat := 118140960795 + 2038353 * 2 ^ 59
def prefixEnd_2038353 : Nat := 4983230072969 + 3 ^ 40 * 2038353 * 2
def baseEnd_2038353 : Nat := 1046654832534168668213291

theorem tailTrace_2038353 : CollatzResearch.WordTrace tailWord_2038353 prefixEnd_2038353 1046654832534168668213291 := by
  unfold tailWord_2038353
  simp only [CollatzResearch.WordTrace]
  refine ⟨74344841584402678822023713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49563227722935119214682475 74344841584402678822023713)
  ·
    refine ⟨55758631188302009116517785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74344841584402678822023713 55758631188302009116517785)
    ·
      refine ⟨41818973391226506837388339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55758631188302009116517785 41818973391226506837388339)
      ·
        refine ⟨62728460086839760256082509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41818973391226506837388339 62728460086839760256082509)
        ·
          refine ⟨23523172532564910096030941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62728460086839760256082509 23523172532564910096030941)
          ·
            refine ⟨8821189699711841286011603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23523172532564910096030941 8821189699711841286011603)
            ·
              refine ⟨13231784549567761929017405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8821189699711841286011603 13231784549567761929017405)
              ·
                refine ⟨4961919206087910723381527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13231784549567761929017405 4961919206087910723381527)
                ·
                  refine ⟨7442878809131866085072291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961919206087910723381527 7442878809131866085072291)
                  ·
                    refine ⟨11164318213697799127608437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442878809131866085072291 11164318213697799127608437)
                    ·
                      refine ⟨1046654832534168668213291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11164318213697799127608437 1046654832534168668213291)
                      ·
                        rfl

theorem cell23_2038353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_2038353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038353 prefixEnd_2038353 := by exact prefixLift 2038353
  have htrace : WordTrace (prefixWord ++ tailWord_2038353) baseStart_2038353 baseEnd_2038353 := by
    simpa [prefixWord, tailWord_2038353, baseEnd_2038353] using wordTrace_append hprefix tailTrace_2038353
  have hstable : (prefixWord ++ tailWord_2038353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038353).length < 2 ^ (prefixWord ++ tailWord_2038353).sum := by decide
  have hdescent : baseEnd_2038353 < baseStart_2038353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038384 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 1, 1, 4]
def baseStart_2038384 : Nat := 118140960795 + 2038384 * 2 ^ 59
def prefixEnd_2038384 : Nat := 4983230072969 + 3 ^ 40 * 2038384 * 2
def baseEnd_2038384 : Nat := 1046670750434458046925649

theorem tailTrace_2038384 : CollatzResearch.WordTrace tailWord_2038384 prefixEnd_2038384 1046670750434458046925649 := by
  unfold tailWord_2038384
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172986123645185558201103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49563981498193580744268137 37172986123645185558201103)
  ·
    refine ⟨55759479185467778337301655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37172986123645185558201103 55759479185467778337301655)
    ·
      refine ⟨83639218778201667505952483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55759479185467778337301655 83639218778201667505952483)
      ·
        refine ⟨125458828167302501258928725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83639218778201667505952483 125458828167302501258928725)
        ·
          refine ⟨1470220642585576186628071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 125458828167302501258928725 1470220642585576186628071)
          ·
            refine ⟨2205330963878364279942107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470220642585576186628071 2205330963878364279942107)
            ·
              refine ⟨3307996445817546419913161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205330963878364279942107 3307996445817546419913161)
              ·
                refine ⟨2480997334363159814934871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307996445817546419913161 2480997334363159814934871)
                ·
                  refine ⟨3721496001544739722402307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480997334363159814934871 3721496001544739722402307)
                  ·
                    refine ⟨5582244002317109583603461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721496001544739722402307 5582244002317109583603461)
                    ·
                      refine ⟨1046670750434458046925649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5582244002317109583603461 1046670750434458046925649)
                      ·
                        rfl

theorem cell23_2038384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 1, 4].length) (baseStart_2038384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038384 prefixEnd_2038384 := by exact prefixLift 2038384
  have htrace : WordTrace (prefixWord ++ tailWord_2038384) baseStart_2038384 baseEnd_2038384 := by
    simpa [prefixWord, tailWord_2038384, baseEnd_2038384] using wordTrace_append hprefix tailTrace_2038384
  have hstable : (prefixWord ++ tailWord_2038384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038384).length < 2 ^ (prefixWord ++ tailWord_2038384).sum := by decide
  have hdescent : baseEnd_2038384 < baseStart_2038384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038400 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3]
def baseStart_2038400 : Nat := 118140960795 + 2038400 * 2 ^ 59
def prefixEnd_2038400 : Nat := 4983230072969 + 3 ^ 40 * 2038400 * 2
def baseEnd_2038400 : Nat := 1046678966124929984325575

theorem tailTrace_2038400 : CollatzResearch.WordTrace tailWord_2038400 prefixEnd_2038400 1046678966124929984325575 := by
  unfold tailWord_2038400
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173277907616202924492327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49564370543488270565989769 37173277907616202924492327)
  ·
    refine ⟨55759916861424304386738491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37173277907616202924492327 55759916861424304386738491)
    ·
      refine ⟨83639875292136456580107737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55759916861424304386738491 83639875292136456580107737)
      ·
        refine ⟨62729906469102342435080803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83639875292136456580107737 62729906469102342435080803)
        ·
          refine ⟨94094859703653513652621205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62729906469102342435080803 94094859703653513652621205)
          ·
            refine ⟨4410696548608758452466619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 94094859703653513652621205 4410696548608758452466619)
            ·
              refine ⟨6616044822913137678699929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410696548608758452466619 6616044822913137678699929)
              ·
                refine ⟨4962033617184853259024947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616044822913137678699929 4962033617184853259024947)
                ·
                  refine ⟨7443050425777279888537421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962033617184853259024947 7443050425777279888537421)
                  ·
                    refine ⟨2791143909666479958201533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7443050425777279888537421 2791143909666479958201533)
                    ·
                      refine ⟨1046678966124929984325575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2791143909666479958201533 1046678966124929984325575)
                      ·
                        rfl

theorem cell23_2038400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_2038400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038400 prefixEnd_2038400 := by exact prefixLift 2038400
  have htrace : WordTrace (prefixWord ++ tailWord_2038400) baseStart_2038400 baseEnd_2038400 := by
    simpa [prefixWord, tailWord_2038400, baseEnd_2038400] using wordTrace_append hprefix tailTrace_2038400
  have hstable : (prefixWord ++ tailWord_2038400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038400).length < 2 ^ (prefixWord ++ tailWord_2038400).sum := by decide
  have hdescent : baseEnd_2038400 < baseStart_2038400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038404 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 1, 2, 3]
def baseStart_2038404 : Nat := 118140960795 + 2038404 * 2 ^ 59
def prefixEnd_2038404 : Nat := 4983230072969 + 3 ^ 40 * 2038404 * 2
def baseEnd_2038404 : Nat := 1046681020047547968675557

theorem tailTrace_2038404 : CollatzResearch.WordTrace tailWord_2038404 prefixEnd_2038404 1046681020047547968675557 := by
  unfold tailWord_2038404
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173350853608957266065133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49564467804811943021420177 37173350853608957266065133)
  ·
    refine ⟨13940006570103358974774425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37173350853608957266065133 13940006570103358974774425)
    ·
      refine ⟨10455004927577519231080819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13940006570103358974774425 10455004927577519231080819)
      ·
        refine ⟨15682507391366278846621229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10455004927577519231080819 15682507391366278846621229)
        ·
          refine ⟨5880940271762354567482961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15682507391366278846621229 5880940271762354567482961)
          ·
            refine ⟨4410705203821765925612221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5880940271762354567482961 4410705203821765925612221)
            ·
              refine ⟨1654014451433162222104583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4410705203821765925612221 1654014451433162222104583)
              ·
                refine ⟨2481021677149743333156875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654014451433162222104583 2481021677149743333156875)
                ·
                  refine ⟨3721532515724614999735313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481021677149743333156875 3721532515724614999735313)
                  ·
                    refine ⟨2791149386793461249801485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3721532515724614999735313 2791149386793461249801485)
                    ·
                      refine ⟨1046681020047547968675557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2791149386793461249801485 1046681020047547968675557)
                      ·
                        rfl

theorem cell23_2038404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_2038404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038404 prefixEnd_2038404 := by exact prefixLift 2038404
  have htrace : WordTrace (prefixWord ++ tailWord_2038404) baseStart_2038404 baseEnd_2038404 := by
    simpa [prefixWord, tailWord_2038404, baseEnd_2038404] using wordTrace_append hprefix tailTrace_2038404
  have hstable : (prefixWord ++ tailWord_2038404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038404).length < 2 ^ (prefixWord ++ tailWord_2038404).sum := by decide
  have hdescent : baseEnd_2038404 < baseStart_2038404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038418 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 1, 2, 2]
def baseStart_2038418 : Nat := 118140960795 + 2038418 * 2 ^ 59
def prefixEnd_2038418 : Nat := 4983230072969 + 3 ^ 40 * 2038418 * 2
def baseEnd_2038418 : Nat := 1046688208776710913900493

theorem tailTrace_2038418 : CollatzResearch.WordTrace tailWord_2038418 prefixEnd_2038418 1046688208776710913900493 := by
  unfold tailWord_2038418
  simp only [CollatzResearch.WordTrace]
  refine ⟨18586803082291798730784977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49564808219444796615426605 18586803082291798730784977)
  ·
    refine ⟨13940102311718849048088733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18586803082291798730784977 13940102311718849048088733)
    ·
      refine ⟨5227538366894568393033275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13940102311718849048088733 5227538366894568393033275)
      ·
        refine ⟨7841307550341852589549913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5227538366894568393033275 7841307550341852589549913)
        ·
          refine ⟨5880980662756389442162435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7841307550341852589549913 5880980662756389442162435)
          ·
            refine ⟨8821470994134584163243653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880980662756389442162435 8821470994134584163243653)
            ·
              refine ⟨1654025811400234530608185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8821470994134584163243653 1654025811400234530608185)
              ·
                refine ⟨1240519358550175897956139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654025811400234530608185 1240519358550175897956139)
                ·
                  refine ⟨1860779037825263846934209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240519358550175897956139 1860779037825263846934209)
                  ·
                    refine ⟨1395584278368947885200657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860779037825263846934209 1395584278368947885200657)
                    ·
                      refine ⟨1046688208776710913900493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395584278368947885200657 1046688208776710913900493)
                      ·
                        rfl

theorem cell23_2038418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_2038418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038418 prefixEnd_2038418 := by exact prefixLift 2038418
  have htrace : WordTrace (prefixWord ++ tailWord_2038418) baseStart_2038418 baseEnd_2038418 := by
    simpa [prefixWord, tailWord_2038418, baseEnd_2038418] using wordTrace_append hprefix tailTrace_2038418
  have hstable : (prefixWord ++ tailWord_2038418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038418).length < 2 ^ (prefixWord ++ tailWord_2038418).sum := by decide
  have hdescent : baseEnd_2038418 < baseStart_2038418 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038420 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2038420 : Nat := 118140960795 + 2038420 * 2 ^ 59
def prefixEnd_2038420 : Nat := 4983230072969 + 3 ^ 40 * 2038420 * 2
def baseEnd_2038420 : Nat := 348896411912673302025161

theorem tailTrace_2038420 : CollatzResearch.WordTrace tailWord_2038420 prefixEnd_2038420 348896411912673302025161 := by
  unfold tailWord_2038420
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173642637579974632356357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49564856850106632843141809 37173642637579974632356357)
  ·
    refine ⟨6970057994546245243566817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37173642637579974632356357 6970057994546245243566817)
    ·
      refine ⟨5227543495909683932675113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6970057994546245243566817 5227543495909683932675113)
      ·
        refine ⟨3920657621932262949506335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5227543495909683932675113 3920657621932262949506335)
        ·
          refine ⟨5880986432898394424259503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920657621932262949506335 5880986432898394424259503)
          ·
            refine ⟨8821479649347591636389255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5880986432898394424259503 8821479649347591636389255)
            ·
              refine ⟨13232219474021387454583883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8821479649347591636389255 13232219474021387454583883)
              ·
                refine ⟨19848329211032081181875825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13232219474021387454583883 19848329211032081181875825)
                ·
                  refine ⟨14886246908274060886406869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19848329211032081181875825 14886246908274060886406869)
                  ·
                    refine ⟨348896411912673302025161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14886246908274060886406869 348896411912673302025161)
                    ·
                      rfl

theorem cell23_2038420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2038420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038420 prefixEnd_2038420 := by exact prefixLift 2038420
  have htrace : WordTrace (prefixWord ++ tailWord_2038420) baseStart_2038420 baseEnd_2038420 := by
    simpa [prefixWord, tailWord_2038420, baseEnd_2038420] using wordTrace_append hprefix tailTrace_2038420
  have hstable : (prefixWord ++ tailWord_2038420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038420).length < 2 ^ (prefixWord ++ tailWord_2038420).sum := by decide
  have hdescent : baseEnd_2038420 < baseStart_2038420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038423 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 4]
def baseStart_2038423 : Nat := 118140960795 + 2038423 * 2 ^ 59
def prefixEnd_2038423 : Nat := 4983230072969 + 3 ^ 40 * 2038423 * 2
def baseEnd_2038423 : Nat := 1046690776179983394337969

theorem tailTrace_2038423 : CollatzResearch.WordTrace tailWord_2038423 prefixEnd_2038423 1046690776179983394337969 := by
  unfold tailWord_2038423
  simp only [CollatzResearch.WordTrace]
  refine ⟨74347394694149080777071923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49564929796099387184714615 74347394694149080777071923)
  ·
    refine ⟨111521092041223621165607885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74347394694149080777071923 111521092041223621165607885)
    ·
      refine ⟨41820409515458857937102957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111521092041223621165607885 41820409515458857937102957)
      ·
        refine ⟨15682653568297071726413609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41820409515458857937102957 15682653568297071726413609)
        ·
          refine ⟨11761990176222803794810207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15682653568297071726413609 11761990176222803794810207)
          ·
            refine ⟨17642985264334205692215311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761990176222803794810207 17642985264334205692215311)
            ·
              refine ⟨26464477896501308538322967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642985264334205692215311 26464477896501308538322967)
              ·
                refine ⟨39696716844751962807484451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26464477896501308538322967 39696716844751962807484451)
                ·
                  refine ⟨59545075267127944211226677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39696716844751962807484451 59545075267127944211226677)
                  ·
                    refine ⟨5582350806293244769802501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59545075267127944211226677 5582350806293244769802501)
                    ·
                      refine ⟨1046690776179983394337969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5582350806293244769802501 1046690776179983394337969)
                      ·
                        rfl

theorem cell23_2038423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_2038423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038423 prefixEnd_2038423 := by exact prefixLift 2038423
  have htrace : WordTrace (prefixWord ++ tailWord_2038423) baseStart_2038423 baseEnd_2038423 := by
    simpa [prefixWord, tailWord_2038423, baseEnd_2038423] using wordTrace_append hprefix tailTrace_2038423
  have hstable : (prefixWord ++ tailWord_2038423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038423).length < 2 ^ (prefixWord ++ tailWord_2038423).sum := by decide
  have hdescent : baseEnd_2038423 < baseStart_2038423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038457 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 4, 2, 2]
def baseStart_2038457 : Nat := 118140960795 + 2038457 * 2 ^ 59
def prefixEnd_2038457 : Nat := 4983230072969 + 3 ^ 40 * 2038457 * 2
def baseEnd_2038457 : Nat := 1046708234522236261312813

theorem tailTrace_2038457 : CollatzResearch.WordTrace tailWord_2038457 prefixEnd_2038457 1046708234522236261312813 := by
  unfold tailWord_2038457
  simp only [CollatzResearch.WordTrace]
  refine ⟨74348634776025904583809625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49565756517350603055873083 74348634776025904583809625)
  ·
    refine ⟨55761476082019428437857219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74348634776025904583809625 55761476082019428437857219)
    ·
      refine ⟨83642214123029142656785829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55761476082019428437857219 83642214123029142656785829)
      ·
        refine ⟨15682915148067964248147343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83642214123029142656785829 15682915148067964248147343)
        ·
          refine ⟨23524372722101946372221015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15682915148067964248147343 23524372722101946372221015)
          ·
            refine ⟨35286559083152919558331523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23524372722101946372221015 35286559083152919558331523)
            ·
              refine ⟨52929838624729379337497285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35286559083152919558331523 52929838624729379337497285)
              ·
                refine ⟨9924344742136758625780741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52929838624729379337497285 9924344742136758625780741)
                ·
                  refine ⟨1860814639150642242333889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9924344742136758625780741 1860814639150642242333889)
                  ·
                    refine ⟨1395610979362981681750417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860814639150642242333889 1395610979362981681750417)
                    ·
                      refine ⟨1046708234522236261312813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395610979362981681750417 1046708234522236261312813)
                      ·
                        rfl

theorem cell23_2038457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 4, 2, 2].length) (baseStart_2038457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038457 prefixEnd_2038457 := by exact prefixLift 2038457
  have htrace : WordTrace (prefixWord ++ tailWord_2038457) baseStart_2038457 baseEnd_2038457 := by
    simpa [prefixWord, tailWord_2038457, baseEnd_2038457] using wordTrace_append hprefix tailTrace_2038457
  have hstable : (prefixWord ++ tailWord_2038457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038457).length < 2 ^ (prefixWord ++ tailWord_2038457).sum := by decide
  have hdescent : baseEnd_2038457 < baseStart_2038457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038461 : List Nat := [1, 4, 1, 2, 1, 5, 2, 1, 1, 3, 2]
def baseStart_2038461 : Nat := 118140960795 + 2038461 * 2 ^ 59
def prefixEnd_2038461 : Nat := 4983230072969 + 3 ^ 40 * 2038461 * 2
def baseEnd_2038461 : Nat := 1046710288444854245662795

theorem tailTrace_2038461 : CollatzResearch.WordTrace tailWord_2038461 prefixEnd_2038461 1046710288444854245662795 := by
  unfold tailWord_2038461
  simp only [CollatzResearch.WordTrace]
  refine ⟨74348780668011413266955237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49565853778674275511303491 74348780668011413266955237)
  ·
    refine ⟨13940396375252139987554107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74348780668011413266955237 13940396375252139987554107)
    ·
      refine ⟨20910594562878209981331161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13940396375252139987554107 20910594562878209981331161)
      ·
        refine ⟨15682945922158657485998371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20910594562878209981331161 15682945922158657485998371)
        ·
          refine ⟨23524418883237986228997557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15682945922158657485998371 23524418883237986228997557)
          ·
            refine ⟨2205414270303561208968521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23524418883237986228997557 2205414270303561208968521)
            ·
              refine ⟨1654060702727670906726391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205414270303561208968521 1654060702727670906726391)
              ·
                refine ⟨2481091054091506360089587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654060702727670906726391 2481091054091506360089587)
                ·
                  refine ⟨3721636581137259540134381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481091054091506360089587 3721636581137259540134381)
                  ·
                    refine ⟨1395613717926472327550393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3721636581137259540134381 1395613717926472327550393)
                    ·
                      refine ⟨1046710288444854245662795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395613717926472327550393 1046710288444854245662795)
                      ·
                        rfl

theorem cell23_2038461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_2038461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038461 prefixEnd_2038461 := by exact prefixLift 2038461
  have htrace : WordTrace (prefixWord ++ tailWord_2038461) baseStart_2038461 baseEnd_2038461 := by
    simpa [prefixWord, tailWord_2038461, baseEnd_2038461] using wordTrace_append hprefix tailTrace_2038461
  have hstable : (prefixWord ++ tailWord_2038461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038461).length < 2 ^ (prefixWord ++ tailWord_2038461).sum := by decide
  have hdescent : baseEnd_2038461 < baseStart_2038461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038474 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_2038474 : Nat := 118140960795 + 2038474 * 2 ^ 59
def prefixEnd_2038474 : Nat := 4983230072969 + 3 ^ 40 * 2038474 * 2
def baseEnd_2038474 : Nat := 1046716963693362694800235

theorem tailTrace_2038474 : CollatzResearch.WordTrace tailWord_2038474 prefixEnd_2038474 1046716963693362694800235 := by
  unfold tailWord_2038474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587313704241079121794619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49566169877976210991452317 18587313704241079121794619)
  ·
    refine ⟨27880970556361618682691929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18587313704241079121794619 27880970556361618682691929)
    ·
      refine ⟨20910727917271214012018947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27880970556361618682691929 20910727917271214012018947)
      ·
        refine ⟨31366091875906821018028421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20910727917271214012018947 31366091875906821018028421)
        ·
          refine ⟨5881142226732528940880329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31366091875906821018028421 5881142226732528940880329)
          ·
            refine ⟨4410856670049396705660247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5881142226732528940880329 4410856670049396705660247)
            ·
              refine ⟨6616285005074095058490371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410856670049396705660247 6616285005074095058490371)
              ·
                refine ⟨9924427507611142587735557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616285005074095058490371 9924427507611142587735557)
                ·
                  refine ⟨1860830157677089235200417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9924427507611142587735557 1860830157677089235200417)
                  ·
                    refine ⟨1395622618257816926400313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1860830157677089235200417 1395622618257816926400313)
                    ·
                      refine ⟨1046716963693362694800235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395622618257816926400313 1046716963693362694800235)
                      ·
                        rfl

theorem cell23_2038474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_2038474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038474 prefixEnd_2038474 := by exact prefixLift 2038474
  have htrace : WordTrace (prefixWord ++ tailWord_2038474) baseStart_2038474 baseEnd_2038474 := by
    simpa [prefixWord, tailWord_2038474, baseEnd_2038474] using wordTrace_append hprefix tailTrace_2038474
  have hstable : (prefixWord ++ tailWord_2038474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038474).length < 2 ^ (prefixWord ++ tailWord_2038474).sum := by decide
  have hdescent : baseEnd_2038474 < baseStart_2038474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038490 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_2038490 : Nat := 118140960795 + 2038490 * 2 ^ 59
def prefixEnd_2038490 : Nat := 4983230072969 + 3 ^ 40 * 2038490 * 2
def baseEnd_2038490 : Nat := 1046725179383834632200161

theorem tailTrace_2038490 : CollatzResearch.WordTrace tailWord_2038490 prefixEnd_2038490 1046725179383834632200161 := by
  unfold tailWord_2038490
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587459596226587804940231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49566558923270900813173949 18587459596226587804940231)
  ·
    refine ⟨27881189394339881707410347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18587459596226587804940231 27881189394339881707410347)
    ·
      refine ⟨41821784091509822561115521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27881189394339881707410347 41821784091509822561115521)
      ·
        refine ⟨31366338068632366920836641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41821784091509822561115521 31366338068632366920836641)
        ·
          refine ⟨23524753551474275190627481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31366338068632366920836641 23524753551474275190627481)
          ·
            refine ⟨17643565163605706392970611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23524753551474275190627481 17643565163605706392970611)
            ·
              refine ⟨26465347745408559589455917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17643565163605706392970611 26465347745408559589455917)
              ·
                refine ⟨9924505404528209846045969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26465347745408559589455917 9924505404528209846045969)
                ·
                  refine ⟨7443379053396157384534477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9924505404528209846045969 7443379053396157384534477)
                  ·
                    refine ⟨2791267145023559019200429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7443379053396157384534477 2791267145023559019200429)
                    ·
                      refine ⟨1046725179383834632200161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2791267145023559019200429 1046725179383834632200161)
                      ·
                        rfl

theorem cell23_2038490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_2038490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038490 prefixEnd_2038490 := by exact prefixLift 2038490
  have htrace : WordTrace (prefixWord ++ tailWord_2038490) baseStart_2038490 baseEnd_2038490 := by
    simpa [prefixWord, tailWord_2038490, baseEnd_2038490] using wordTrace_append hprefix tailTrace_2038490
  have hstable : (prefixWord ++ tailWord_2038490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038490).length < 2 ^ (prefixWord ++ tailWord_2038490).sum := by decide
  have hdescent : baseEnd_2038490 < baseStart_2038490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038510 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2038510 : Nat := 118140960795 + 2038510 * 2 ^ 59
def prefixEnd_2038510 : Nat := 4983230072969 + 3 ^ 40 * 2038510 * 2
def baseEnd_2038510 : Nat := 348911816332308184650023

theorem tailTrace_2038510 : CollatzResearch.WordTrace tailWord_2038510 prefixEnd_2038510 348911816332308184650023 := by
  unfold tailWord_2038510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293820980604236829436123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49567045229889263090325989 9293820980604236829436123)
  ·
    refine ⟨13940731470906355244154185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9293820980604236829436123 13940731470906355244154185)
    ·
      refine ⟨10455548603179766433115639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13940731470906355244154185 10455548603179766433115639)
      ·
        refine ⟨15683322904769649649673459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10455548603179766433115639 15683322904769649649673459)
        ·
          refine ⟨23524984357154474474510189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15683322904769649649673459 23524984357154474474510189)
          ·
            refine ⟨8821869133932927927941321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23524984357154474474510189 8821869133932927927941321)
            ·
              refine ⟨6616401850449695945955991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821869133932927927941321 6616401850449695945955991)
              ·
                refine ⟨9924602775674543918933987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616401850449695945955991 9924602775674543918933987)
                ·
                  refine ⟨14886904163511815878400981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9924602775674543918933987 14886904163511815878400981)
                  ·
                    refine ⟨348911816332308184650023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14886904163511815878400981 348911816332308184650023)
                    ·
                      rfl

theorem cell23_2038510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2038510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038510 prefixEnd_2038510 := by exact prefixLift 2038510
  have htrace : WordTrace (prefixWord ++ tailWord_2038510) baseStart_2038510 baseEnd_2038510 := by
    simpa [prefixWord, tailWord_2038510, baseEnd_2038510] using wordTrace_append hprefix tailTrace_2038510
  have hstable : (prefixWord ++ tailWord_2038510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038510).length < 2 ^ (prefixWord ++ tailWord_2038510).sum := by decide
  have hdescent : baseEnd_2038510 < baseStart_2038510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038514 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 5]
def baseStart_2038514 : Nat := 118140960795 + 2038514 * 2 ^ 59
def prefixEnd_2038514 : Nat := 4983230072969 + 3 ^ 40 * 2038514 * 2
def baseEnd_2038514 : Nat := 116304166991060282033339

theorem tailTrace_2038514 : CollatzResearch.WordTrace tailWord_2038514 prefixEnd_2038514 116304166991060282033339 := by
  unfold tailWord_2038514
  simp only [CollatzResearch.WordTrace]
  refine ⟨18587678434204850829658649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49567142491212935545756397 18587678434204850829658649)
  ·
    refine ⟨13940758825653638122243987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18587678434204850829658649 13940758825653638122243987)
    ·
      refine ⟨20911138238480457183365981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13940758825653638122243987 20911138238480457183365981)
      ·
        refine ⟨7841676839430171443762243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20911138238480457183365981 7841676839430171443762243)
        ·
          refine ⟨11762515259145257165643365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7841676839430171443762243 11762515259145257165643365)
          ·
            refine ⟨2205471611089735718558131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11762515259145257165643365 2205471611089735718558131)
            ·
              refine ⟨3308207416634603577837197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205471611089735718558131 3308207416634603577837197)
              ·
                refine ⟨1240577781237976341688949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3308207416634603577837197 1240577781237976341688949)
                ·
                  refine ⟨116304166991060282033339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1240577781237976341688949 116304166991060282033339)
                  ·
                    rfl

theorem cell23_2038514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_2038514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038514 prefixEnd_2038514 := by exact prefixLift 2038514
  have htrace : WordTrace (prefixWord ++ tailWord_2038514) baseStart_2038514 baseEnd_2038514 := by
    simpa [prefixWord, tailWord_2038514, baseEnd_2038514] using wordTrace_append hprefix tailTrace_2038514
  have hstable : (prefixWord ++ tailWord_2038514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038514).length < 2 ^ (prefixWord ++ tailWord_2038514).sum := by decide
  have hdescent : baseEnd_2038514 < baseStart_2038514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038553 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 10]
def baseStart_2038553 : Nat := 118140960795 + 2038553 * 2 ^ 59
def prefixEnd_2038553 : Nat := 4983230072969 + 3 ^ 40 * 2038553 * 2
def baseEnd_2038553 : Nat := 116306392073896431745819

theorem tailTrace_2038553 : CollatzResearch.WordTrace tailWord_2038553 prefixEnd_2038553 116306392073896431745819 := by
  unfold tailWord_2038553
  simp only [CollatzResearch.WordTrace]
  refine ⟨74352136183678112979304313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49568090789118741986202875 74352136183678112979304313)
  ·
    refine ⟨55764102137758584734478235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74352136183678112979304313 55764102137758584734478235)
    ·
      refine ⟨83646153206637877101717353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55764102137758584734478235 83646153206637877101717353)
      ·
        refine ⟨62734614904978407826288015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83646153206637877101717353 62734614904978407826288015)
        ·
          refine ⟨94101922357467611739432023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62734614904978407826288015 94101922357467611739432023)
          ·
            refine ⟨141152883536201417609148035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94101922357467611739432023 141152883536201417609148035)
            ·
              refine ⟨211729325304302126413722053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141152883536201417609148035 211729325304302126413722053)
              ·
                refine ⟨39699248494556648702572885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211729325304302126413722053 39699248494556648702572885)
                ·
                  refine ⟨116306392073896431745819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 39699248494556648702572885 116306392073896431745819)
                  ·
                    rfl

theorem cell23_2038553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 10].length) (baseStart_2038553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038553 prefixEnd_2038553 := by exact prefixLift 2038553
  have htrace : WordTrace (prefixWord ++ tailWord_2038553) baseStart_2038553 baseEnd_2038553 := by
    simpa [prefixWord, tailWord_2038553, baseEnd_2038553] using wordTrace_append hprefix tailTrace_2038553
  have hstable : (prefixWord ++ tailWord_2038553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038553).length < 2 ^ (prefixWord ++ tailWord_2038553).sum := by decide
  have hdescent : baseEnd_2038553 < baseStart_2038553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038564 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2038564 : Nat := 118140960795 + 2038564 * 2 ^ 59
def prefixEnd_2038564 : Nat := 4983230072969 + 3 ^ 40 * 2038564 * 2
def baseEnd_2038564 : Nat := 1046763176952267342674821

theorem tailTrace_2038564 : CollatzResearch.WordTrace tailWord_2038564 prefixEnd_2038564 1046763176952267342674821 := by
  unfold tailWord_2038564
  simp only [CollatzResearch.WordTrace]
  refine ⟨37176268693319130928977373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49568358257758841238636497 37176268693319130928977373)
  ·
    refine ⟨13941100759994674098366515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37176268693319130928977373 13941100759994674098366515)
    ·
      refine ⟨20911651139992011147549773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13941100759994674098366515 20911651139992011147549773)
      ·
        refine ⟨7841869177497004180331165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20911651139992011147549773 7841869177497004180331165)
        ·
          refine ⟨2940700941561376567624187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7841869177497004180331165 2940700941561376567624187)
          ·
            refine ⟨4411051412342064851436281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940700941561376567624187 4411051412342064851436281)
            ·
              refine ⟨3308288559256548638577211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411051412342064851436281 3308288559256548638577211)
              ·
                refine ⟨4962432838884822957865817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308288559256548638577211 4962432838884822957865817)
                ·
                  refine ⟨3721824629163617218399363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962432838884822957865817 3721824629163617218399363)
                  ·
                    refine ⟨5582736943745425827599045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721824629163617218399363 5582736943745425827599045)
                    ·
                      refine ⟨1046763176952267342674821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5582736943745425827599045 1046763176952267342674821)
                      ·
                        rfl

theorem cell23_2038564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2038564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038564 prefixEnd_2038564 := by exact prefixLift 2038564
  have htrace : WordTrace (prefixWord ++ tailWord_2038564) baseStart_2038564 baseEnd_2038564 := by
    simpa [prefixWord, tailWord_2038564, baseEnd_2038564] using wordTrace_append hprefix tailTrace_2038564
  have hstable : (prefixWord ++ tailWord_2038564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038564).length < 2 ^ (prefixWord ++ tailWord_2038564).sum := by decide
  have hdescent : baseEnd_2038564 < baseStart_2038564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038591 : List Nat := [1, 1, 2, 2, 5, 1, 4, 2, 1, 4]
def baseStart_2038591 : Nat := 118140960795 + 2038591 * 2 ^ 59
def prefixEnd_2038591 : Nat := 4983230072969 + 3 ^ 40 * 2038591 * 2
def baseEnd_2038591 : Nat := 348925680309979579012399

theorem tailTrace_2038591 : CollatzResearch.WordTrace tailWord_2038591 prefixEnd_2038591 348925680309979579012399 := by
  unfold tailWord_2038591
  simp only [CollatzResearch.WordTrace]
  refine ⟨74353522157540445469187627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49569014771693630312791751 74353522157540445469187627)
  ·
    refine ⟨111530283236310668203781441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74353522157540445469187627 111530283236310668203781441)
    ·
      refine ⟨83647712427233001152836081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111530283236310668203781441 83647712427233001152836081)
      ·
        refine ⟨62735784320424750864627061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83647712427233001152836081 62735784320424750864627061)
        ·
          refine ⟨5881479780039820393558787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62735784320424750864627061 5881479780039820393558787)
          ·
            refine ⟨8822219670059730590338181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881479780039820393558787 8822219670059730590338181)
            ·
              refine ⟨1654166188136199485688409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8822219670059730590338181 1654166188136199485688409)
              ·
                refine ⟨1240624641102149614266307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1654166188136199485688409 1240624641102149614266307)
                ·
                  refine ⟨1860936961653224421399461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240624641102149614266307 1860936961653224421399461)
                  ·
                    refine ⟨348925680309979579012399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1860936961653224421399461 348925680309979579012399)
                    ·
                      rfl

theorem cell23_2038591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 1, 4].length) (baseStart_2038591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038591 prefixEnd_2038591 := by exact prefixLift 2038591
  have htrace : WordTrace (prefixWord ++ tailWord_2038591) baseStart_2038591 baseEnd_2038591 := by
    simpa [prefixWord, tailWord_2038591, baseEnd_2038591] using wordTrace_append hprefix tailTrace_2038591
  have hstable : (prefixWord ++ tailWord_2038591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038591).length < 2 ^ (prefixWord ++ tailWord_2038591).sum := by decide
  have hdescent : baseEnd_2038591 < baseStart_2038591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038598 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2038598 : Nat := 118140960795 + 2038598 * 2 ^ 59
def prefixEnd_2038598 : Nat := 4983230072969 + 3 ^ 40 * 2038598 * 2
def baseEnd_2038598 : Nat := 1046780635294520209649665

theorem tailTrace_2038598 : CollatzResearch.WordTrace tailWord_2038598 prefixEnd_2038598 1046780635294520209649665 := by
  unfold tailWord_2038598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2323555545891096427021639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49569184979010057109794965 2323555545891096427021639)
  ·
    refine ⟨3485333318836644640532459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2323555545891096427021639 3485333318836644640532459)
    ·
      refine ⟨5227999978254966960798689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3485333318836644640532459 5227999978254966960798689)
      ·
        refine ⟨3920999983691225220599017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5227999978254966960798689 3920999983691225220599017)
        ·
          refine ⟨2940749987768418915449263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3920999983691225220599017 2940749987768418915449263)
          ·
            refine ⟨4411124981652628373173895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940749987768418915449263 4411124981652628373173895)
            ·
              refine ⟨6616687472478942559760843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411124981652628373173895 6616687472478942559760843)
              ·
                refine ⟨9925031208718413839641265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616687472478942559760843 9925031208718413839641265)
                ·
                  refine ⟨7443773406538810379730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9925031208718413839641265 7443773406538810379730949)
                  ·
                    refine ⟨1395707513726026946199553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7443773406538810379730949 1395707513726026946199553)
                    ·
                      refine ⟨1046780635294520209649665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395707513726026946199553 1046780635294520209649665)
                      ·
                        rfl

theorem cell23_2038598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2038598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038598 prefixEnd_2038598 := by exact prefixLift 2038598
  have htrace : WordTrace (prefixWord ++ tailWord_2038598) baseStart_2038598 baseEnd_2038598 := by
    simpa [prefixWord, tailWord_2038598, baseEnd_2038598] using wordTrace_append hprefix tailTrace_2038598
  have hstable : (prefixWord ++ tailWord_2038598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038598).length < 2 ^ (prefixWord ++ tailWord_2038598).sum := by decide
  have hdescent : baseEnd_2038598 < baseStart_2038598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038600 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_2038600 : Nat := 118140960795 + 2038600 * 2 ^ 59
def prefixEnd_2038600 : Nat := 4983230072969 + 3 ^ 40 * 2038600 * 2
def baseEnd_2038600 : Nat := 348927220751943067274885

theorem tailTrace_2038600 : CollatzResearch.WordTrace tailWord_2038600 prefixEnd_2038600 348927220751943067274885 := by
  unfold tailWord_2038600
  simp only [CollatzResearch.WordTrace]
  refine ⟨37176925207253920003132627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49569233609671893337510169 37176925207253920003132627)
  ·
    refine ⟨55765387810880880004698941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37176925207253920003132627 55765387810880880004698941)
    ·
      refine ⟨20912020429080330001762103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55765387810880880004698941 20912020429080330001762103)
      ·
        refine ⟨31368030643620495002643155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20912020429080330001762103 31368030643620495002643155)
        ·
          refine ⟨47052045965430742503964733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31368030643620495002643155 47052045965430742503964733)
          ·
            refine ⟨17644517237036528438986775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47052045965430742503964733 17644517237036528438986775)
            ·
              refine ⟨26466775855554792658480163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644517237036528438986775 26466775855554792658480163)
              ·
                refine ⟨39700163783332188987720245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26466775855554792658480163 39700163783332188987720245)
                ·
                  refine ⟨3721890354687392717598773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39700163783332188987720245 3721890354687392717598773)
                  ·
                    refine ⟨348927220751943067274885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3721890354687392717598773 348927220751943067274885)
                    ·
                      rfl

theorem cell23_2038600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_2038600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038600 prefixEnd_2038600 := by exact prefixLift 2038600
  have htrace : WordTrace (prefixWord ++ tailWord_2038600) baseStart_2038600 baseEnd_2038600 := by
    simpa [prefixWord, tailWord_2038600, baseEnd_2038600] using wordTrace_append hprefix tailTrace_2038600
  have hstable : (prefixWord ++ tailWord_2038600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038600).length < 2 ^ (prefixWord ++ tailWord_2038600).sum := by decide
  have hdescent : baseEnd_2038600 < baseStart_2038600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038610 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2038610 : Nat := 118140960795 + 2038610 * 2 ^ 59
def prefixEnd_2038610 : Nat := 4983230072969 + 3 ^ 40 * 2038610 * 2
def baseEnd_2038610 : Nat := 1046786797062374162699609

theorem tailTrace_2038610 : CollatzResearch.WordTrace tailWord_2038610 prefixEnd_2038610 1046786797062374162699609 := by
  unfold tailWord_2038610
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588553786117902928532321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49569476762981074476086189 18588553786117902928532321)
  ·
    refine ⟨13941415339588427196399241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18588553786117902928532321 13941415339588427196399241)
    ·
      refine ⟨10456061504691320397299431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13941415339588427196399241 10456061504691320397299431)
      ·
        refine ⟨15684092257036980595949147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456061504691320397299431 15684092257036980595949147)
        ·
          refine ⟨23526138385555470893923721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15684092257036980595949147 23526138385555470893923721)
          ·
            refine ⟨17644603789166603170442791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23526138385555470893923721 17644603789166603170442791)
            ·
              refine ⟨26466905683749904755664187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644603789166603170442791 26466905683749904755664187)
              ·
                refine ⟨39700358525624857133496281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26466905683749904755664187 39700358525624857133496281)
                ·
                  refine ⟨29775268894218642850122211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39700358525624857133496281 29775268894218642850122211)
                  ·
                    refine ⟨44662903341327964275183317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29775268894218642850122211 44662903341327964275183317)
                    ·
                      refine ⟨1046786797062374162699609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44662903341327964275183317 1046786797062374162699609)
                      ·
                        rfl

theorem cell23_2038610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2038610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038610 prefixEnd_2038610 := by exact prefixLift 2038610
  have htrace : WordTrace (prefixWord ++ tailWord_2038610) baseStart_2038610 baseEnd_2038610 := by
    simpa [prefixWord, tailWord_2038610, baseEnd_2038610] using wordTrace_append hprefix tailTrace_2038610
  have hstable : (prefixWord ++ tailWord_2038610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038610).length < 2 ^ (prefixWord ++ tailWord_2038610).sum := by decide
  have hdescent : baseEnd_2038610 < baseStart_2038610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038631 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 1, 1, 3]
def baseStart_2038631 : Nat := 118140960795 + 2038631 * 2 ^ 59
def prefixEnd_2038631 : Nat := 4983230072969 + 3 ^ 40 * 2038631 * 2
def baseEnd_2038631 : Nat := 1046797580156118580537013

theorem tailTrace_2038631 : CollatzResearch.WordTrace tailWord_2038631 prefixEnd_2038631 1046797580156118580537013 := by
  unfold tailWord_2038631
  simp only [CollatzResearch.WordTrace]
  refine ⟨74354981077395532300643747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49569987384930354867095831 74354981077395532300643747)
  ·
    refine ⟨111532471616093298450965621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74354981077395532300643747 111532471616093298450965621)
    ·
      refine ⟨10456169214008746729778027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111532471616093298450965621 10456169214008746729778027)
      ·
        refine ⟨15684253821013120094667041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456169214008746729778027 15684253821013120094667041)
        ·
          refine ⟨11763190365759840071000281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15684253821013120094667041 11763190365759840071000281)
          ·
            refine ⟨8822392774319880053250211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11763190365759840071000281 8822392774319880053250211)
            ·
              refine ⟨13233589161479820079875317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822392774319880053250211 13233589161479820079875317)
              ·
                refine ⟨1240648983888733132488311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13233589161479820079875317 1240648983888733132488311)
                ·
                  refine ⟨1860973475833099698732467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240648983888733132488311 1860973475833099698732467)
                  ·
                    refine ⟨2791460213749649548098701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1860973475833099698732467 2791460213749649548098701)
                    ·
                      refine ⟨1046797580156118580537013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2791460213749649548098701 1046797580156118580537013)
                      ·
                        rfl

theorem cell23_2038631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_2038631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038631 prefixEnd_2038631 := by exact prefixLift 2038631
  have htrace : WordTrace (prefixWord ++ tailWord_2038631) baseStart_2038631 baseEnd_2038631 := by
    simpa [prefixWord, tailWord_2038631, baseEnd_2038631] using wordTrace_append hprefix tailTrace_2038631
  have hstable : (prefixWord ++ tailWord_2038631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038631).length < 2 ^ (prefixWord ++ tailWord_2038631).sum := by decide
  have hdescent : baseEnd_2038631 < baseStart_2038631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038650 : List Nat := [3, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_2038650 : Nat := 118140960795 + 2038650 * 2 ^ 59
def prefixEnd_2038650 : Nat := 4983230072969 + 3 ^ 40 * 2038650 * 2
def baseEnd_2038650 : Nat := 1046807336288554006199425

theorem tailTrace_2038650 : CollatzResearch.WordTrace tailWord_2038650 prefixEnd_2038650 1046807336288554006199425 := by
  unfold tailWord_2038650
  simp only [CollatzResearch.WordTrace]
  refine ⟨18588918516081674636396351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49570449376217799030390269 18588918516081674636396351)
  ·
    refine ⟨27883377774122511954594527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18588918516081674636396351 27883377774122511954594527)
    ·
      refine ⟨41825066661183767931891791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27883377774122511954594527 41825066661183767931891791)
      ·
        refine ⟨62737599991775651897837687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41825066661183767931891791 62737599991775651897837687)
        ·
          refine ⟨94106399987663477846756531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62737599991775651897837687 94106399987663477846756531)
          ·
            refine ⟨141159599981495216770134797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94106399987663477846756531 141159599981495216770134797)
            ·
              refine ⟨52934849993060706288800549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141159599981495216770134797 52934849993060706288800549)
              ·
                refine ⟨9925284373698882429150103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52934849993060706288800549 9925284373698882429150103)
                ·
                  refine ⟨14887926560548323643725155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925284373698882429150103 14887926560548323643725155)
                  ·
                    refine ⟨22331889840822485465587733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14887926560548323643725155 22331889840822485465587733)
                    ·
                      refine ⟨1046807336288554006199425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22331889840822485465587733 1046807336288554006199425)
                      ·
                        rfl

theorem cell23_2038650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_2038650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038650 prefixEnd_2038650 := by exact prefixLift 2038650
  have htrace : WordTrace (prefixWord ++ tailWord_2038650) baseStart_2038650 baseEnd_2038650 := by
    simpa [prefixWord, tailWord_2038650, baseEnd_2038650] using wordTrace_append hprefix tailTrace_2038650
  have hstable : (prefixWord ++ tailWord_2038650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038650).length < 2 ^ (prefixWord ++ tailWord_2038650).sum := by decide
  have hdescent : baseEnd_2038650 < baseStart_2038650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038660 : List Nat := [2, 3, 2, 1, 1, 1, 1, 12]
def baseStart_2038660 : Nat := 118140960795 + 2038660 * 2 ^ 59
def prefixEnd_2038660 : Nat := 4983230072969 + 3 ^ 40 * 2038660 * 2
def baseEnd_2038660 : Nat := 38770832262781443224977

theorem tailTrace_2038660 : CollatzResearch.WordTrace tailWord_2038660 prefixEnd_2038660 38770832262781443224977 := by
  unfold tailWord_2038660
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178019397145235126724717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49570692529526980168966289 37178019397145235126724717)
  ·
    refine ⟨13941757273929463172521769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37178019397145235126724717 13941757273929463172521769)
    ·
      refine ⟨10456317955447097379391327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13941757273929463172521769 10456317955447097379391327)
      ·
        refine ⟨15684476933170646069086991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456317955447097379391327 15684476933170646069086991)
        ·
          refine ⟨23526715399755969103630487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15684476933170646069086991 23526715399755969103630487)
          ·
            refine ⟨35290073099633953655445731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23526715399755969103630487 35290073099633953655445731)
            ·
              refine ⟨52935109649450930483168597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35290073099633953655445731 52935109649450930483168597)
              ·
                refine ⟨38770832262781443224977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 52935109649450930483168597 38770832262781443224977)
                ·
                  rfl

theorem cell23_2038660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 12].length) (baseStart_2038660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038660 prefixEnd_2038660 := by exact prefixLift 2038660
  have htrace : WordTrace (prefixWord ++ tailWord_2038660) baseStart_2038660 baseEnd_2038660 := by
    simpa [prefixWord, tailWord_2038660, baseEnd_2038660] using wordTrace_append hprefix tailTrace_2038660
  have hstable : (prefixWord ++ tailWord_2038660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038660).length < 2 ^ (prefixWord ++ tailWord_2038660).sum := by decide
  have hdescent : baseEnd_2038660 < baseStart_2038660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038664 : List Nat := [2, 1, 3, 3, 2, 3, 1, 1, 1, 6]
def baseStart_2038664 : Nat := 118140960795 + 2038664 * 2 ^ 59
def prefixEnd_2038664 : Nat := 4983230072969 + 3 ^ 40 * 2038664 * 2
def baseEnd_2038664 : Nat := 348938175005905650474787

theorem tailTrace_2038664 : CollatzResearch.WordTrace tailWord_2038664 prefixEnd_2038664 348938175005905650474787 := by
  unfold tailWord_2038664
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178092343137989468297523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49570789790850652624396697 37178092343137989468297523)
  ·
    refine ⟨55767138514706984202446285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37178092343137989468297523 55767138514706984202446285)
    ·
      refine ⟨20912676943015119075917357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55767138514706984202446285 20912676943015119075917357)
      ·
        refine ⟨7842253853630669653469009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20912676943015119075917357 7842253853630669653469009)
        ·
          refine ⟨5881690390223002240101757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842253853630669653469009 5881690390223002240101757)
          ·
            refine ⟨2205633896333625840038159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5881690390223002240101757 2205633896333625840038159)
            ·
              refine ⟨3308450844500438760057239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205633896333625840038159 3308450844500438760057239)
              ·
                refine ⟨4962676266750658140085859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308450844500438760057239 4962676266750658140085859)
                ·
                  refine ⟨7444014400125987210128789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962676266750658140085859 7444014400125987210128789)
                  ·
                    refine ⟨348938175005905650474787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7444014400125987210128789 348938175005905650474787)
                    ·
                      rfl

theorem cell23_2038664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_2038664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038664 prefixEnd_2038664 := by exact prefixLift 2038664
  have htrace : WordTrace (prefixWord ++ tailWord_2038664) baseStart_2038664 baseEnd_2038664 := by
    simpa [prefixWord, tailWord_2038664, baseEnd_2038664] using wordTrace_append hprefix tailTrace_2038664
  have hstable : (prefixWord ++ tailWord_2038664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038664).length < 2 ^ (prefixWord ++ tailWord_2038664).sum := by decide
  have hdescent : baseEnd_2038664 < baseStart_2038664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038667 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 4]
def baseStart_2038667 : Nat := 118140960795 + 2038667 * 2 ^ 59
def prefixEnd_2038667 : Nat := 4983230072969 + 3 ^ 40 * 2038667 * 2
def baseEnd_2038667 : Nat := 1046816065459680439686847

theorem tailTrace_2038667 : CollatzResearch.WordTrace tailWord_2038667 prefixEnd_2038667 1046816065459680439686847 := by
  unfold tailWord_2038667
  simp only [CollatzResearch.WordTrace]
  refine ⟨74356294105265110448954255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49570862736843406965969503 74356294105265110448954255)
  ·
    refine ⟨111534441157897665673431383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74356294105265110448954255 111534441157897665673431383)
    ·
      refine ⟨167301661736846498510147075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111534441157897665673431383 167301661736846498510147075)
      ·
        refine ⟨250952492605269747765220613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167301661736846498510147075 250952492605269747765220613)
        ·
          refine ⟨47053592363488077705978865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250952492605269747765220613 47053592363488077705978865)
          ·
            refine ⟨35290194272616058279484149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47053592363488077705978865 35290194272616058279484149)
            ·
              refine ⟨3308455713057755463701639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35290194272616058279484149 3308455713057755463701639)
              ·
                refine ⟨4962683569586633195552459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308455713057755463701639 4962683569586633195552459)
                ·
                  refine ⟨7444025354379949793328689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962683569586633195552459 7444025354379949793328689)
                  ·
                    refine ⟨5583019015784962344996517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444025354379949793328689 5583019015784962344996517)
                    ·
                      refine ⟨1046816065459680439686847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5583019015784962344996517 1046816065459680439686847)
                      ·
                        rfl

theorem cell23_2038667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 4].length) (baseStart_2038667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038667 prefixEnd_2038667 := by exact prefixLift 2038667
  have htrace : WordTrace (prefixWord ++ tailWord_2038667) baseStart_2038667 baseEnd_2038667 := by
    simpa [prefixWord, tailWord_2038667, baseEnd_2038667] using wordTrace_append hprefix tailTrace_2038667
  have hstable : (prefixWord ++ tailWord_2038667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038667).length < 2 ^ (prefixWord ++ tailWord_2038667).sum := by decide
  have hdescent : baseEnd_2038667 < baseStart_2038667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038677 : List Nat := [1, 3, 2, 1, 1, 4, 4, 7]
def baseStart_2038677 : Nat := 118140960795 + 2038677 * 2 ^ 59
def prefixEnd_2038677 : Nat := 4983230072969 + 3 ^ 40 * 2038677 * 2
def baseEnd_2038677 : Nat := 38771155565415755576363

theorem tailTrace_2038677 : CollatzResearch.WordTrace tailWord_2038677 prefixEnd_2038677 38771155565415755576363 := by
  unfold tailWord_2038677
  simp only [CollatzResearch.WordTrace]
  refine ⟨74356658835228882156818285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49571105890152588104545523 74356658835228882156818285)
  ·
    refine ⟨27883747063210830808806857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74356658835228882156818285 27883747063210830808806857)
    ·
      refine ⟨20912810297408123106605143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27883747063210830808806857 20912810297408123106605143)
      ·
        refine ⟨31369215446112184659907715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20912810297408123106605143 31369215446112184659907715)
        ·
          refine ⟨47053823169168276989861573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31369215446112184659907715 47053823169168276989861573)
          ·
            refine ⟨8822591844219051935599045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47053823169168276989861573 8822591844219051935599045)
            ·
              refine ⟨1654235970791072237924821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8822591844219051935599045 1654235970791072237924821)
              ·
                refine ⟨38771155565415755576363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1654235970791072237924821 38771155565415755576363)
                ·
                  rfl

theorem cell23_2038677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 4, 7].length) (baseStart_2038677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038677 prefixEnd_2038677 := by exact prefixLift 2038677
  have htrace : WordTrace (prefixWord ++ tailWord_2038677) baseStart_2038677 baseEnd_2038677 := by
    simpa [prefixWord, tailWord_2038677, baseEnd_2038677] using wordTrace_append hprefix tailTrace_2038677
  have hstable : (prefixWord ++ tailWord_2038677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038677).length < 2 ^ (prefixWord ++ tailWord_2038677).sum := by decide
  have hdescent : baseEnd_2038677 < baseStart_2038677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038688 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 1, 2, 2]
def baseStart_2038688 : Nat := 118140960795 + 2038688 * 2 ^ 59
def prefixEnd_2038688 : Nat := 4983230072969 + 3 ^ 40 * 2038688 * 2
def baseEnd_2038688 : Nat := 1046826848553424857524251

theorem tailTrace_2038688 : CollatzResearch.WordTrace tailWord_2038688 prefixEnd_2038688 1046826848553424857524251 := by
  unfold tailWord_2038688
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178530019094515517734359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49571373358792687356979145 37178530019094515517734359)
  ·
    refine ⟨55767795028641773276601539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37178530019094515517734359 55767795028641773276601539)
    ·
      refine ⟨83651692542962659914902309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55767795028641773276601539 83651692542962659914902309)
      ·
        refine ⟨15684692351805498734044183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83651692542962659914902309 15684692351805498734044183)
        ·
          refine ⟨23527038527708248101066275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15684692351805498734044183 23527038527708248101066275)
          ·
            refine ⟨35290557791562372151599413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23527038527708248101066275 35290557791562372151599413)
            ·
              refine ⟨3308489792958972389212445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35290557791562372151599413 3308489792958972389212445)
              ·
                refine ⟨1240683672359614645954667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3308489792958972389212445 1240683672359614645954667)
                ·
                  refine ⟨1861025508539421968932001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240683672359614645954667 1861025508539421968932001)
                  ·
                    refine ⟨1395769131404566476699001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861025508539421968932001 1395769131404566476699001)
                    ·
                      refine ⟨1046826848553424857524251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395769131404566476699001 1046826848553424857524251)
                      ·
                        rfl

theorem cell23_2038688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_2038688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038688 prefixEnd_2038688 := by exact prefixLift 2038688
  have htrace : WordTrace (prefixWord ++ tailWord_2038688) baseStart_2038688 baseEnd_2038688 := by
    simpa [prefixWord, tailWord_2038688, baseEnd_2038688] using wordTrace_append hprefix tailTrace_2038688
  have hstable : (prefixWord ++ tailWord_2038688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038688).length < 2 ^ (prefixWord ++ tailWord_2038688).sum := by decide
  have hdescent : baseEnd_2038688 < baseStart_2038688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038705 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 3, 2, 2]
def baseStart_2038705 : Nat := 118140960795 + 2038705 * 2 ^ 59
def prefixEnd_2038705 : Nat := 4983230072969 + 3 ^ 40 * 2038705 * 2
def baseEnd_2038705 : Nat := 1046835577724551291011673

theorem tailTrace_2038705 : CollatzResearch.WordTrace tailWord_2038705 prefixEnd_2038705 1046835577724551291011673 := by
  unfold tailWord_2038705
  simp only [CollatzResearch.WordTrace]
  refine ⟨74357680079127442938837569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49571786719418295292558379 74357680079127442938837569)
  ·
    refine ⟨55768260059345582204128177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74357680079127442938837569 55768260059345582204128177)
    ·
      refine ⟨41826195044509186653096133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55768260059345582204128177 41826195044509186653096133)
      ·
        refine ⟨7842411570845472497455525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41826195044509186653096133 7842411570845472497455525)
        ·
          refine ⟨1470452169533526093272911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7842411570845472497455525 1470452169533526093272911)
          ·
            refine ⟨2205678254300289139909367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470452169533526093272911 2205678254300289139909367)
            ·
              refine ⟨3308517381450433709864051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205678254300289139909367 3308517381450433709864051)
              ·
                refine ⟨4962776072175650564796077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308517381450433709864051 4962776072175650564796077)
                ·
                  refine ⟨1861041027065868961798529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4962776072175650564796077 1861041027065868961798529)
                  ·
                    refine ⟨1395780770299401721348897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861041027065868961798529 1395780770299401721348897)
                    ·
                      refine ⟨1046835577724551291011673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395780770299401721348897 1046835577724551291011673)
                      ·
                        rfl

theorem cell23_2038705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_2038705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038705 prefixEnd_2038705 := by exact prefixLift 2038705
  have htrace : WordTrace (prefixWord ++ tailWord_2038705) baseStart_2038705 baseEnd_2038705 := by
    simpa [prefixWord, tailWord_2038705, baseEnd_2038705] using wordTrace_append hprefix tailTrace_2038705
  have hstable : (prefixWord ++ tailWord_2038705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038705).length < 2 ^ (prefixWord ++ tailWord_2038705).sum := by decide
  have hdescent : baseEnd_2038705 < baseStart_2038705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038714 : List Nat := [3, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2]
def baseStart_2038714 : Nat := 118140960795 + 2038714 * 2 ^ 59
def prefixEnd_2038714 : Nat := 4983230072969 + 3 ^ 40 * 2038714 * 2
def baseEnd_2038714 : Nat := 1046840199050441755799131

theorem tailTrace_2038714 : CollatzResearch.WordTrace tailWord_2038714 prefixEnd_2038714 1046840199050441755799131 := by
  unfold tailWord_2038714
  simp only [CollatzResearch.WordTrace]
  refine ⟨18589502084023709368978799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49572005557396558317276797 18589502084023709368978799)
  ·
    refine ⟨27884253126035564053468199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18589502084023709368978799 27884253126035564053468199)
    ·
      refine ⟨41826379689053346080202299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27884253126035564053468199 41826379689053346080202299)
      ·
        refine ⟨62739569533580019120303449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41826379689053346080202299 62739569533580019120303449)
        ·
          refine ⟨47054677150185014340227587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62739569533580019120303449 47054677150185014340227587)
          ·
            refine ⟨70582015725277521510341381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47054677150185014340227587 70582015725277521510341381)
            ·
              refine ⟨13234127948489535283189009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70582015725277521510341381 13234127948489535283189009)
              ·
                refine ⟨9925595961367151462391757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13234127948489535283189009 9925595961367151462391757)
                ·
                  refine ⟨3722098485512681798396909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9925595961367151462391757 3722098485512681798396909)
                  ·
                    refine ⟨1395786932067255674398841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722098485512681798396909 1395786932067255674398841)
                    ·
                      refine ⟨1046840199050441755799131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395786932067255674398841 1046840199050441755799131)
                      ·
                        rfl

theorem cell23_2038714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_2038714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038714 prefixEnd_2038714 := by exact prefixLift 2038714
  have htrace : WordTrace (prefixWord ++ tailWord_2038714) baseStart_2038714 baseEnd_2038714 := by
    simpa [prefixWord, tailWord_2038714, baseEnd_2038714] using wordTrace_append hprefix tailTrace_2038714
  have hstable : (prefixWord ++ tailWord_2038714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038714).length < 2 ^ (prefixWord ++ tailWord_2038714).sum := by decide
  have hdescent : baseEnd_2038714 < baseStart_2038714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038731 : List Nat := [1, 1, 1, 1, 3, 5, 3, 2, 1, 3, 2]
def baseStart_2038731 : Nat := 118140960795 + 2038731 * 2 ^ 59
def prefixEnd_2038731 : Nat := 4983230072969 + 3 ^ 40 * 2038731 * 2
def baseEnd_2038731 : Nat := 1046848928221568189286553

theorem tailTrace_2038731 : CollatzResearch.WordTrace tailWord_2038731 prefixEnd_2038731 1046848928221568189286553 := by
  unfold tailWord_2038731
  simp only [CollatzResearch.WordTrace]
  refine ⟨74358628377033249379284047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49572418918022166252856031 74358628377033249379284047)
  ·
    refine ⟨111537942565549874068926071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74358628377033249379284047 111537942565549874068926071)
    ·
      refine ⟨167306913848324811103389107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111537942565549874068926071 167306913848324811103389107)
      ·
        refine ⟨250960370772487216655083661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167306913848324811103389107 250960370772487216655083661)
        ·
          refine ⟨94110139039682706245656373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250960370772487216655083661 94110139039682706245656373)
          ·
            refine ⟨8822825534970253710530285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94110139039682706245656373 8822825534970253710530285)
            ·
              refine ⟨3308559575613845141448857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8822825534970253710530285 3308559575613845141448857)
              ·
                refine ⟨2481419681710383856086643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308559575613845141448857 2481419681710383856086643)
                ·
                  refine ⟨3722129522565575784129965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481419681710383856086643 3722129522565575784129965)
                  ·
                    refine ⟨1395798570962090919048737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3722129522565575784129965 1395798570962090919048737)
                    ·
                      refine ⟨1046848928221568189286553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395798570962090919048737 1046848928221568189286553)
                      ·
                        rfl

theorem cell23_2038731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 3, 2].length) (baseStart_2038731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038731 prefixEnd_2038731 := by exact prefixLift 2038731
  have htrace : WordTrace (prefixWord ++ tailWord_2038731) baseStart_2038731 baseEnd_2038731 := by
    simpa [prefixWord, tailWord_2038731, baseEnd_2038731] using wordTrace_append hprefix tailTrace_2038731
  have hstable : (prefixWord ++ tailWord_2038731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038731).length < 2 ^ (prefixWord ++ tailWord_2038731).sum := by decide
  have hdescent : baseEnd_2038731 < baseStart_2038731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038744 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 3, 4, 2]
def baseStart_2038744 : Nat := 118140960795 + 2038744 * 2 ^ 59
def prefixEnd_2038744 : Nat := 4983230072969 + 3 ^ 40 * 2038744 * 2
def baseEnd_2038744 : Nat := 1046855603470076638423993

theorem tailTrace_2038744 : CollatzResearch.WordTrace tailWord_2038744 prefixEnd_2038744 1046855603470076638423993 := by
  unfold tailWord_2038744
  simp only [CollatzResearch.WordTrace]
  refine ⟨37179551262993076299753643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49572735017324101733004857 37179551262993076299753643)
  ·
    refine ⟨55769326894489614449630465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37179551262993076299753643 55769326894489614449630465)
    ·
      refine ⟨41826995170867210837222849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55769326894489614449630465 41826995170867210837222849)
      ·
        refine ⟨31370246378150408127917137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41826995170867210837222849 31370246378150408127917137)
        ·
          refine ⟨23527684783612806095937853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31370246378150408127917137 23527684783612806095937853)
          ·
            refine ⟨8822881793854802285976695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23527684783612806095937853 8822881793854802285976695)
            ·
              refine ⟨13234322690782203428965043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822881793854802285976695 13234322690782203428965043)
              ·
                refine ⟨19851484036173305143447565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234322690782203428965043 19851484036173305143447565)
                ·
                  refine ⟨7444306513564989428792837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19851484036173305143447565 7444306513564989428792837)
                  ·
                    refine ⟨1395807471293435517898657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7444306513564989428792837 1395807471293435517898657)
                    ·
                      refine ⟨1046855603470076638423993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395807471293435517898657 1046855603470076638423993)
                      ·
                        rfl

theorem cell23_2038744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_2038744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038744 prefixEnd_2038744 := by exact prefixLift 2038744
  have htrace : WordTrace (prefixWord ++ tailWord_2038744) baseStart_2038744 baseEnd_2038744 := by
    simpa [prefixWord, tailWord_2038744, baseEnd_2038744] using wordTrace_append hprefix tailTrace_2038744
  have hstable : (prefixWord ++ tailWord_2038744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038744).length < 2 ^ (prefixWord ++ tailWord_2038744).sum := by decide
  have hdescent : baseEnd_2038744 < baseStart_2038744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038772 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2038772 : Nat := 118140960795 + 2038772 * 2 ^ 59
def prefixEnd_2038772 : Nat := 4983230072969 + 3 ^ 40 * 2038772 * 2
def baseEnd_2038772 : Nat := 1046869980928402528873865

theorem tailTrace_2038772 : CollatzResearch.WordTrace tailWord_2038772 prefixEnd_2038772 1046869980928402528873865 := by
  unfold tailWord_2038772
  simp only [CollatzResearch.WordTrace]
  refine ⟨37180061884942356690763285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49573415846589808921017713 37180061884942356690763285)
  ·
    refine ⟨1742815400856672969879529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37180061884942356690763285 1742815400856672969879529)
    ·
      refine ⟨1307111550642504727409647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1742815400856672969879529 1307111550642504727409647)
      ·
        refine ⟨1960667325963757091114471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1307111550642504727409647 1960667325963757091114471)
        ·
          refine ⟨2941000988945635636671707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1960667325963757091114471 2941000988945635636671707)
          ·
            refine ⟨4411501483418453455007561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2941000988945635636671707 4411501483418453455007561)
            ·
              refine ⟨3308626112563840091255671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411501483418453455007561 3308626112563840091255671)
              ·
                refine ⟨4962939168845760136883507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308626112563840091255671 4962939168845760136883507)
                ·
                  refine ⟨7444408753268640205325261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962939168845760136883507 7444408753268640205325261)
                  ·
                    refine ⟨2791653282475740076996973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7444408753268640205325261 2791653282475740076996973)
                    ·
                      refine ⟨1046869980928402528873865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2791653282475740076996973 1046869980928402528873865)
                      ·
                        rfl

theorem cell23_2038772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2038772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038772 prefixEnd_2038772 := by exact prefixLift 2038772
  have htrace : WordTrace (prefixWord ++ tailWord_2038772) baseStart_2038772 baseEnd_2038772 := by
    simpa [prefixWord, tailWord_2038772, baseEnd_2038772] using wordTrace_append hprefix tailTrace_2038772
  have hstable : (prefixWord ++ tailWord_2038772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038772).length < 2 ^ (prefixWord ++ tailWord_2038772).sum := by decide
  have hdescent : baseEnd_2038772 < baseStart_2038772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038774 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_2038774 : Nat := 118140960795 + 2038774 * 2 ^ 59
def prefixEnd_2038774 : Nat := 4983230072969 + 3 ^ 40 * 2038774 * 2
def baseEnd_2038774 : Nat := 1046871007889711521048855

theorem tailTrace_2038774 : CollatzResearch.WordTrace tailWord_2038774 prefixEnd_2038774 1046871007889711521048855 := by
  unfold tailWord_2038774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647512294742341732693711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49573464477251645148732917 4647512294742341732693711)
  ·
    refine ⟨6971268442113512599040567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4647512294742341732693711 6971268442113512599040567)
    ·
      refine ⟨10456902663170268898560851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6971268442113512599040567 10456902663170268898560851)
      ·
        refine ⟨15685353994755403347841277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10456902663170268898560851 15685353994755403347841277)
        ·
          refine ⟨5882007748033276255440479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15685353994755403347841277 5882007748033276255440479)
          ·
            refine ⟨8823011622049914383160719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882007748033276255440479 8823011622049914383160719)
            ·
              refine ⟨13234517433074871574741079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8823011622049914383160719 13234517433074871574741079)
              ·
                refine ⟨19851776149612307362111619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234517433074871574741079 19851776149612307362111619)
                ·
                  refine ⟨29777664224418461043167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19851776149612307362111619 29777664224418461043167429)
                  ·
                    refine ⟨5583312042078461445593893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29777664224418461043167429 5583312042078461445593893)
                    ·
                      refine ⟨1046871007889711521048855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5583312042078461445593893 1046871007889711521048855)
                      ·
                        rfl

theorem cell23_2038774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_2038774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038774 prefixEnd_2038774 := by exact prefixLift 2038774
  have htrace : WordTrace (prefixWord ++ tailWord_2038774) baseStart_2038774 baseEnd_2038774 := by
    simpa [prefixWord, tailWord_2038774, baseEnd_2038774] using wordTrace_append hprefix tailTrace_2038774
  have hstable : (prefixWord ++ tailWord_2038774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038774).length < 2 ^ (prefixWord ++ tailWord_2038774).sum := by decide
  have hdescent : baseEnd_2038774 < baseStart_2038774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038812 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_2038812 : Nat := 118140960795 + 2038812 * 2 ^ 59
def prefixEnd_2038812 : Nat := 4983230072969 + 3 ^ 40 * 2038812 * 2
def baseEnd_2038812 : Nat := 1046890520154582372373681

theorem tailTrace_2038812 : CollatzResearch.WordTrace tailWord_2038812 prefixEnd_2038812 1046890520154582372373681 := by
  unfold tailWord_2038812
  simp only [CollatzResearch.WordTrace]
  refine ⟨37180791344869900106491345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49574388459826533475321793 37180791344869900106491345)
  ·
    refine ⟨27885593508652425079868509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37180791344869900106491345 27885593508652425079868509)
    ·
      refine ⟨10457097565744659404950691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27885593508652425079868509 10457097565744659404950691)
      ·
        refine ⟨15685646348616989107426037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10457097565744659404950691 15685646348616989107426037)
        ·
          refine ⟨1470529345182842728821191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15685646348616989107426037 1470529345182842728821191)
          ·
            refine ⟨2205794017774264093231787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470529345182842728821191 2205794017774264093231787)
            ·
              refine ⟨3308691026661396139847681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2205794017774264093231787 3308691026661396139847681)
              ·
                refine ⟨2481518269996047104885761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308691026661396139847681 2481518269996047104885761)
                ·
                  refine ⟨1861138702497035328664321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2481518269996047104885761 1861138702497035328664321)
                  ·
                    refine ⟨1395854026872776496498241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861138702497035328664321 1395854026872776496498241)
                    ·
                      refine ⟨1046890520154582372373681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395854026872776496498241 1046890520154582372373681)
                      ·
                        rfl

theorem cell23_2038812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_2038812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038812 prefixEnd_2038812 := by exact prefixLift 2038812
  have htrace : WordTrace (prefixWord ++ tailWord_2038812) baseStart_2038812 baseEnd_2038812 := by
    simpa [prefixWord, tailWord_2038812, baseEnd_2038812] using wordTrace_append hprefix tailTrace_2038812
  have hstable : (prefixWord ++ tailWord_2038812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038812).length < 2 ^ (prefixWord ++ tailWord_2038812).sum := by decide
  have hdescent : baseEnd_2038812 < baseStart_2038812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038847 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 4]
def baseStart_2038847 : Nat := 118140960795 + 2038847 * 2 ^ 59
def prefixEnd_2038847 : Nat := 4983230072969 + 3 ^ 40 * 2038847 * 2
def baseEnd_2038847 : Nat := 1046908491977489735436019

theorem tailTrace_2038847 : CollatzResearch.WordTrace tailWord_2038847 prefixEnd_2038847 1046908491977489735436019 := by
  unfold tailWord_2038847
  simp only [CollatzResearch.WordTrace]
  refine ⟨74362859244613001190506795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49575239496408667460337863 74362859244613001190506795)
  ·
    refine ⟨111544288866919501785760193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74362859244613001190506795 111544288866919501785760193)
    ·
      refine ⟨83658216650189626339320145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111544288866919501785760193 83658216650189626339320145)
      ·
        refine ⟨62743662487642219754490109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83658216650189626339320145 62743662487642219754490109)
        ·
          refine ⟨23528873432865832407933791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62743662487642219754490109 23528873432865832407933791)
          ·
            refine ⟨35293310149298748611900687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23528873432865832407933791 35293310149298748611900687)
            ·
              refine ⟨52939965223948122917851031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35293310149298748611900687 52939965223948122917851031)
              ·
                refine ⟨79409947835922184376776547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52939965223948122917851031 79409947835922184376776547)
                ·
                  refine ⟨119114921753883276565164821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79409947835922184376776547 119114921753883276565164821)
                  ·
                    refine ⟨5583511957213278588992101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119114921753883276565164821 5583511957213278588992101)
                    ·
                      refine ⟨1046908491977489735436019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5583511957213278588992101 1046908491977489735436019)
                      ·
                        rfl

theorem cell23_2038847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_2038847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038847 prefixEnd_2038847 := by exact prefixLift 2038847
  have htrace : WordTrace (prefixWord ++ tailWord_2038847) baseStart_2038847 baseEnd_2038847 := by
    simpa [prefixWord, tailWord_2038847, baseEnd_2038847] using wordTrace_append hprefix tailTrace_2038847
  have hstable : (prefixWord ++ tailWord_2038847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038847).length < 2 ^ (prefixWord ++ tailWord_2038847).sum := by decide
  have hdescent : baseEnd_2038847 < baseStart_2038847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038897 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 7]
def baseStart_2038897 : Nat := 118140960795 + 2038897 * 2 ^ 59
def prefixEnd_2038897 : Nat := 4983230072969 + 3 ^ 40 * 2038897 * 2
def baseEnd_2038897 : Nat := 1046934166010214539810789

theorem tailTrace_2038897 : CollatzResearch.WordTrace tailWord_2038897 prefixEnd_2038897 1046934166010214539810789 := by
  unfold tailWord_2038897
  simp only [CollatzResearch.WordTrace]
  refine ⟨74364682894431859729826945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49576455262954573153217963 74364682894431859729826945)
  ·
    refine ⟨55773512170823894797370209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74364682894431859729826945 55773512170823894797370209)
    ·
      refine ⟨41830134128117921098027657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55773512170823894797370209 41830134128117921098027657)
      ·
        refine ⟨31372600596088440823520743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41830134128117921098027657 31372600596088440823520743)
        ·
          refine ⟨47058900894132661235281115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31372600596088440823520743 47058900894132661235281115)
          ·
            refine ⟨70588351341198991852921673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47058900894132661235281115 70588351341198991852921673)
            ·
              refine ⟨52941263505899243889691255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70588351341198991852921673 52941263505899243889691255)
              ·
                refine ⟨79411895258848865834536883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52941263505899243889691255 79411895258848865834536883)
                ·
                  refine ⟨119117842888273298751805325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79411895258848865834536883 119117842888273298751805325)
                  ·
                    refine ⟨44669191083102487031926997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119117842888273298751805325 44669191083102487031926997)
                    ·
                      refine ⟨1046934166010214539810789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44669191083102487031926997 1046934166010214539810789)
                      ·
                        rfl

theorem cell23_2038897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_2038897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038897 prefixEnd_2038897 := by exact prefixLift 2038897
  have htrace : WordTrace (prefixWord ++ tailWord_2038897) baseStart_2038897 baseEnd_2038897 := by
    simpa [prefixWord, tailWord_2038897, baseEnd_2038897] using wordTrace_append hprefix tailTrace_2038897
  have hstable : (prefixWord ++ tailWord_2038897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038897).length < 2 ^ (prefixWord ++ tailWord_2038897).sum := by decide
  have hdescent : baseEnd_2038897 < baseStart_2038897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038935 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 1, 1, 3]
def baseStart_2038935 : Nat := 118140960795 + 2038935 * 2 ^ 59
def prefixEnd_2038935 : Nat := 4983230072969 + 3 ^ 40 * 2038935 * 2
def baseEnd_2038935 : Nat := 1046953678275085391135615

theorem tailTrace_2038935 : CollatzResearch.WordTrace tailWord_2038935 prefixEnd_2038935 1046953678275085391135615 := by
  unfold tailWord_2038935
  simp only [CollatzResearch.WordTrace]
  refine ⟨74366068868294192219710259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49577379245529461479806839 74366068868294192219710259)
  ·
    refine ⟨111549103302441288329565389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74366068868294192219710259 111549103302441288329565389)
    ·
      refine ⟨41830913738415483123587021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111549103302441288329565389 41830913738415483123587021)
      ·
        refine ⟨15686592651905806171345133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41830913738415483123587021 15686592651905806171345133)
        ·
          refine ⟨5882472244464677314254425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15686592651905806171345133 5882472244464677314254425)
          ·
            refine ⟨4411854183348507985690819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882472244464677314254425 4411854183348507985690819)
            ·
              refine ⟨6617781275022761978536229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4411854183348507985690819 6617781275022761978536229)
              ·
                refine ⟨1240833989066767870975543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6617781275022761978536229 1240833989066767870975543)
                ·
                  refine ⟨1861250983600151806463315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240833989066767870975543 1861250983600151806463315)
                  ·
                    refine ⟨2791876475400227709694973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1861250983600151806463315 2791876475400227709694973)
                    ·
                      refine ⟨1046953678275085391135615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2791876475400227709694973 1046953678275085391135615)
                      ·
                        rfl

theorem cell23_2038935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_2038935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038935 prefixEnd_2038935 := by exact prefixLift 2038935
  have htrace : WordTrace (prefixWord ++ tailWord_2038935) baseStart_2038935 baseEnd_2038935 := by
    simpa [prefixWord, tailWord_2038935, baseEnd_2038935] using wordTrace_append hprefix tailTrace_2038935
  have hstable : (prefixWord ++ tailWord_2038935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038935).length < 2 ^ (prefixWord ++ tailWord_2038935).sum := by decide
  have hdescent : baseEnd_2038935 < baseStart_2038935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038944 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5]
def baseStart_2038944 : Nat := 118140960795 + 2038944 * 2 ^ 59
def prefixEnd_2038944 : Nat := 4983230072969 + 3 ^ 40 * 2038944 * 2
def baseEnd_2038944 : Nat := 1046958299600975855923073

theorem tailTrace_2038944 : CollatzResearch.WordTrace tailWord_2038944 prefixEnd_2038944 1046958299600975855923073 := by
  unfold tailWord_2038944
  simp only [CollatzResearch.WordTrace]
  refine ⟨37183198562630793378393943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49577598083507724504525257 37183198562630793378393943)
  ·
    refine ⟨55774797843946190067590915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37183198562630793378393943 55774797843946190067590915)
    ·
      refine ⟨83662196765919285101386373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55774797843946190067590915 83662196765919285101386373)
      ·
        refine ⟨15686661893609865956509945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83662196765919285101386373 15686661893609865956509945)
        ·
          refine ⟨11764996420207399467382459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15686661893609865956509945 11764996420207399467382459)
          ·
            refine ⟨17647494630311099201073689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11764996420207399467382459 17647494630311099201073689)
            ·
              refine ⟨13235620972733324400805267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17647494630311099201073689 13235620972733324400805267)
              ·
                refine ⟨19853431459099986601207901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13235620972733324400805267 19853431459099986601207901)
                ·
                  refine ⟨7445036797162494975452963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19853431459099986601207901 7445036797162494975452963)
                  ·
                    refine ⟨11167555195743742463179445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7445036797162494975452963 11167555195743742463179445)
                    ·
                      refine ⟨1046958299600975855923073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11167555195743742463179445 1046958299600975855923073)
                      ·
                        rfl

theorem cell23_2038944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_2038944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038944 prefixEnd_2038944 := by exact prefixLift 2038944
  have htrace : WordTrace (prefixWord ++ tailWord_2038944) baseStart_2038944 baseEnd_2038944 := by
    simpa [prefixWord, tailWord_2038944, baseEnd_2038944] using wordTrace_append hprefix tailTrace_2038944
  have hstable : (prefixWord ++ tailWord_2038944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038944).length < 2 ^ (prefixWord ++ tailWord_2038944).sum := by decide
  have hdescent : baseEnd_2038944 < baseStart_2038944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038951 : List Nat := [1, 1, 6, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2038951 : Nat := 118140960795 + 2038951 * 2 ^ 59
def prefixEnd_2038951 : Nat := 4983230072969 + 3 ^ 40 * 2038951 * 2
def baseEnd_2038951 : Nat := 348987297988519109511847

theorem tailTrace_2038951 : CollatzResearch.WordTrace tailWord_2038951 prefixEnd_2038951 348987297988519109511847 := by
  unfold tailWord_2038951
  simp only [CollatzResearch.WordTrace]
  refine ⟨74366652436236226952292707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49577768290824151301528471 74366652436236226952292707)
  ·
    refine ⟨111549978654354340428439061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74366652436236226952292707 111549978654354340428439061)
    ·
      refine ⟨5228905249422859707583081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111549978654354340428439061 5228905249422859707583081)
      ·
        refine ⟨3921678937067144780687311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5228905249422859707583081 3921678937067144780687311)
        ·
          refine ⟨5882518405600717171030967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921678937067144780687311 5882518405600717171030967)
          ·
            refine ⟨8823777608401075756546451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882518405600717171030967 8823777608401075756546451)
            ·
              refine ⟨13235666412601613634819677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8823777608401075756546451 13235666412601613634819677)
              ·
                refine ⟨4963374904725605113057379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13235666412601613634819677 4963374904725605113057379)
                ·
                  refine ⟨7445062357088407669586069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963374904725605113057379 7445062357088407669586069)
                  ·
                    refine ⟨348987297988519109511847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7445062357088407669586069 348987297988519109511847)
                    ·
                      rfl

theorem cell23_2038951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2038951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038951 prefixEnd_2038951 := by exact prefixLift 2038951
  have htrace : WordTrace (prefixWord ++ tailWord_2038951) baseStart_2038951 baseEnd_2038951 := by
    simpa [prefixWord, tailWord_2038951, baseEnd_2038951] using wordTrace_append hprefix tailTrace_2038951
  have hstable : (prefixWord ++ tailWord_2038951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038951).length < 2 ^ (prefixWord ++ tailWord_2038951).sum := by decide
  have hdescent : baseEnd_2038951 < baseStart_2038951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2038975 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 1, 2, 2]
def baseStart_2038975 : Nat := 118140960795 + 2038975 * 2 ^ 59
def prefixEnd_2038975 : Nat := 4983230072969 + 3 ^ 40 * 2038975 * 2
def baseEnd_2038975 : Nat := 1046974217501265234635431

theorem tailTrace_2038975 : CollatzResearch.WordTrace tailWord_2038975 prefixEnd_2038975 1046974217501265234635431 := by
  unfold tailWord_2038975
  simp only [CollatzResearch.WordTrace]
  refine ⟨74367527788149279051166379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49578351858766186034110919 74367527788149279051166379)
  ·
    refine ⟨111551291682223918576749569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74367527788149279051166379 111551291682223918576749569)
    ·
      refine ⟨83663468761667938932562177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111551291682223918576749569 83663468761667938932562177)
      ·
        refine ⟨62747601571250954199421633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83663468761667938932562177 62747601571250954199421633)
        ·
          refine ⟨47060701178438215649566225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62747601571250954199421633 47060701178438215649566225)
          ·
            refine ⟨35295525883828661737174669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47060701178438215649566225 35295525883828661737174669)
            ·
              refine ⟨13235822206435748151440501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35295525883828661737174669 13235822206435748151440501)
              ·
                refine ⟨1240858331853351389197547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13235822206435748151440501 1240858331853351389197547)
                ·
                  refine ⟨1861287497780027083796321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240858331853351389197547 1861287497780027083796321)
                  ·
                    refine ⟨1395965623335020312847241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861287497780027083796321 1395965623335020312847241)
                    ·
                      refine ⟨1046974217501265234635431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1395965623335020312847241 1046974217501265234635431)
                      ·
                        rfl

theorem cell23_2038975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_2038975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2038975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2038975 prefixEnd_2038975 := by exact prefixLift 2038975
  have htrace : WordTrace (prefixWord ++ tailWord_2038975) baseStart_2038975 baseEnd_2038975 := by
    simpa [prefixWord, tailWord_2038975, baseEnd_2038975] using wordTrace_append hprefix tailTrace_2038975
  have hstable : (prefixWord ++ tailWord_2038975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2038975).length < 2 ^ (prefixWord ++ tailWord_2038975).sum := by decide
  have hdescent : baseEnd_2038975 < baseStart_2038975 := by decide
  rcases family_descends (prefixWord ++ tailWord_2038975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039005 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2039005 : Nat := 118140960795 + 2039005 * 2 ^ 59
def prefixEnd_2039005 : Nat := 4983230072969 + 3 ^ 40 * 2039005 * 2
def baseEnd_2039005 : Nat := 1046989621920900117260293

theorem tailTrace_2039005 : CollatzResearch.WordTrace tailWord_2039005 prefixEnd_2039005 1046989621920900117260293 := by
  unfold tailWord_2039005
  simp only [CollatzResearch.WordTrace]
  refine ⟨74368621978040594174758469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49579081318693729449838979 74368621978040594174758469)
  ·
    refine ⟨13944116620882611407767213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74368621978040594174758469 13944116620882611407767213)
    ·
      refine ⟨5229043732830979277912705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13944116620882611407767213 5229043732830979277912705)
      ·
        refine ⟨3921782799623234458434529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5229043732830979277912705 3921782799623234458434529)
        ·
          refine ⟨2941337099717425843825897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3921782799623234458434529 2941337099717425843825897)
          ·
            refine ⟨2206002824788069382869423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2941337099717425843825897 2206002824788069382869423)
            ·
              refine ⟨3309004237182104074304135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206002824788069382869423 3309004237182104074304135)
              ·
                refine ⟨4963506355773156111456203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309004237182104074304135 4963506355773156111456203)
                ·
                  refine ⟨7445259533659734167184305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963506355773156111456203 7445259533659734167184305)
                  ·
                    refine ⟨5583944650244800625388229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7445259533659734167184305 5583944650244800625388229)
                    ·
                      refine ⟨1046989621920900117260293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5583944650244800625388229 1046989621920900117260293)
                      ·
                        rfl

theorem cell23_2039005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2039005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039005 prefixEnd_2039005 := by exact prefixLift 2039005
  have htrace : WordTrace (prefixWord ++ tailWord_2039005) baseStart_2039005 baseEnd_2039005 := by
    simpa [prefixWord, tailWord_2039005, baseEnd_2039005] using wordTrace_append hprefix tailTrace_2039005
  have hstable : (prefixWord ++ tailWord_2039005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039005).length < 2 ^ (prefixWord ++ tailWord_2039005).sum := by decide
  have hdescent : baseEnd_2039005 < baseStart_2039005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039008 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3]
def baseStart_2039008 : Nat := 118140960795 + 2039008 * 2 ^ 59
def prefixEnd_2039008 : Nat := 4983230072969 + 3 ^ 40 * 2039008 * 2
def baseEnd_2039008 : Nat := 1046991162362863605522779

theorem tailTrace_2039008 : CollatzResearch.WordTrace tailWord_2039008 prefixEnd_2039008 1046991162362863605522779 := by
  unfold tailWord_2039008
  simp only [CollatzResearch.WordTrace]
  refine ⟨37184365698514862843558839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49579154264686483791411785 37184365698514862843558839)
  ·
    refine ⟨55776548547772294265338259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37184365698514862843558839 55776548547772294265338259)
    ·
      refine ⟨83664822821658441398007389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55776548547772294265338259 83664822821658441398007389)
      ·
        refine ⟨31374308558121915524252771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83664822821658441398007389 31374308558121915524252771)
        ·
          refine ⟨47061462837182873286379157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31374308558121915524252771 47061462837182873286379157)
          ·
            refine ⟨2206006070492947185299023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47061462837182873286379157 2206006070492947185299023)
            ·
              refine ⟨3309009105739420777948535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206006070492947185299023 3309009105739420777948535)
              ·
                refine ⟨4963513658609131166922803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309009105739420777948535 4963513658609131166922803)
                ·
                  refine ⟨7445270487913696750384205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963513658609131166922803 7445270487913696750384205)
                  ·
                    refine ⟨2791976432967636281394077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7445270487913696750384205 2791976432967636281394077)
                    ·
                      refine ⟨1046991162362863605522779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2791976432967636281394077 1046991162362863605522779)
                      ·
                        rfl

theorem cell23_2039008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_2039008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039008 prefixEnd_2039008 := by exact prefixLift 2039008
  have htrace : WordTrace (prefixWord ++ tailWord_2039008) baseStart_2039008 baseEnd_2039008 := by
    simpa [prefixWord, tailWord_2039008, baseEnd_2039008] using wordTrace_append hprefix tailTrace_2039008
  have hstable : (prefixWord ++ tailWord_2039008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039008).length < 2 ^ (prefixWord ++ tailWord_2039008).sum := by decide
  have hdescent : baseEnd_2039008 < baseStart_2039008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039015 : List Nat := [1, 1, 5, 3, 3, 1, 2, 7]
def baseStart_2039015 : Nat := 118140960795 + 2039015 * 2 ^ 59
def prefixEnd_2039015 : Nat := 4983230072969 + 3 ^ 40 * 2039015 * 2
def baseEnd_2039015 : Nat := 38777583582497965856861

theorem tailTrace_2039015 : CollatzResearch.WordTrace tailWord_2039015 prefixEnd_2039015 38777583582497965856861 := by
  unfold tailWord_2039015
  simp only [CollatzResearch.WordTrace]
  refine ⟨74368986708004365882622499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49579324472002910588414999 74368986708004365882622499)
  ·
    refine ⟨111553480062006548823933749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74368986708004365882622499 111553480062006548823933749)
    ·
      refine ⟨10458138755813113952243789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111553480062006548823933749 10458138755813113952243789)
      ·
        refine ⟨3921802033429917732091421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10458138755813113952243789 3921802033429917732091421)
        ·
          refine ⟨1470675762536219149534283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3921802033429917732091421 1470675762536219149534283)
          ·
            refine ⟨2206013643804328724301425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470675762536219149534283 2206013643804328724301425)
            ·
              refine ⟨1654510232853246543226069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2206013643804328724301425 1654510232853246543226069)
              ·
                refine ⟨38777583582497965856861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1654510232853246543226069 38777583582497965856861)
                ·
                  rfl

theorem cell23_2039015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 2, 7].length) (baseStart_2039015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039015 prefixEnd_2039015 := by exact prefixLift 2039015
  have htrace : WordTrace (prefixWord ++ tailWord_2039015) baseStart_2039015 baseEnd_2039015 := by
    simpa [prefixWord, tailWord_2039015, baseEnd_2039015] using wordTrace_append hprefix tailTrace_2039015
  have hstable : (prefixWord ++ tailWord_2039015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039015).length < 2 ^ (prefixWord ++ tailWord_2039015).sum := by decide
  have hdescent : baseEnd_2039015 < baseStart_2039015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039021 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2039021 : Nat := 118140960795 + 2039021 * 2 ^ 59
def prefixEnd_2039021 : Nat := 4983230072969 + 3 ^ 40 * 2039021 * 2
def baseEnd_2039021 : Nat := 1046997837611372054660219

theorem tailTrace_2039021 : CollatzResearch.WordTrace tailWord_2039021 prefixEnd_2039021 1046997837611372054660219 := by
  unfold tailWord_2039021
  simp only [CollatzResearch.WordTrace]
  refine ⟨74369205545982628907340917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49579470363988419271560611 74369205545982628907340917)
  ·
    refine ⟨6972113019935871460063211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74369205545982628907340917 6972113019935871460063211)
    ·
      refine ⟨10458169529903807190094817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6972113019935871460063211 10458169529903807190094817)
      ·
        refine ⟨7843627147427855392571113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10458169529903807190094817 7843627147427855392571113)
        ·
          refine ⟨5882720360570891544428335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7843627147427855392571113 5882720360570891544428335)
          ·
            refine ⟨8824080540856337316642503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882720360570891544428335 8824080540856337316642503)
            ·
              refine ⟨13236120811284505974963755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8824080540856337316642503 13236120811284505974963755)
              ·
                refine ⟨19854181216926758962445633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13236120811284505974963755 19854181216926758962445633)
                ·
                  refine ⟨14890635912695069221834225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19854181216926758962445633 14890635912695069221834225)
                  ·
                    refine ⟨11167976934521301916375669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14890635912695069221834225 11167976934521301916375669)
                    ·
                      refine ⟨1046997837611372054660219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11167976934521301916375669 1046997837611372054660219)
                      ·
                        rfl

theorem cell23_2039021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2039021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039021 prefixEnd_2039021 := by exact prefixLift 2039021
  have htrace : WordTrace (prefixWord ++ tailWord_2039021) baseStart_2039021 baseEnd_2039021 := by
    simpa [prefixWord, tailWord_2039021, baseEnd_2039021] using wordTrace_append hprefix tailTrace_2039021
  have hstable : (prefixWord ++ tailWord_2039021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039021).length < 2 ^ (prefixWord ++ tailWord_2039021).sum := by decide
  have hdescent : baseEnd_2039021 < baseStart_2039021 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039026 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 1, 2, 2]
def baseStart_2039026 : Nat := 118140960795 + 2039026 * 2 ^ 59
def prefixEnd_2039026 : Nat := 4983230072969 + 3 ^ 40 * 2039026 * 2
def baseEnd_2039026 : Nat := 1047000405014644535097697

theorem tailTrace_2039026 : CollatzResearch.WordTrace tailWord_2039026 prefixEnd_2039026 1047000405014644535097697 := by
  unfold tailWord_2039026
  simp only [CollatzResearch.WordTrace]
  refine ⟨18592346977741128690318233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49579591940643009840848621 18592346977741128690318233)
  ·
    refine ⟨13944260233305846517738675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18592346977741128690318233 13944260233305846517738675)
    ·
      refine ⟨20916390349958769776608013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13944260233305846517738675 20916390349958769776608013)
      ·
        refine ⟨7843646381234538666228005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20916390349958769776608013 7843646381234538666228005)
        ·
          refine ⟨1470683696481475999917751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7843646381234538666228005 1470683696481475999917751)
          ·
            refine ⟨2206025544722213999876627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470683696481475999917751 2206025544722213999876627)
            ·
              refine ⟨3309038317083320999814941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206025544722213999876627 3309038317083320999814941)
              ·
                refine ⟨1240889368906245374930603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309038317083320999814941 1240889368906245374930603)
                ·
                  refine ⟨1861334053359368062395905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240889368906245374930603 1861334053359368062395905)
                  ·
                    refine ⟨1396000540019526046796929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861334053359368062395905 1396000540019526046796929)
                    ·
                      refine ⟨1047000405014644535097697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396000540019526046796929 1047000405014644535097697)
                      ·
                        rfl

theorem cell23_2039026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_2039026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039026 prefixEnd_2039026 := by exact prefixLift 2039026
  have htrace : WordTrace (prefixWord ++ tailWord_2039026) baseStart_2039026 baseEnd_2039026 := by
    simpa [prefixWord, tailWord_2039026, baseEnd_2039026] using wordTrace_append hprefix tailTrace_2039026
  have hstable : (prefixWord ++ tailWord_2039026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039026).length < 2 ^ (prefixWord ++ tailWord_2039026).sum := by decide
  have hdescent : baseEnd_2039026 < baseStart_2039026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039105 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 5]
def baseStart_2039105 : Nat := 118140960795 + 2039105 * 2 ^ 59
def prefixEnd_2039105 : Nat := 4983230072969 + 3 ^ 40 * 2039105 * 2
def baseEnd_2039105 : Nat := 116337885554038858445537

theorem tailTrace_2039105 : CollatzResearch.WordTrace tailWord_2039105 prefixEnd_2039105 116337885554038858445537 := by
  unfold tailWord_2039105
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372269277678311253398769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49581512851785540835599179 74372269277678311253398769)
  ·
    refine ⟨55779201958258733440049077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74372269277678311253398769 55779201958258733440049077)
    ·
      refine ⟨5229300183586756260004601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55779201958258733440049077 5229300183586756260004601)
      ·
        refine ⟨3921975137690067195003451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5229300183586756260004601 3921975137690067195003451)
        ·
          refine ⟨5882962706535100792505177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921975137690067195003451 5882962706535100792505177)
          ·
            refine ⟨4412222029901325594378883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882962706535100792505177 4412222029901325594378883)
            ·
              refine ⟨6618333044851988391568325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4412222029901325594378883 6618333044851988391568325)
              ·
                refine ⟨1240937445909747823419061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6618333044851988391568325 1240937445909747823419061)
                ·
                  refine ⟨116337885554038858445537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1240937445909747823419061 116337885554038858445537)
                  ·
                    rfl

theorem cell23_2039105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 5].length) (baseStart_2039105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039105 prefixEnd_2039105 := by exact prefixLift 2039105
  have htrace : WordTrace (prefixWord ++ tailWord_2039105) baseStart_2039105 baseEnd_2039105 := by
    simpa [prefixWord, tailWord_2039105, baseEnd_2039105] using wordTrace_append hprefix tailTrace_2039105
  have hstable : (prefixWord ++ tailWord_2039105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039105).length < 2 ^ (prefixWord ++ tailWord_2039105).sum := by decide
  have hdescent : baseEnd_2039105 < baseStart_2039105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039111 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_2039111 : Nat := 118140960795 + 2039111 * 2 ^ 59
def prefixEnd_2039111 : Nat := 4983230072969 + 3 ^ 40 * 2039111 * 2
def baseEnd_2039111 : Nat := 1047044050870276702534805

theorem tailTrace_2039111 : CollatzResearch.WordTrace tailWord_2039111 prefixEnd_2039111 1047044050870276702534805 := by
  unfold tailWord_2039111
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372488115656574278117187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49581658743771049518744791 74372488115656574278117187)
  ·
    refine ⟨111558732173484861417175781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74372488115656574278117187 111558732173484861417175781)
    ·
      refine ⟨20917262282528411515720459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111558732173484861417175781 20917262282528411515720459)
      ·
        refine ⟨31375893423792617273580689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20917262282528411515720459 31375893423792617273580689)
        ·
          refine ⟨23531920067844462955185517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31375893423792617273580689 23531920067844462955185517)
          ·
            refine ⟨8824470025441673608194569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23531920067844462955185517 8824470025441673608194569)
            ·
              refine ⟨6618352519081255206145927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8824470025441673608194569 6618352519081255206145927)
              ·
                refine ⟨9927528778621882809218891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6618352519081255206145927 9927528778621882809218891)
                ·
                  refine ⟨14891293167932824213828337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9927528778621882809218891 14891293167932824213828337)
                  ·
                    refine ⟨11168469875949618160371253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14891293167932824213828337 11168469875949618160371253)
                    ·
                      refine ⟨1047044050870276702534805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11168469875949618160371253 1047044050870276702534805)
                      ·
                        rfl

theorem cell23_2039111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_2039111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039111 prefixEnd_2039111 := by exact prefixLift 2039111
  have htrace : WordTrace (prefixWord ++ tailWord_2039111) baseStart_2039111 baseEnd_2039111 := by
    simpa [prefixWord, tailWord_2039111, baseEnd_2039111] using wordTrace_append hprefix tailTrace_2039111
  have hstable : (prefixWord ++ tailWord_2039111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039111).length < 2 ^ (prefixWord ++ tailWord_2039111).sum := by decide
  have hdescent : baseEnd_2039111 < baseStart_2039111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039121 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_2039121 : Nat := 118140960795 + 2039121 * 2 ^ 59
def prefixEnd_2039121 : Nat := 4983230072969 + 3 ^ 40 * 2039121 * 2
def baseEnd_2039121 : Nat := 1047049185676821663409759

theorem tailTrace_2039121 : CollatzResearch.WordTrace tailWord_2039121 prefixEnd_2039121 1047049185676821663409759 := by
  unfold tailWord_2039121
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372852845620345985981217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49581901897080230657320811 74372852845620345985981217)
  ·
    refine ⟨55779639634215259489485913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74372852845620345985981217 55779639634215259489485913)
    ·
      refine ⟨41834729725661444617114435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55779639634215259489485913 41834729725661444617114435)
      ·
        refine ⟨62752094588492166925671653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41834729725661444617114435 62752094588492166925671653)
        ·
          refine ⟨11766017735342281298563435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62752094588492166925671653 11766017735342281298563435)
          ·
            refine ⟨17649026603013421947845153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766017735342281298563435 17649026603013421947845153)
            ·
              refine ⟨13236769952260066460883865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17649026603013421947845153 13236769952260066460883865)
              ·
                refine ⟨9927577464195049845662899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13236769952260066460883865 9927577464195049845662899)
                ·
                  refine ⟨14891366196292574768494349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9927577464195049845662899 14891366196292574768494349)
                  ·
                    refine ⟨5584262323609715538185381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14891366196292574768494349 5584262323609715538185381)
                    ·
                      refine ⟨1047049185676821663409759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5584262323609715538185381 1047049185676821663409759)
                      ·
                        rfl

theorem cell23_2039121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_2039121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039121 prefixEnd_2039121 := by exact prefixLift 2039121
  have htrace : WordTrace (prefixWord ++ tailWord_2039121) baseStart_2039121 baseEnd_2039121 := by
    simpa [prefixWord, tailWord_2039121, baseEnd_2039121] using wordTrace_append hprefix tailTrace_2039121
  have hstable : (prefixWord ++ tailWord_2039121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039121).length < 2 ^ (prefixWord ++ tailWord_2039121).sum := by decide
  have hdescent : baseEnd_2039121 < baseStart_2039121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039138 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2039138 : Nat := 118140960795 + 2039138 * 2 ^ 59
def prefixEnd_2039138 : Nat := 4983230072969 + 3 ^ 40 * 2039138 * 2
def baseEnd_2039138 : Nat := 1047057914847948096897181

theorem tailTrace_2039138 : CollatzResearch.WordTrace tailWord_2039138 prefixEnd_2039138 1047057914847948096897181 := by
  unfold tailWord_2039138
  simp only [CollatzResearch.WordTrace]
  refine ⟨18593368221639689472337517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49582315257705838592900045 18593368221639689472337517)
  ·
    refine ⟨6972513083114883552126569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18593368221639689472337517 6972513083114883552126569)
    ·
      refine ⟨5229384812336162664094927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6972513083114883552126569 5229384812336162664094927)
      ·
        refine ⟨7844077218504243996142391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229384812336162664094927 7844077218504243996142391)
        ·
          refine ⟨11766115827756365994213587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7844077218504243996142391 11766115827756365994213587)
          ·
            refine ⟨17649173741634548991320381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766115827756365994213587 17649173741634548991320381)
            ·
              refine ⟨6618440153112955871745143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17649173741634548991320381 6618440153112955871745143)
              ·
                refine ⟨9927660229669433807617715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6618440153112955871745143 9927660229669433807617715)
                ·
                  refine ⟨14891490344504150711426573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9927660229669433807617715 14891490344504150711426573)
                  ·
                    refine ⟨5584308879189056516784965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14891490344504150711426573 5584308879189056516784965)
                    ·
                      refine ⟨1047057914847948096897181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5584308879189056516784965 1047057914847948096897181)
                      ·
                        rfl

theorem cell23_2039138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2039138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039138 prefixEnd_2039138 := by exact prefixLift 2039138
  have htrace : WordTrace (prefixWord ++ tailWord_2039138) baseStart_2039138 baseEnd_2039138 := by
    simpa [prefixWord, tailWord_2039138, baseEnd_2039138] using wordTrace_append hprefix tailTrace_2039138
  have hstable : (prefixWord ++ tailWord_2039138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039138).length < 2 ^ (prefixWord ++ tailWord_2039138).sum := by decide
  have hdescent : baseEnd_2039138 < baseStart_2039138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039165 : List Nat := [1, 4, 1, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2039165 : Nat := 118140960795 + 2039165 * 2 ^ 59
def prefixEnd_2039165 : Nat := 4983230072969 + 3 ^ 40 * 2039165 * 2
def baseEnd_2039165 : Nat := 349023926275206497086519

theorem tailTrace_2039165 : CollatzResearch.WordTrace tailWord_2039165 prefixEnd_2039165 349023926275206497086519 := by
  unfold tailWord_2039165
  simp only [CollatzResearch.WordTrace]
  refine ⟨74374457657460941500582949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49582971771640627667055299 74374457657460941500582949)
  ·
    refine ⟨13945210810773926531359303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74374457657460941500582949 13945210810773926531359303)
    ·
      refine ⟨20917816216160889797038955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13945210810773926531359303 20917816216160889797038955)
      ·
        refine ⟨31376724324241334695558433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20917816216160889797038955 31376724324241334695558433)
        ·
          refine ⟨23532543243181001021668825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31376724324241334695558433 23532543243181001021668825)
          ·
            refine ⟨17649407432385750766251619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23532543243181001021668825 17649407432385750766251619)
            ·
              refine ⟨26474111148578626149377429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17649407432385750766251619 26474111148578626149377429)
              ·
                refine ⟨1240973960089623100752067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26474111148578626149377429 1240973960089623100752067)
                ·
                  refine ⟨1861460940134434651128101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1240973960089623100752067 1861460940134434651128101)
                  ·
                    refine ⟨349023926275206497086519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1861460940134434651128101 349023926275206497086519)
                    ·
                      rfl

theorem cell23_2039165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2039165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039165 prefixEnd_2039165 := by exact prefixLift 2039165
  have htrace : WordTrace (prefixWord ++ tailWord_2039165) baseStart_2039165 baseEnd_2039165 := by
    simpa [prefixWord, tailWord_2039165, baseEnd_2039165] using wordTrace_append hprefix tailTrace_2039165
  have hstable : (prefixWord ++ tailWord_2039165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039165).length < 2 ^ (prefixWord ++ tailWord_2039165).sum := by decide
  have hdescent : baseEnd_2039165 < baseStart_2039165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039248 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3]
def baseStart_2039248 : Nat := 118140960795 + 2039248 * 2 ^ 59
def prefixEnd_2039248 : Nat := 4983230072969 + 3 ^ 40 * 2039248 * 2
def baseEnd_2039248 : Nat := 1047114397719942666521675

theorem tailTrace_2039248 : CollatzResearch.WordTrace tailWord_2039248 prefixEnd_2039248 1047114397719942666521675 := by
  unfold tailWord_2039248
  simp only [CollatzResearch.WordTrace]
  refine ⟨37188742458080123337927199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49584989944106831117236265 37188742458080123337927199)
  ·
    refine ⟨55783113687120185006890799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37188742458080123337927199 55783113687120185006890799)
    ·
      refine ⟨83674670530680277510336199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55783113687120185006890799 83674670530680277510336199)
      ·
        refine ⟨125512005796020416265504299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83674670530680277510336199 125512005796020416265504299)
        ·
          refine ⟨188268008694030624398256449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125512005796020416265504299 188268008694030624398256449)
          ·
            refine ⟨141201006520522968298692337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188268008694030624398256449 141201006520522968298692337)
            ·
              refine ⟨105900754890392226224019253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141201006520522968298692337 105900754890392226224019253)
              ·
                refine ⟨9928195770974271208501805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105900754890392226224019253 9928195770974271208501805)
                ·
                  refine ⟨3723073414115351703188177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9928195770974271208501805 3723073414115351703188177)
                  ·
                    refine ⟨2792305060586513777391133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3723073414115351703188177 2792305060586513777391133)
                    ·
                      refine ⟨1047114397719942666521675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2792305060586513777391133 1047114397719942666521675)
                      ·
                        rfl

theorem cell23_2039248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_2039248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039248 prefixEnd_2039248 := by exact prefixLift 2039248
  have htrace : WordTrace (prefixWord ++ tailWord_2039248) baseStart_2039248 baseEnd_2039248 := by
    simpa [prefixWord, tailWord_2039248, baseEnd_2039248] using wordTrace_append hprefix tailTrace_2039248
  have hstable : (prefixWord ++ tailWord_2039248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039248).length < 2 ^ (prefixWord ++ tailWord_2039248).sum := by decide
  have hdescent : baseEnd_2039248 < baseStart_2039248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039258 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_2039258 : Nat := 118140960795 + 2039258 * 2 ^ 59
def prefixEnd_2039258 : Nat := 4983230072969 + 3 ^ 40 * 2039258 * 2
def baseEnd_2039258 : Nat := 1047119532526487627396629

theorem tailTrace_2039258 : CollatzResearch.WordTrace tailWord_2039258 prefixEnd_2039258 1047119532526487627396629 := by
  unfold tailWord_2039258
  simp only [CollatzResearch.WordTrace]
  refine ⟨18594462411531004595929607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49585233097416012255812285 18594462411531004595929607)
  ·
    refine ⟨27891693617296506893894411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18594462411531004595929607 27891693617296506893894411)
    ·
      refine ⟨41837540425944760340841617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27891693617296506893894411 41837540425944760340841617)
      ·
        refine ⟨31378155319458570255631213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41837540425944760340841617 31378155319458570255631213)
        ·
          refine ⟨11766808244796963845861705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31378155319458570255631213 11766808244796963845861705)
          ·
            refine ⟨8825106183597722884396279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11766808244796963845861705 8825106183597722884396279)
            ·
              refine ⟨13237659275396584326594419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8825106183597722884396279 13237659275396584326594419)
              ·
                refine ⟨19856488913094876489891629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13237659275396584326594419 19856488913094876489891629)
                ·
                  refine ⟨7446183342410578683709361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19856488913094876489891629 7446183342410578683709361)
                  ·
                    refine ⟨5584637506807934012782021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7446183342410578683709361 5584637506807934012782021)
                    ·
                      refine ⟨1047119532526487627396629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5584637506807934012782021 1047119532526487627396629)
                      ·
                        rfl

theorem cell23_2039258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_2039258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039258 prefixEnd_2039258 := by exact prefixLift 2039258
  have htrace : WordTrace (prefixWord ++ tailWord_2039258) baseStart_2039258 baseEnd_2039258 := by
    simpa [prefixWord, tailWord_2039258, baseEnd_2039258] using wordTrace_append hprefix tailTrace_2039258
  have hstable : (prefixWord ++ tailWord_2039258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039258).length < 2 ^ (prefixWord ++ tailWord_2039258).sum := by decide
  have hdescent : baseEnd_2039258 < baseStart_2039258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039265 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 5]
def baseStart_2039265 : Nat := 118140960795 + 2039265 * 2 ^ 59
def prefixEnd_2039265 : Nat := 4983230072969 + 3 ^ 40 * 2039265 * 2
def baseEnd_2039265 : Nat := 1047123126891069100009097

theorem tailTrace_2039265 : CollatzResearch.WordTrace tailWord_2039265 prefixEnd_2039265 1047123126891069100009097 := by
  unfold tailWord_2039265
  simp only [CollatzResearch.WordTrace]
  refine ⟨74378104957098658579223249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49585403304732439052815499 74378104957098658579223249)
  ·
    refine ⟨55783578717823993934417437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74378104957098658579223249 55783578717823993934417437)
    ·
      refine ⟨20918842019183997725406539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55783578717823993934417437 20918842019183997725406539)
      ·
        refine ⟨31378263028775996588109809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20918842019183997725406539 31378263028775996588109809)
        ·
          refine ⟨23533697271581997441082357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31378263028775996588109809 23533697271581997441082357)
          ·
            refine ⟨2206284119210812260101471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23533697271581997441082357 2206284119210812260101471)
            ·
              refine ⟨3309426178816218390152207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206284119210812260101471 3309426178816218390152207)
              ·
                refine ⟨4964139268224327585228311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309426178816218390152207 4964139268224327585228311)
                ·
                  refine ⟨7446208902336491377842467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964139268224327585228311 7446208902336491377842467)
                  ·
                    refine ⟨11169313353504737066763701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7446208902336491377842467 11169313353504737066763701)
                    ·
                      refine ⟨1047123126891069100009097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11169313353504737066763701 1047123126891069100009097)
                      ·
                        rfl

theorem cell23_2039265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_2039265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039265 prefixEnd_2039265 := by exact prefixLift 2039265
  have htrace : WordTrace (prefixWord ++ tailWord_2039265) baseStart_2039265 baseEnd_2039265 := by
    simpa [prefixWord, tailWord_2039265, baseEnd_2039265] using wordTrace_append hprefix tailTrace_2039265
  have hstable : (prefixWord ++ tailWord_2039265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039265).length < 2 ^ (prefixWord ++ tailWord_2039265).sum := by decide
  have hdescent : baseEnd_2039265 < baseStart_2039265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039285 : List Nat := [1, 3, 5, 1, 1, 1, 3, 8]
def baseStart_2039285 : Nat := 118140960795 + 2039285 * 2 ^ 59
def prefixEnd_2039285 : Nat := 4983230072969 + 3 ^ 40 * 2039285 * 2
def baseEnd_2039285 : Nat := 38782718389042926731815

theorem tailTrace_2039285 : CollatzResearch.WordTrace tailWord_2039285 prefixEnd_2039285 38782718389042926731815 := by
  unfold tailWord_2039285
  simp only [CollatzResearch.WordTrace]
  refine ⟨74378834417026201994951309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49585889611350801329967539 74378834417026201994951309)
  ·
    refine ⟨27892062906384825748106741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74378834417026201994951309 27892062906384825748106741)
    ·
      refine ⟨2614880897473577413885007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27892062906384825748106741 2614880897473577413885007)
      ·
        refine ⟨3922321346210366120827511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2614880897473577413885007 3922321346210366120827511)
        ·
          refine ⟨5883482019315549181241267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3922321346210366120827511 5883482019315549181241267)
          ·
            refine ⟨8825223028973323771861901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883482019315549181241267 8825223028973323771861901)
            ·
              refine ⟨3309458635864996414448213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8825223028973323771861901 3309458635864996414448213)
              ·
                refine ⟨38782718389042926731815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3309458635864996414448213 38782718389042926731815)
                ·
                  rfl

theorem cell23_2039285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 8].length) (baseStart_2039285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039285 prefixEnd_2039285 := by exact prefixLift 2039285
  have htrace : WordTrace (prefixWord ++ tailWord_2039285) baseStart_2039285 baseEnd_2039285 := by
    simpa [prefixWord, tailWord_2039285, baseEnd_2039285] using wordTrace_append hprefix tailTrace_2039285
  have hstable : (prefixWord ++ tailWord_2039285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039285).length < 2 ^ (prefixWord ++ tailWord_2039285).sum := by decide
  have hdescent : baseEnd_2039285 < baseStart_2039285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039305 : List Nat := [1, 2, 1, 1, 3, 1, 3, 3, 3, 3, 2]
def baseStart_2039305 : Nat := 118140960795 + 2039305 * 2 ^ 59
def prefixEnd_2039305 : Nat := 4983230072969 + 3 ^ 40 * 2039305 * 2
def baseEnd_2039305 : Nat := 1047143666117248943508913

theorem tailTrace_2039305 : CollatzResearch.WordTrace tailWord_2039305 prefixEnd_2039305 1047143666117248943508913 := by
  unfold tailWord_2039305
  simp only [CollatzResearch.WordTrace]
  refine ⟨74379563876953745410679369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49586375917969163607119579 74379563876953745410679369)
  ·
    refine ⟨55784672907715309058009527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74379563876953745410679369 55784672907715309058009527)
    ·
      refine ⟨83677009361572963587014291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55784672907715309058009527 83677009361572963587014291)
      ·
        refine ⟨125515514042359445380521437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83677009361572963587014291 125515514042359445380521437)
        ·
          refine ⟨47068317765884792017695539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125515514042359445380521437 47068317765884792017695539)
          ·
            refine ⟨70602476648827188026543309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47068317765884792017695539 70602476648827188026543309)
            ·
              refine ⟨26475928743310195509953741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70602476648827188026543309 26475928743310195509953741)
              ·
                refine ⟨9928473278741323316232653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26475928743310195509953741 9928473278741323316232653)
                ·
                  refine ⟨3723177479527996243587245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9928473278741323316232653 3723177479527996243587245)
                  ·
                    refine ⟨1396191554822998591345217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3723177479527996243587245 1396191554822998591345217)
                    ·
                      refine ⟨1047143666117248943508913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396191554822998591345217 1047143666117248943508913)
                      ·
                        rfl

theorem cell23_2039305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 3, 2].length) (baseStart_2039305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039305 prefixEnd_2039305 := by exact prefixLift 2039305
  have htrace : WordTrace (prefixWord ++ tailWord_2039305) baseStart_2039305 baseEnd_2039305 := by
    simpa [prefixWord, tailWord_2039305, baseEnd_2039305] using wordTrace_append hprefix tailTrace_2039305
  have hstable : (prefixWord ++ tailWord_2039305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039305).length < 2 ^ (prefixWord ++ tailWord_2039305).sum := by decide
  have hdescent : baseEnd_2039305 < baseStart_2039305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039329 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2039329 : Nat := 118140960795 + 2039329 * 2 ^ 59
def prefixEnd_2039329 : Nat := 4983230072969 + 3 ^ 40 * 2039329 * 2
def baseEnd_2039329 : Nat := 1047155989652956849608803

theorem tailTrace_2039329 : CollatzResearch.WordTrace tailWord_2039329 prefixEnd_2039329 1047155989652956849608803 := by
  unfold tailWord_2039329
  simp only [CollatzResearch.WordTrace]
  refine ⟨74380439228866797509553041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49586959485911198339702027 74380439228866797509553041)
  ·
    refine ⟨55785329421650098132164781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74380439228866797509553041 55785329421650098132164781)
    ·
      refine ⟨20919498533118786799561793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55785329421650098132164781 20919498533118786799561793)
      ·
        refine ⟨15689623899839090099671345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20919498533118786799561793 15689623899839090099671345)
        ·
          refine ⟨11767217924879317574753509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15689623899839090099671345 11767217924879317574753509)
          ·
            refine ⟨2206353360914872045266283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11767217924879317574753509 2206353360914872045266283)
            ·
              refine ⟨3309530041372308067899425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206353360914872045266283 3309530041372308067899425)
              ·
                refine ⟨2482147531029231050924569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309530041372308067899425 2482147531029231050924569)
                ·
                  refine ⟨1861610648271923288193427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2482147531029231050924569 1861610648271923288193427)
                  ·
                    refine ⟨2792415972407884932290141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1861610648271923288193427 2792415972407884932290141)
                    ·
                      refine ⟨1047155989652956849608803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2792415972407884932290141 1047155989652956849608803)
                      ·
                        rfl

theorem cell23_2039329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2039329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039329 prefixEnd_2039329 := by exact prefixLift 2039329
  have htrace : WordTrace (prefixWord ++ tailWord_2039329) baseStart_2039329 baseEnd_2039329 := by
    simpa [prefixWord, tailWord_2039329, baseEnd_2039329] using wordTrace_append hprefix tailTrace_2039329
  have hstable : (prefixWord ++ tailWord_2039329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039329).length < 2 ^ (prefixWord ++ tailWord_2039329).sum := by decide
  have hdescent : baseEnd_2039329 < baseStart_2039329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039352 : List Nat := [2, 1, 2, 1, 4, 2, 3, 1, 1, 4, 2]
def baseStart_2039352 : Nat := 118140960795 + 2039352 * 2 ^ 59
def prefixEnd_2039352 : Nat := 4983230072969 + 3 ^ 40 * 2039352 * 2
def baseEnd_2039352 : Nat := 1047167799708010259621197

theorem tailTrace_2039352 : CollatzResearch.WordTrace tailWord_2039352 prefixEnd_2039352 1047167799708010259621197 := by
  unfold tailWord_2039352
  simp only [CollatzResearch.WordTrace]
  refine ⟨37190639053891736218820155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49587518738522314958426873 37190639053891736218820155)
  ·
    refine ⟨55785958580837604328230233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37190639053891736218820155 55785958580837604328230233)
    ·
      refine ⟨41839468935628203246172675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55785958580837604328230233 41839468935628203246172675)
      ·
        refine ⟨62759203403442304869259013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41839468935628203246172675 62759203403442304869259013)
        ·
          refine ⟨11767350638145432162986065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62759203403442304869259013 11767350638145432162986065)
          ·
            refine ⟨8825512978609074122239549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11767350638145432162986065 8825512978609074122239549)
            ·
              refine ⟨3309567366978402795839831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8825512978609074122239549 3309567366978402795839831)
              ·
                refine ⟨4964351050467604193759747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309567366978402795839831 4964351050467604193759747)
                ·
                  refine ⟨7446526575701406290639621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964351050467604193759747 7446526575701406290639621)
                  ·
                    refine ⟨1396223732944013679494929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7446526575701406290639621 1396223732944013679494929)
                    ·
                      refine ⟨1047167799708010259621197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396223732944013679494929 1047167799708010259621197)
                      ·
                        rfl

theorem cell23_2039352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_2039352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039352 prefixEnd_2039352 := by exact prefixLift 2039352
  have htrace : WordTrace (prefixWord ++ tailWord_2039352) baseStart_2039352 baseEnd_2039352 := by
    simpa [prefixWord, tailWord_2039352, baseEnd_2039352] using wordTrace_append hprefix tailTrace_2039352
  have hstable : (prefixWord ++ tailWord_2039352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039352).length < 2 ^ (prefixWord ++ tailWord_2039352).sum := by decide
  have hdescent : baseEnd_2039352 < baseStart_2039352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039479 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 3]
def baseStart_2039479 : Nat := 118140960795 + 2039479 * 2 ^ 59
def prefixEnd_2039479 : Nat := 4983230072969 + 3 ^ 40 * 2039479 * 2
def baseEnd_2039479 : Nat := 1047233011751131262733113

theorem tailTrace_2039479 : CollatzResearch.WordTrace tailWord_2039479 prefixEnd_2039479 1047233011751131262733113 := by
  unfold tailWord_2039479
  simp only [CollatzResearch.WordTrace]
  refine ⟨74385910178323373127513491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49590606785548915418342327 74385910178323373127513491)
  ·
    refine ⟨111578865267485059691270237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74385910178323373127513491 111578865267485059691270237)
    ·
      refine ⟨41842074475306897384226339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111578865267485059691270237 41842074475306897384226339)
      ·
        refine ⟨62763111712960346076339509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41842074475306897384226339 62763111712960346076339509)
        ·
          refine ⟨5884041723090032444656829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62763111712960346076339509 5884041723090032444656829)
          ·
            refine ⟨2206515646158762166746311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5884041723090032444656829 2206515646158762166746311)
            ·
              refine ⟨3309773469238143250119467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206515646158762166746311 3309773469238143250119467)
              ·
                refine ⟨4964660203857214875179201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309773469238143250119467 4964660203857214875179201)
                ·
                  refine ⟨3723495152892911156384401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4964660203857214875179201 3723495152892911156384401)
                  ·
                    refine ⟨2792621364669683367288301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3723495152892911156384401 2792621364669683367288301)
                    ·
                      refine ⟨1047233011751131262733113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2792621364669683367288301 1047233011751131262733113)
                      ·
                        rfl

theorem cell23_2039479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 2, 3].length) (baseStart_2039479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039479 prefixEnd_2039479 := by exact prefixLift 2039479
  have htrace : WordTrace (prefixWord ++ tailWord_2039479) baseStart_2039479 baseEnd_2039479 := by
    simpa [prefixWord, tailWord_2039479, baseEnd_2039479] using wordTrace_append hprefix tailTrace_2039479
  have hstable : (prefixWord ++ tailWord_2039479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039479).length < 2 ^ (prefixWord ++ tailWord_2039479).sum := by decide
  have hdescent : baseEnd_2039479 < baseStart_2039479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039486 : List Nat := [4, 2, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2039486 : Nat := 118140960795 + 2039486 * 2 ^ 59
def prefixEnd_2039486 : Nat := 4983230072969 + 3 ^ 40 * 2039486 * 2
def baseEnd_2039486 : Nat := 349078868705237578448527

theorem tailTrace_2039486 : CollatzResearch.WordTrace tailWord_2039486 prefixEnd_2039486 349078868705237578448527 := by
  unfold tailWord_2039486
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298270686162251665377289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49590776992865342215345541 9298270686162251665377289)
  ·
    refine ⟨6973703014621688749032967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9298270686162251665377289 6973703014621688749032967)
    ·
      refine ⟨10460554521932533123549451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6973703014621688749032967 10460554521932533123549451)
      ·
        refine ⟨15690831782898799685324177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10460554521932533123549451 15690831782898799685324177)
        ·
          refine ⟨11768123837174099763993133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15690831782898799685324177 11768123837174099763993133)
          ·
            refine ⟨4413046438940287411497425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11768123837174099763993133 4413046438940287411497425)
            ·
              refine ⟨3309784829205215558623069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4413046438940287411497425 3309784829205215558623069)
              ·
                refine ⟨1241169310951955834483651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3309784829205215558623069 1241169310951955834483651)
                ·
                  refine ⟨1861753966427933751725477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241169310951955834483651 1861753966427933751725477)
                  ·
                    refine ⟨349078868705237578448527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1861753966427933751725477 349078868705237578448527)
                    ·
                      rfl

theorem cell23_2039486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2039486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039486 prefixEnd_2039486 := by exact prefixLift 2039486
  have htrace : WordTrace (prefixWord ++ tailWord_2039486) baseStart_2039486 baseEnd_2039486 := by
    simpa [prefixWord, tailWord_2039486, baseEnd_2039486] using wordTrace_append hprefix tailTrace_2039486
  have hstable : (prefixWord ++ tailWord_2039486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039486).length < 2 ^ (prefixWord ++ tailWord_2039486).sum := by decide
  have hdescent : baseEnd_2039486 < baseStart_2039486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039516 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 6]
def baseStart_2039516 : Nat := 118140960795 + 2039516 * 2 ^ 59
def prefixEnd_2039516 : Nat := 4983230072969 + 3 ^ 40 * 2039516 * 2
def baseEnd_2039516 : Nat := 116361334503927513107827

theorem tailTrace_2039516 : CollatzResearch.WordTrace tailWord_2039516 prefixEnd_2039516 116361334503927513107827 := by
  unfold tailWord_2039516
  simp only [CollatzResearch.WordTrace]
  refine ⟨37193629839594664223305201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49591506452792885631073601 37193629839594664223305201)
  ·
    refine ⟨27895222379695998167478901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37193629839594664223305201 27895222379695998167478901)
    ·
      refine ⟨2615177098096499828201147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27895222379695998167478901 2615177098096499828201147)
      ·
        refine ⟨3922765647144749742301721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615177098096499828201147 3922765647144749742301721)
        ·
          refine ⟨2942074235358562306726291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3922765647144749742301721 2942074235358562306726291)
          ·
            refine ⟨4413111353037843460089437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942074235358562306726291 4413111353037843460089437)
            ·
              refine ⟨1654916757389191297533539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4413111353037843460089437 1654916757389191297533539)
              ·
                refine ⟨2482375136083786946300309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1654916757389191297533539 2482375136083786946300309)
                ·
                  refine ⟨116361334503927513107827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2482375136083786946300309 116361334503927513107827)
                  ·
                    rfl

theorem cell23_2039516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 6].length) (baseStart_2039516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039516 prefixEnd_2039516 := by exact prefixLift 2039516
  have htrace : WordTrace (prefixWord ++ tailWord_2039516) baseStart_2039516 baseEnd_2039516 := by
    simpa [prefixWord, tailWord_2039516, baseEnd_2039516] using wordTrace_append hprefix tailTrace_2039516
  have hstable : (prefixWord ++ tailWord_2039516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039516).length < 2 ^ (prefixWord ++ tailWord_2039516).sum := by decide
  have hdescent : baseEnd_2039516 < baseStart_2039516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039532 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_2039532 : Nat := 118140960795 + 2039532 * 2 ^ 59
def prefixEnd_2039532 : Nat := 4983230072969 + 3 ^ 40 * 2039532 * 2
def baseEnd_2039532 : Nat := 1047260226225819555370369

theorem tailTrace_2039532 : CollatzResearch.WordTrace tailWord_2039532 prefixEnd_2039532 1047260226225819555370369 := by
  unfold tailWord_2039532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37193921623565681589596425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49591895498087575452795233 37193921623565681589596425)
  ·
    refine ⟨27895441217674261192197319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37193921623565681589596425 27895441217674261192197319)
    ·
      refine ⟨41843161826511391788295979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27895441217674261192197319 41843161826511391788295979)
      ·
        refine ⟨62764742739767087682443969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41843161826511391788295979 62764742739767087682443969)
        ·
          refine ⟨47073557054825315761832977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62764742739767087682443969 47073557054825315761832977)
          ·
            refine ⟨35305167791118986821374733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47073557054825315761832977 35305167791118986821374733)
            ·
              refine ⟨13239437921669620058015525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35305167791118986821374733 13239437921669620058015525)
              ·
                refine ⟨2482394610313053760877911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13239437921669620058015525 2482394610313053760877911)
                ·
                  refine ⟨3723591915469580641316867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482394610313053760877911 3723591915469580641316867)
                  ·
                    refine ⟨5585387873204370961975301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3723591915469580641316867 5585387873204370961975301)
                    ·
                      refine ⟨1047260226225819555370369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5585387873204370961975301 1047260226225819555370369)
                      ·
                        rfl

theorem cell23_2039532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_2039532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039532 prefixEnd_2039532 := by exact prefixLift 2039532
  have htrace : WordTrace (prefixWord ++ tailWord_2039532) baseStart_2039532 baseEnd_2039532 := by
    simpa [prefixWord, tailWord_2039532, baseEnd_2039532] using wordTrace_append hprefix tailTrace_2039532
  have hstable : (prefixWord ++ tailWord_2039532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039532).length < 2 ^ (prefixWord ++ tailWord_2039532).sum := by decide
  have hdescent : baseEnd_2039532 < baseStart_2039532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039535 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 5]
def baseStart_2039535 : Nat := 118140960795 + 2039535 * 2 ^ 59
def prefixEnd_2039535 : Nat := 4983230072969 + 3 ^ 40 * 2039535 * 2
def baseEnd_2039535 : Nat := 1047261766667783043632855

theorem tailTrace_2039535 : CollatzResearch.WordTrace tailWord_2039535 prefixEnd_2039535 1047261766667783043632855 := by
  unfold tailWord_2039535
  simp only [CollatzResearch.WordTrace]
  refine ⟨74387952666120494691552059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49591968444080329794368039 74387952666120494691552059)
  ·
    refine ⟨111581928999180742037328089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74387952666120494691552059 111581928999180742037328089)
    ·
      refine ⟨83686446749385556527996067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111581928999180742037328089 83686446749385556527996067)
      ·
        refine ⟨125529670124078334791994101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83686446749385556527996067 125529670124078334791994101)
        ·
          refine ⟨11768406574132343886749447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125529670124078334791994101 11768406574132343886749447)
          ·
            refine ⟨17652609861198515830124171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11768406574132343886749447 17652609861198515830124171)
            ·
              refine ⟨26478914791797773745186257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17652609861198515830124171 26478914791797773745186257)
              ·
                refine ⟨19859186093848330308889693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26478914791797773745186257 19859186093848330308889693)
                ·
                  refine ⟨7447194785193123865833635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19859186093848330308889693 7447194785193123865833635)
                  ·
                    refine ⟨11170792177789685798750453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7447194785193123865833635 11170792177789685798750453)
                    ·
                      refine ⟨1047261766667783043632855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11170792177789685798750453 1047261766667783043632855)
                      ·
                        rfl

theorem cell23_2039535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_2039535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039535 prefixEnd_2039535 := by exact prefixLift 2039535
  have htrace : WordTrace (prefixWord ++ tailWord_2039535) baseStart_2039535 baseEnd_2039535 := by
    simpa [prefixWord, tailWord_2039535, baseEnd_2039535] using wordTrace_append hprefix tailTrace_2039535
  have hstable : (prefixWord ++ tailWord_2039535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039535).length < 2 ^ (prefixWord ++ tailWord_2039535).sum := by decide
  have hdescent : baseEnd_2039535 < baseStart_2039535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039566 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_2039566 : Nat := 118140960795 + 2039566 * 2 ^ 59
def prefixEnd_2039566 : Nat := 4983230072969 + 3 ^ 40 * 2039566 * 2
def baseEnd_2039566 : Nat := 1047277684568072422345213

theorem tailTrace_2039566 : CollatzResearch.WordTrace tailWord_2039566 prefixEnd_2039566 1047277684568072422345213 := by
  unfold tailWord_2039566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9298635416126023373241319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49592722219338791323953701 9298635416126023373241319)
  ·
    refine ⟨13947953124189035059861979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9298635416126023373241319 13947953124189035059861979)
    ·
      refine ⟨20921929686283552589792969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13947953124189035059861979 20921929686283552589792969)
      ·
        refine ⟨15691447264712664442344727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20921929686283552589792969 15691447264712664442344727)
        ·
          refine ⟨23537170897068996663517091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15691447264712664442344727 23537170897068996663517091)
          ·
            refine ⟨35305756345603494995275637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23537170897068996663517091 35305756345603494995275637)
            ·
              refine ⟨3309914657400327655807091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35305756345603494995275637 3309914657400327655807091)
              ·
                refine ⟨4964871986100491483710637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309914657400327655807091 4964871986100491483710637)
                ·
                  refine ⟨1861826994787684306391489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4964871986100491483710637 1861826994787684306391489)
                  ·
                    refine ⟨1396370246090763229793617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861826994787684306391489 1396370246090763229793617)
                    ·
                      refine ⟨1047277684568072422345213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396370246090763229793617 1047277684568072422345213)
                      ·
                        rfl

theorem cell23_2039566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_2039566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039566 prefixEnd_2039566 := by exact prefixLift 2039566
  have htrace : WordTrace (prefixWord ++ tailWord_2039566) baseStart_2039566 baseEnd_2039566 := by
    simpa [prefixWord, tailWord_2039566, baseEnd_2039566] using wordTrace_append hprefix tailTrace_2039566
  have hstable : (prefixWord ++ tailWord_2039566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039566).length < 2 ^ (prefixWord ++ tailWord_2039566).sum := by decide
  have hdescent : baseEnd_2039566 < baseStart_2039566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039642 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_2039642 : Nat := 118140960795 + 2039642 * 2 ^ 59
def prefixEnd_2039642 : Nat := 4983230072969 + 3 ^ 40 * 2039642 * 2
def baseEnd_2039642 : Nat := 1047316709097814124994863

theorem tailTrace_2039642 : CollatzResearch.WordTrace tailWord_2039642 prefixEnd_2039642 1047316709097814124994863 := by
  unfold tailWord_2039642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18597963819183212991424295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49594570184488567977131453 18597963819183212991424295)
  ·
    refine ⟨27896945728774819487136443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18597963819183212991424295 27896945728774819487136443)
    ·
      refine ⟨41845418593162229230704665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27896945728774819487136443 41845418593162229230704665)
      ·
        refine ⟨31384063944871671923028499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41845418593162229230704665 31384063944871671923028499)
        ·
          refine ⟨47076095917307507884542749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31384063944871671923028499 47076095917307507884542749)
          ·
            refine ⟨17653535968990315456703531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47076095917307507884542749 17653535968990315456703531)
            ·
              refine ⟨26480303953485473185055297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17653535968990315456703531 26480303953485473185055297)
              ·
                refine ⟨19860227965114104888791473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26480303953485473185055297 19860227965114104888791473)
                ·
                  refine ⟨14895170973835578666593605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19860227965114104888791473 14895170973835578666593605)
                  ·
                    refine ⟨2792844557594170999986301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14895170973835578666593605 2792844557594170999986301)
                    ·
                      refine ⟨1047316709097814124994863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2792844557594170999986301 1047316709097814124994863)
                      ·
                        rfl

theorem cell23_2039642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_2039642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039642 prefixEnd_2039642 := by exact prefixLift 2039642
  have htrace : WordTrace (prefixWord ++ tailWord_2039642) baseStart_2039642 baseEnd_2039642 := by
    simpa [prefixWord, tailWord_2039642, baseEnd_2039642] using wordTrace_append hprefix tailTrace_2039642
  have hstable : (prefixWord ++ tailWord_2039642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039642).length < 2 ^ (prefixWord ++ tailWord_2039642).sum := by decide
  have hdescent : baseEnd_2039642 < baseStart_2039642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039656 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2039656 : Nat := 118140960795 + 2039656 * 2 ^ 59
def prefixEnd_2039656 : Nat := 4983230072969 + 3 ^ 40 * 2039656 * 2
def baseEnd_2039656 : Nat := 1047323897826977070219799

theorem tailTrace_2039656 : CollatzResearch.WordTrace tailWord_2039656 prefixEnd_2039656 1047323897826977070219799 := by
  unfold tailWord_2039656
  simp only [CollatzResearch.WordTrace]
  refine ⟨37196182949341066178353411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49594910599121421571137881 37196182949341066178353411)
  ·
    refine ⟨55794274424011599267530117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37196182949341066178353411 55794274424011599267530117)
    ·
      refine ⟨10461426454502174862661897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55794274424011599267530117 10461426454502174862661897)
      ·
        refine ⟨7846069840876631146996423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10461426454502174862661897 7846069840876631146996423)
        ·
          refine ⟨11769104761314946720494635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846069840876631146996423 11769104761314946720494635)
          ·
            refine ⟨17653657141972420080741953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769104761314946720494635 17653657141972420080741953)
            ·
              refine ⟨13240242856479315060556465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17653657141972420080741953 13240242856479315060556465)
              ·
                refine ⟨9930182142359486295417349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13240242856479315060556465 9930182142359486295417349)
                ·
                  refine ⟨1861909151692403680390753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9930182142359486295417349 1861909151692403680390753)
                  ·
                    refine ⟨1396431863769302760293065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1861909151692403680390753 1396431863769302760293065)
                    ·
                      refine ⟨1047323897826977070219799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396431863769302760293065 1047323897826977070219799)
                      ·
                        rfl

theorem cell23_2039656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2039656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039656 prefixEnd_2039656 := by exact prefixLift 2039656
  have htrace : WordTrace (prefixWord ++ tailWord_2039656) baseStart_2039656 baseEnd_2039656 := by
    simpa [prefixWord, tailWord_2039656, baseEnd_2039656] using wordTrace_append hprefix tailTrace_2039656
  have hstable : (prefixWord ++ tailWord_2039656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039656).length < 2 ^ (prefixWord ++ tailWord_2039656).sum := by decide
  have hdescent : baseEnd_2039656 < baseStart_2039656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039690 : List Nat := [3, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_2039690 : Nat := 118140960795 + 2039690 * 2 ^ 59
def prefixEnd_2039690 : Nat := 4983230072969 + 3 ^ 40 * 2039690 * 2
def baseEnd_2039690 : Nat := 1047341356169229937194643

theorem tailTrace_2039690 : CollatzResearch.WordTrace tailWord_2039690 prefixEnd_2039690 1047341356169229937194643 := by
  unfold tailWord_2039690
  simp only [CollatzResearch.WordTrace]
  refine ⟨18598401495139739040861131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49595737320372637442296349 18598401495139739040861131)
  ·
    refine ⟨27897602242709608561291697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18598401495139739040861131 27897602242709608561291697)
    ·
      refine ⟨20923201682032206420968773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27897602242709608561291697 20923201682032206420968773)
      ·
        refine ⟨3923100315381038703931645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20923201682032206420968773 3923100315381038703931645)
        ·
          refine ⟨1471162618267889513974367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3923100315381038703931645 1471162618267889513974367)
          ·
            refine ⟨2206743927401834270961551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471162618267889513974367 2206743927401834270961551)
            ·
              refine ⟨3310115891102751406442327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206743927401834270961551 3310115891102751406442327)
              ·
                refine ⟨4965173836654127109663491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310115891102751406442327 4965173836654127109663491)
                ·
                  refine ⟨7447760754981190664495237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965173836654127109663491 7447760754981190664495237)
                  ·
                    refine ⟨1396455141558973249592857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7447760754981190664495237 1396455141558973249592857)
                    ·
                      refine ⟨1047341356169229937194643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396455141558973249592857 1047341356169229937194643)
                      ·
                        rfl

theorem cell23_2039690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_2039690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039690 prefixEnd_2039690 := by exact prefixLift 2039690
  have htrace : WordTrace (prefixWord ++ tailWord_2039690) baseStart_2039690 baseEnd_2039690 := by
    simpa [prefixWord, tailWord_2039690, baseEnd_2039690] using wordTrace_append hprefix tailTrace_2039690
  have hstable : (prefixWord ++ tailWord_2039690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039690).length < 2 ^ (prefixWord ++ tailWord_2039690).sum := by decide
  have hdescent : baseEnd_2039690 < baseStart_2039690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039713 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 5]
def baseStart_2039713 : Nat := 118140960795 + 2039713 * 2 ^ 59
def prefixEnd_2039713 : Nat := 4983230072969 + 3 ^ 40 * 2039713 * 2
def baseEnd_2039713 : Nat := 116372574024920371911893

theorem tailTrace_2039713 : CollatzResearch.WordTrace tailWord_2039713 prefixEnd_2039713 116372574024920371911893 := by
  unfold tailWord_2039713
  simp only [CollatzResearch.WordTrace]
  refine ⟨74394444859475631091531793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49596296572983754061021195 74394444859475631091531793)
  ·
    refine ⟨55795833644606723318648845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74394444859475631091531793 55795833644606723318648845)
    ·
      refine ⟨20923437616727521244493317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55795833644606723318648845 20923437616727521244493317)
      ·
        refine ⟨3923144553136410233342497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20923437616727521244493317 3923144553136410233342497)
        ·
          refine ⟨2942358414852307675006873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923144553136410233342497 2942358414852307675006873)
          ·
            refine ⟨2206768811139230756255155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942358414852307675006873 2206768811139230756255155)
            ·
              refine ⟨3310153216708846134382733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206768811139230756255155 3310153216708846134382733)
              ·
                refine ⟨1241307456265817300393525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3310153216708846134382733 1241307456265817300393525)
                ·
                  refine ⟨116372574024920371911893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1241307456265817300393525 116372574024920371911893)
                  ·
                    rfl

theorem cell23_2039713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 5].length) (baseStart_2039713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039713 prefixEnd_2039713 := by exact prefixLift 2039713
  have htrace : WordTrace (prefixWord ++ tailWord_2039713) baseStart_2039713 baseEnd_2039713 := by
    simpa [prefixWord, tailWord_2039713, baseEnd_2039713] using wordTrace_append hprefix tailTrace_2039713
  have hstable : (prefixWord ++ tailWord_2039713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039713).length < 2 ^ (prefixWord ++ tailWord_2039713).sum := by decide
  have hdescent : baseEnd_2039713 < baseStart_2039713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039729 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2039729 : Nat := 118140960795 + 2039729 * 2 ^ 59
def prefixEnd_2039729 : Nat := 4983230072969 + 3 ^ 40 * 2039729 * 2
def baseEnd_2039729 : Nat := 1047361381914755284606963

theorem tailTrace_2039729 : CollatzResearch.WordTrace tailWord_2039729 prefixEnd_2039729 1047361381914755284606963 := by
  unfold tailWord_2039729
  simp only [CollatzResearch.WordTrace]
  refine ⟨74395028427417665824114241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49596685618278443882742827 74395028427417665824114241)
  ·
    refine ⟨55796271320563249368085681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74395028427417665824114241 55796271320563249368085681)
    ·
      refine ⟨41847203490422437026064261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55796271320563249368085681 41847203490422437026064261)
      ·
        refine ⟨7846350654454206942387049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41847203490422437026064261 7846350654454206942387049)
        ·
          refine ⟨5884762990840655206790287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846350654454206942387049 5884762990840655206790287)
          ·
            refine ⟨8827144486260982810185431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884762990840655206790287 8827144486260982810185431)
            ·
              refine ⟨13240716729391474215278147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827144486260982810185431 13240716729391474215278147)
              ·
                refine ⟨19861075094087211322917221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240716729391474215278147 19861075094087211322917221)
                ·
                  refine ⟨3723951580141352123046979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19861075094087211322917221 3723951580141352123046979)
                  ·
                    refine ⟨5585927370212028184570469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3723951580141352123046979 5585927370212028184570469)
                    ·
                      refine ⟨1047361381914755284606963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5585927370212028184570469 1047361381914755284606963)
                      ·
                        rfl

theorem cell23_2039729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2039729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039729 prefixEnd_2039729 := by exact prefixLift 2039729
  have htrace : WordTrace (prefixWord ++ tailWord_2039729) baseStart_2039729 baseEnd_2039729 := by
    simpa [prefixWord, tailWord_2039729, baseEnd_2039729] using wordTrace_append hprefix tailTrace_2039729
  have hstable : (prefixWord ++ tailWord_2039729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039729).length < 2 ^ (prefixWord ++ tailWord_2039729).sum := by decide
  have hdescent : baseEnd_2039729 < baseStart_2039729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039790 : List Nat := [4, 1, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_2039790 : Nat := 118140960795 + 2039790 * 2 ^ 59
def prefixEnd_2039790 : Nat := 4983230072969 + 3 ^ 40 * 2039790 * 2
def baseEnd_2039790 : Nat := 349130901411559848648061

theorem tailTrace_2039790 : CollatzResearch.WordTrace tailWord_2039790 prefixEnd_2039790 349130901411559848648061 := by
  unfold tailWord_2039790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9299656660024584155260603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49598168853464448828056549 9299656660024584155260603)
  ·
    refine ⟨13949484990036876232890905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9299656660024584155260603 13949484990036876232890905)
    ·
      refine ⟨10462113742527657174668179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13949484990036876232890905 10462113742527657174668179)
      ·
        refine ⟨15693170613791485762002269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10462113742527657174668179 15693170613791485762002269)
        ·
          refine ⟨5884938980171807160750851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15693170613791485762002269 5884938980171807160750851)
          ·
            refine ⟨8827408470257710741126277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5884938980171807160750851 8827408470257710741126277)
            ·
              refine ⟨1655139088173320763961177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8827408470257710741126277 1655139088173320763961177)
              ·
                refine ⟨1241354316129990572970883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1655139088173320763961177 1241354316129990572970883)
                ·
                  refine ⟨1862031474194985859456325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241354316129990572970883 1862031474194985859456325)
                  ·
                    refine ⟨349130901411559848648061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1862031474194985859456325 349130901411559848648061)
                    ·
                      rfl

theorem cell23_2039790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_2039790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039790 prefixEnd_2039790 := by exact prefixLift 2039790
  have htrace : WordTrace (prefixWord ++ tailWord_2039790) baseStart_2039790 baseEnd_2039790 := by
    simpa [prefixWord, tailWord_2039790, baseEnd_2039790] using wordTrace_append hprefix tailTrace_2039790
  have hstable : (prefixWord ++ tailWord_2039790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039790).length < 2 ^ (prefixWord ++ tailWord_2039790).sum := by decide
  have hdescent : baseEnd_2039790 < baseStart_2039790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039814 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_2039814 : Nat := 118140960795 + 2039814 * 2 ^ 59
def prefixEnd_2039814 : Nat := 4983230072969 + 3 ^ 40 * 2039814 * 2
def baseEnd_2039814 : Nat := 1047405027770387452044073

theorem tailTrace_2039814 : CollatzResearch.WordTrace tailWord_2039814 prefixEnd_2039814 1047405027770387452044073 := by
  unfold tailWord_2039814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2324941519753428916904953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 49598752421406483560638997 2324941519753428916904953)
  ·
    refine ⟨1743706139815071687678715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2324941519753428916904953 1743706139815071687678715)
    ·
      refine ⟨2615559209722607531518073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743706139815071687678715 2615559209722607531518073)
      ·
        refine ⟨1961669407291955648638555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2615559209722607531518073 1961669407291955648638555)
        ·
          refine ⟨2942504110937933472957833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1961669407291955648638555 2942504110937933472957833)
          ·
            refine ⟨2206878083203450104718375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2942504110937933472957833 2206878083203450104718375)
            ·
              refine ⟨3310317124805175157077563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2206878083203450104718375 3310317124805175157077563)
              ·
                refine ⟨4965475687207762735616345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310317124805175157077563 4965475687207762735616345)
                ·
                  refine ⟨3724106765405822051712259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965475687207762735616345 3724106765405822051712259)
                  ·
                    refine ⟨5586160148108733077568389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3724106765405822051712259 5586160148108733077568389)
                    ·
                      refine ⟨1047405027770387452044073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5586160148108733077568389 1047405027770387452044073)
                      ·
                        rfl

theorem cell23_2039814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_2039814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039814 prefixEnd_2039814 := by exact prefixLift 2039814
  have htrace : WordTrace (prefixWord ++ tailWord_2039814) baseStart_2039814 baseEnd_2039814 := by
    simpa [prefixWord, tailWord_2039814, baseEnd_2039814] using wordTrace_append hprefix tailTrace_2039814
  have hstable : (prefixWord ++ tailWord_2039814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039814).length < 2 ^ (prefixWord ++ tailWord_2039814).sum := by decide
  have hdescent : baseEnd_2039814 < baseStart_2039814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039819 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 4]
def baseStart_2039819 : Nat := 118140960795 + 2039819 * 2 ^ 59
def prefixEnd_2039819 : Nat := 4983230072969 + 3 ^ 40 * 2039819 * 2
def baseEnd_2039819 : Nat := 1047407595173659932481549

theorem tailTrace_2039819 : CollatzResearch.WordTrace tailWord_2039819 prefixEnd_2039819 1047407595173659932481549 := by
  unfold tailWord_2039819
  simp only [CollatzResearch.WordTrace]
  refine ⟨74398310997091611194890511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49598873998061074129927007 74398310997091611194890511)
  ·
    refine ⟨111597466495637416792335767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74398310997091611194890511 111597466495637416792335767)
    ·
      refine ⟨167396199743456125188503651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111597466495637416792335767 167396199743456125188503651)
      ·
        refine ⟨251094299615184187782755477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167396199743456125188503651 251094299615184187782755477)
        ·
          refine ⟨11770045294461758802316663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251094299615184187782755477 11770045294461758802316663)
          ·
            refine ⟨17655067941692638203474995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11770045294461758802316663 17655067941692638203474995)
            ·
              refine ⟨26482601912538957305212493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17655067941692638203474995 26482601912538957305212493)
              ·
                refine ⟨9930975717202108989454685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26482601912538957305212493 9930975717202108989454685)
                ·
                  refine ⟨3724115893950790871045507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9930975717202108989454685 3724115893950790871045507)
                  ·
                    refine ⟨5586173840926186306568261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3724115893950790871045507 5586173840926186306568261)
                    ·
                      refine ⟨1047407595173659932481549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5586173840926186306568261 1047407595173659932481549)
                      ·
                        rfl

theorem cell23_2039819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 1, 4].length) (baseStart_2039819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039819 prefixEnd_2039819 := by exact prefixLift 2039819
  have htrace : WordTrace (prefixWord ++ tailWord_2039819) baseStart_2039819 baseEnd_2039819 := by
    simpa [prefixWord, tailWord_2039819, baseEnd_2039819] using wordTrace_append hprefix tailTrace_2039819
  have hstable : (prefixWord ++ tailWord_2039819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039819).length < 2 ^ (prefixWord ++ tailWord_2039819).sum := by decide
  have hdescent : baseEnd_2039819 < baseStart_2039819 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039839 : List Nat := [1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 5]
def baseStart_2039839 : Nat := 118140960795 + 2039839 * 2 ^ 59
def prefixEnd_2039839 : Nat := 4983230072969 + 3 ^ 40 * 2039839 * 2
def baseEnd_2039839 : Nat := 1047417864786749854231457

theorem tailTrace_2039839 : CollatzResearch.WordTrace tailWord_2039839 prefixEnd_2039839 1047417864786749854231457 := by
  unfold tailWord_2039839
  simp only [CollatzResearch.WordTrace]
  refine ⟨74399040457019154610618571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49599360304679436407079047 74399040457019154610618571)
  ·
    refine ⟨111598560685528731915927857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74399040457019154610618571 111598560685528731915927857)
    ·
      refine ⟨83698920514146548936945893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111598560685528731915927857 83698920514146548936945893)
      ·
        refine ⟨15693547596402477925677355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83698920514146548936945893 15693547596402477925677355)
        ·
          refine ⟨23540321394603716888516033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15693547596402477925677355 23540321394603716888516033)
          ·
            refine ⟨17655241045952787666387025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23540321394603716888516033 17655241045952787666387025)
            ·
              refine ⟨13241430784464590749790269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17655241045952787666387025 13241430784464590749790269)
              ·
                refine ⟨4965536544174221531171351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13241430784464590749790269 4965536544174221531171351)
                ·
                  refine ⟨7448304816261332296757027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965536544174221531171351 7448304816261332296757027)
                  ·
                    refine ⟨11172457224391998445135541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7448304816261332296757027 11172457224391998445135541)
                    ·
                      refine ⟨1047417864786749854231457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11172457224391998445135541 1047417864786749854231457)
                      ·
                        rfl

theorem cell23_2039839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_2039839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039839 prefixEnd_2039839 := by exact prefixLift 2039839
  have htrace : WordTrace (prefixWord ++ tailWord_2039839) baseStart_2039839 baseEnd_2039839 := by
    simpa [prefixWord, tailWord_2039839, baseEnd_2039839] using wordTrace_append hprefix tailTrace_2039839
  have hstable : (prefixWord ++ tailWord_2039839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039839).length < 2 ^ (prefixWord ++ tailWord_2039839).sum := by decide
  have hdescent : baseEnd_2039839 < baseStart_2039839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039870 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2039870 : Nat := 118140960795 + 2039870 * 2 ^ 59
def prefixEnd_2039870 : Nat := 4983230072969 + 3 ^ 40 * 2039870 * 2
def baseEnd_2039870 : Nat := 1047433782687039232943815

theorem tailTrace_2039870 : CollatzResearch.WordTrace tailWord_2039870 prefixEnd_2039870 1047433782687039232943815 := by
  unfold tailWord_2039870
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300021389988355863124633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49600114079937897936664709 9300021389988355863124633)
  ·
    refine ⟨6975016042491266897343475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9300021389988355863124633 6975016042491266897343475)
    ·
      refine ⟨10462524063736900346015213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6975016042491266897343475 10462524063736900346015213)
      ·
        refine ⟨3923446523901337629755705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10462524063736900346015213 3923446523901337629755705)
        ·
          refine ⟨2942584892926003222316779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3923446523901337629755705 2942584892926003222316779)
          ·
            refine ⟨4413877339389004833475169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2942584892926003222316779 4413877339389004833475169)
            ·
              refine ⟨3310408004541753625106377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4413877339389004833475169 3310408004541753625106377)
              ·
                refine ⟨2482806003406315218829783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310408004541753625106377 2482806003406315218829783)
                ·
                  refine ⟨3724209005109472828244675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482806003406315218829783 3724209005109472828244675)
                  ·
                    refine ⟨5586313507664209242367013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3724209005109472828244675 5586313507664209242367013)
                    ·
                      refine ⟨1047433782687039232943815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5586313507664209242367013 1047433782687039232943815)
                      ·
                        rfl

theorem cell23_2039870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2039870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039870 prefixEnd_2039870 := by exact prefixLift 2039870
  have htrace : WordTrace (prefixWord ++ tailWord_2039870) baseStart_2039870 baseEnd_2039870 := by
    simpa [prefixWord, tailWord_2039870, baseEnd_2039870] using wordTrace_append hprefix tailTrace_2039870
  have hstable : (prefixWord ++ tailWord_2039870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039870).length < 2 ^ (prefixWord ++ tailWord_2039870).sum := by decide
  have hdescent : baseEnd_2039870 < baseStart_2039870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039873 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2039873 : Nat := 118140960795 + 2039873 * 2 ^ 59
def prefixEnd_2039873 : Nat := 4983230072969 + 3 ^ 40 * 2039873 * 2
def baseEnd_2039873 : Nat := 1047435323129002721206301

theorem tailTrace_2039873 : CollatzResearch.WordTrace tailWord_2039873 prefixEnd_2039873 1047435323129002721206301 := by
  unfold tailWord_2039873
  simp only [CollatzResearch.WordTrace]
  refine ⟨74400280538895978417356273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49600187025930652278237515 74400280538895978417356273)
  ·
    refine ⟨55800210404171983813017205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74400280538895978417356273 55800210404171983813017205)
    ·
      refine ⟨5231269725391123482470363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55800210404171983813017205 5231269725391123482470363)
      ·
        refine ⟨7846904588086685223705545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5231269725391123482470363 7846904588086685223705545)
        ·
          refine ⟨5885178441065013917779159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846904588086685223705545 5885178441065013917779159)
          ·
            refine ⟨8827767661597520876668739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885178441065013917779159 8827767661597520876668739)
            ·
              refine ⟨13241651492396281315003109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827767661597520876668739 13241651492396281315003109)
              ·
                refine ⟨2482809654824302746563083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13241651492396281315003109 2482809654824302746563083)
                ·
                  refine ⟨3724214482236454119844625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482809654824302746563083 3724214482236454119844625)
                  ·
                    refine ⟨2793160861677340589883469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3724214482236454119844625 2793160861677340589883469)
                    ·
                      refine ⟨1047435323129002721206301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2793160861677340589883469 1047435323129002721206301)
                      ·
                        rfl

theorem cell23_2039873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2039873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039873 prefixEnd_2039873 := by exact prefixLift 2039873
  have htrace : WordTrace (prefixWord ++ tailWord_2039873) baseStart_2039873 baseEnd_2039873 := by
    simpa [prefixWord, tailWord_2039873, baseEnd_2039873] using wordTrace_append hprefix tailTrace_2039873
  have hstable : (prefixWord ++ tailWord_2039873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039873).length < 2 ^ (prefixWord ++ tailWord_2039873).sum := by decide
  have hdescent : baseEnd_2039873 < baseStart_2039873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039920 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 2, 1, 3]
def baseStart_2039920 : Nat := 118140960795 + 2039920 * 2 ^ 59
def prefixEnd_2039920 : Nat := 4983230072969 + 3 ^ 40 * 2039920 * 2
def baseEnd_2039920 : Nat := 1047459456719764037318585

theorem tailTrace_2039920 : CollatzResearch.WordTrace tailWord_2039920 prefixEnd_2039920 1047459456719764037318585 := by
  unfold tailWord_2039920
  simp only [CollatzResearch.WordTrace]
  refine ⟨37200997384862852722158607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49601329846483803629544809 37200997384862852722158607)
  ·
    refine ⟨55801496077294279083237911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37200997384862852722158607 55801496077294279083237911)
    ·
      refine ⟨83702244115941418624856867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55801496077294279083237911 83702244115941418624856867)
      ·
        refine ⟨125553366173912127937285301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83702244115941418624856867 125553366173912127937285301)
        ·
          refine ⟨11770628078804261994120497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125553366173912127937285301 11770628078804261994120497)
          ·
            refine ⟨8827971059103196495590373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11770628078804261994120497 8827971059103196495590373)
            ·
              refine ⟨1655244573581849342923195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8827971059103196495590373 1655244573581849342923195)
              ·
                refine ⟨2482866860372774014384793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655244573581849342923195 2482866860372774014384793)
                ·
                  refine ⟨1862150145279580510788595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2482866860372774014384793 1862150145279580510788595)
                  ·
                    refine ⟨2793225217919370766182893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1862150145279580510788595 2793225217919370766182893)
                    ·
                      refine ⟨1047459456719764037318585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2793225217919370766182893 1047459456719764037318585)
                      ·
                        rfl

theorem cell23_2039920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 1, 3].length) (baseStart_2039920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039920 prefixEnd_2039920 := by exact prefixLift 2039920
  have htrace : WordTrace (prefixWord ++ tailWord_2039920) baseStart_2039920 baseEnd_2039920 := by
    simpa [prefixWord, tailWord_2039920, baseEnd_2039920] using wordTrace_append hprefix tailTrace_2039920
  have hstable : (prefixWord ++ tailWord_2039920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039920).length < 2 ^ (prefixWord ++ tailWord_2039920).sum := by decide
  have hdescent : baseEnd_2039920 < baseStart_2039920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039943 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_2039943 : Nat := 118140960795 + 2039943 * 2 ^ 59
def prefixEnd_2039943 : Nat := 4983230072969 + 3 ^ 40 * 2039943 * 2
def baseEnd_2039943 : Nat := 1047471266774817447330979

theorem tailTrace_2039943 : CollatzResearch.WordTrace tailWord_2039943 prefixEnd_2039943 1047471266774817447330979 := by
  unfold tailWord_2039943
  simp only [CollatzResearch.WordTrace]
  refine ⟨74402833648642380372404483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49601889099094920248269655 74402833648642380372404483)
  ·
    refine ⟨111604250472963570558606725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74402833648642380372404483 111604250472963570558606725)
    ·
      refine ⟨20925796963680669479738761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111604250472963570558606725 20925796963680669479738761)
      ·
        refine ⟨15694347722760502109804071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20925796963680669479738761 15694347722760502109804071)
        ·
          refine ⟨23541521584140753164706107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694347722760502109804071 23541521584140753164706107)
          ·
            refine ⟨35312282376211129747059161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23541521584140753164706107 35312282376211129747059161)
            ·
              refine ⟨26484211782158347310294371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35312282376211129747059161 26484211782158347310294371)
              ·
                refine ⟨39726317673237520965441557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26484211782158347310294371 39726317673237520965441557)
                ·
                  refine ⟨1862171140933008795255073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39726317673237520965441557 1862171140933008795255073)
                  ·
                    refine ⟨1396628355699756596441305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862171140933008795255073 1396628355699756596441305)
                    ·
                      refine ⟨1047471266774817447330979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396628355699756596441305 1047471266774817447330979)
                      ·
                        rfl

theorem cell23_2039943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_2039943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039943 prefixEnd_2039943 := by exact prefixLift 2039943
  have htrace : WordTrace (prefixWord ++ tailWord_2039943) baseStart_2039943 baseEnd_2039943 := by
    simpa [prefixWord, tailWord_2039943, baseEnd_2039943] using wordTrace_append hprefix tailTrace_2039943
  have hstable : (prefixWord ++ tailWord_2039943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039943).length < 2 ^ (prefixWord ++ tailWord_2039943).sum := by decide
  have hdescent : baseEnd_2039943 < baseStart_2039943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2039946 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_2039946 : Nat := 118140960795 + 2039946 * 2 ^ 59
def prefixEnd_2039946 : Nat := 4983230072969 + 3 ^ 40 * 2039946 * 2
def baseEnd_2039946 : Nat := 1047472807216780935593465

theorem tailTrace_2039946 : CollatzResearch.WordTrace tailWord_2039946 prefixEnd_2039946 1047472807216780935593465 := by
  unfold tailWord_2039946
  simp only [CollatzResearch.WordTrace]
  refine ⟨18600735766907877971190923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49601962045087674589842461 18600735766907877971190923)
  ·
    refine ⟨27901103650361816956786385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18600735766907877971190923 27901103650361816956786385)
    ·
      refine ⟨20925827737771362717589789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27901103650361816956786385 20925827737771362717589789)
      ·
        refine ⟨7847185401664261019096171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20925827737771362717589789 7847185401664261019096171)
        ·
          refine ⟨11770778102496391528644257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847185401664261019096171 11770778102496391528644257)
          ·
            refine ⟨8828083576872293646483193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11770778102496391528644257 8828083576872293646483193)
            ·
              refine ⟨6621062682654220234862395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8828083576872293646483193 6621062682654220234862395)
              ·
                refine ⟨9931594023981330352293593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621062682654220234862395 9931594023981330352293593)
                ·
                  refine ⟨7448695517985997764220195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9931594023981330352293593 7448695517985997764220195)
                  ·
                    refine ⟨11173043276978996646330293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7448695517985997764220195 11173043276978996646330293)
                    ·
                      refine ⟨1047472807216780935593465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11173043276978996646330293 1047472807216780935593465)
                      ·
                        rfl

theorem cell23_2039946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_2039946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2039946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2039946 prefixEnd_2039946 := by exact prefixLift 2039946
  have htrace : WordTrace (prefixWord ++ tailWord_2039946) baseStart_2039946 baseEnd_2039946 := by
    simpa [prefixWord, tailWord_2039946, baseEnd_2039946] using wordTrace_append hprefix tailTrace_2039946
  have hstable : (prefixWord ++ tailWord_2039946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2039946).length < 2 ^ (prefixWord ++ tailWord_2039946).sum := by decide
  have hdescent : baseEnd_2039946 < baseStart_2039946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2039946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040033 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 2, 4, 2]
def baseStart_2040033 : Nat := 118140960795 + 2040033 * 2 ^ 59
def prefixEnd_2040033 : Nat := 4983230072969 + 3 ^ 40 * 2040033 * 2
def baseEnd_2040033 : Nat := 1047517480033722095205565

theorem tailTrace_2040033 : CollatzResearch.WordTrace tailWord_2040033 prefixEnd_2040033 1047517480033722095205565 := by
  unfold tailWord_2040033
  simp only [CollatzResearch.WordTrace]
  refine ⟨74406116218316325743180753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49604077478877550495453835 74406116218316325743180753)
  ·
    refine ⟨55804587163737244307385565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74406116218316325743180753 55804587163737244307385565)
    ·
      refine ⟨20926720186401466615269587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55804587163737244307385565 20926720186401466615269587)
      ·
        refine ⟨31390080279602199922904381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20926720186401466615269587 31390080279602199922904381)
        ·
          refine ⟨11771280104850824971089143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31390080279602199922904381 11771280104850824971089143)
          ·
            refine ⟨17656920157276237456633715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771280104850824971089143 17656920157276237456633715)
            ·
              refine ⟨26485380235914356184950573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656920157276237456633715 26485380235914356184950573)
              ·
                refine ⟨9932017588467883569356465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26485380235914356184950573 9932017588467883569356465)
                ·
                  refine ⟨7449013191350912677017349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932017588467883569356465 7449013191350912677017349)
                  ·
                    refine ⟨1396689973378296126940753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7449013191350912677017349 1396689973378296126940753)
                    ·
                      refine ⟨1047517480033722095205565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396689973378296126940753 1047517480033722095205565)
                      ·
                        rfl

theorem cell23_2040033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 4, 2].length) (baseStart_2040033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040033 prefixEnd_2040033 := by exact prefixLift 2040033
  have htrace : WordTrace (prefixWord ++ tailWord_2040033) baseStart_2040033 baseEnd_2040033 := by
    simpa [prefixWord, tailWord_2040033, baseEnd_2040033] using wordTrace_append hprefix tailTrace_2040033
  have hstable : (prefixWord ++ tailWord_2040033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040033).length < 2 ^ (prefixWord ++ tailWord_2040033).sum := by decide
  have hdescent : baseEnd_2040033 < baseStart_2040033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040046 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_2040046 : Nat := 118140960795 + 2040046 * 2 ^ 59
def prefixEnd_2040046 : Nat := 4983230072969 + 3 ^ 40 * 2040046 * 2
def baseEnd_2040046 : Nat := 1047524155282230544343005

theorem tailTrace_2040046 : CollatzResearch.WordTrace tailWord_2040046 prefixEnd_2040046 1047524155282230544343005 := by
  unfold tailWord_2040046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9300823795908653620425499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49604393578179485975602661 9300823795908653620425499)
  ·
    refine ⟨13951235693862980430638249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9300823795908653620425499 13951235693862980430638249)
    ·
      refine ⟨10463426770397235322978687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13951235693862980430638249 10463426770397235322978687)
      ·
        refine ⟨15695140155595852984468031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10463426770397235322978687 15695140155595852984468031)
        ·
          refine ⟨23542710233393779476702047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15695140155595852984468031 23542710233393779476702047)
          ·
            refine ⟨35314065350090669215053071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542710233393779476702047 35314065350090669215053071)
            ·
              refine ⟨52971098025136003822579607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35314065350090669215053071 52971098025136003822579607)
              ·
                refine ⟨79456647037704005733869411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52971098025136003822579607 79456647037704005733869411)
                ·
                  refine ⟨119184970556556008600804117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79456647037704005733869411 119184970556556008600804117)
                  ·
                    refine ⟨5586795494838562903162693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 119184970556556008600804117 5586795494838562903162693)
                    ·
                      refine ⟨1047524155282230544343005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5586795494838562903162693 1047524155282230544343005)
                      ·
                        rfl

theorem cell23_2040046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_2040046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040046 prefixEnd_2040046 := by exact prefixLift 2040046
  have htrace : WordTrace (prefixWord ++ tailWord_2040046) baseStart_2040046 baseEnd_2040046 := by
    simpa [prefixWord, tailWord_2040046, baseEnd_2040046] using wordTrace_append hprefix tailTrace_2040046
  have hstable : (prefixWord ++ tailWord_2040046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040046).length < 2 ^ (prefixWord ++ tailWord_2040046).sum := by decide
  have hdescent : baseEnd_2040046 < baseStart_2040046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040117 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_2040117 : Nat := 118140960795 + 2040117 * 2 ^ 59
def prefixEnd_2040117 : Nat := 4983230072969 + 3 ^ 40 * 2040117 * 2
def baseEnd_2040117 : Nat := 1047560612408699766555179

theorem tailTrace_2040117 : CollatzResearch.WordTrace tailWord_2040117 prefixEnd_2040117 1047560612408699766555179 := by
  unfold tailWord_2040117
  simp only [CollatzResearch.WordTrace]
  refine ⟨74409179950012008089238605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49606119966674672059492403 74409179950012008089238605)
  ·
    refine ⟨27903442481254503033464477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74409179950012008089238605 27903442481254503033464477)
    ·
      refine ⟨10463790930470438637549179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27903442481254503033464477 10463790930470438637549179)
      ·
        refine ⟨15695686395705657956323769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10463790930470438637549179 15695686395705657956323769)
        ·
          refine ⟨11771764796779243467242827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15695686395705657956323769 11771764796779243467242827)
          ·
            refine ⟨17657647195168865200864241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771764796779243467242827 17657647195168865200864241)
            ·
              refine ⟨13243235396376648900648181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17657647195168865200864241 13243235396376648900648181)
              ·
                refine ⟨1241553318410310834435767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13243235396376648900648181 1241553318410310834435767)
                ·
                  refine ⟨1862329977615466251653651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241553318410310834435767 1862329977615466251653651)
                  ·
                    refine ⟨2793494966423199377480477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1862329977615466251653651 2793494966423199377480477)
                    ·
                      refine ⟨1047560612408699766555179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2793494966423199377480477 1047560612408699766555179)
                      ·
                        rfl

theorem cell23_2040117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_2040117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040117 prefixEnd_2040117 := by exact prefixLift 2040117
  have htrace : WordTrace (prefixWord ++ tailWord_2040117) baseStart_2040117 baseEnd_2040117 := by
    simpa [prefixWord, tailWord_2040117, baseEnd_2040117] using wordTrace_append hprefix tailTrace_2040117
  have hstable : (prefixWord ++ tailWord_2040117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040117).length < 2 ^ (prefixWord ++ tailWord_2040117).sum := by decide
  have hdescent : baseEnd_2040117 < baseStart_2040117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040136 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_2040136 : Nat := 118140960795 + 2040136 * 2 ^ 59
def prefixEnd_2040136 : Nat := 4983230072969 + 3 ^ 40 * 2040136 * 2
def baseEnd_2040136 : Nat := 1047570368541135192217591

theorem tailTrace_2040136 : CollatzResearch.WordTrace tailWord_2040136 prefixEnd_2040136 1047570368541135192217591 := by
  unfold tailWord_2040136
  simp only [CollatzResearch.WordTrace]
  refine ⟨37204936468471587167090131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49606581957962116222786841 37204936468471587167090131)
  ·
    refine ⟨55807404702707380750635197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37204936468471587167090131 55807404702707380750635197)
    ·
      refine ⟨20927776763515267781488199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55807404702707380750635197 20927776763515267781488199)
      ·
        refine ⟨31391665145272901672232299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20927776763515267781488199 31391665145272901672232299)
        ·
          refine ⟨47087497717909352508348449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31391665145272901672232299 47087497717909352508348449)
          ·
            refine ⟨35315623288432014381261337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47087497717909352508348449 35315623288432014381261337)
            ·
              refine ⟨26486717466324010785946003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35315623288432014381261337 26486717466324010785946003)
              ·
                refine ⟨39730076199486016178919005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26486717466324010785946003 39730076199486016178919005)
                ·
                  refine ⟨14898778574807256067094627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39730076199486016178919005 14898778574807256067094627)
                  ·
                    refine ⟨22348167862210884100641941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14898778574807256067094627 22348167862210884100641941)
                    ·
                      refine ⟨1047570368541135192217591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 22348167862210884100641941 1047570368541135192217591)
                      ·
                        rfl

theorem cell23_2040136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_2040136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040136 prefixEnd_2040136 := by exact prefixLift 2040136
  have htrace : WordTrace (prefixWord ++ tailWord_2040136) baseStart_2040136 baseEnd_2040136 := by
    simpa [prefixWord, tailWord_2040136, baseEnd_2040136] using wordTrace_append hprefix tailTrace_2040136
  have hstable : (prefixWord ++ tailWord_2040136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040136).length < 2 ^ (prefixWord ++ tailWord_2040136).sum := by decide
  have hdescent : baseEnd_2040136 < baseStart_2040136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040163 : List Nat := [1, 1, 1, 5, 2, 1, 5, 7]
def baseStart_2040163 : Nat := 118140960795 + 2040163 * 2 ^ 59
def prefixEnd_2040163 : Nat := 4983230072969 + 3 ^ 40 * 2040163 * 2
def baseEnd_2040163 : Nat := 38799416019215058762221

theorem tailTrace_2040163 : CollatzResearch.WordTrace tailWord_2040163 prefixEnd_2040163 38799416019215058762221 := by
  unfold tailWord_2040163
  simp only [CollatzResearch.WordTrace]
  refine ⟨74410857707845357945413143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49607238471896905296942095 74410857707845357945413143)
  ·
    refine ⟨111616286561768036918119715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74410857707845357945413143 111616286561768036918119715)
    ·
      refine ⟨167424429842652055377179573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111616286561768036918119715 167424429842652055377179573)
      ·
        refine ⟨15696040297748630191610585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167424429842652055377179573 15696040297748630191610585)
        ·
          refine ⟨11772030223311472643707939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15696040297748630191610585 11772030223311472643707939)
          ·
            refine ⟨17658045334967208965561909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772030223311472643707939 17658045334967208965561909)
            ·
              refine ⟨1655441750153175840521429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17658045334967208965561909 1655441750153175840521429)
              ·
                refine ⟨38799416019215058762221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1655441750153175840521429 38799416019215058762221)
                ·
                  rfl

theorem cell23_2040163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 5, 7].length) (baseStart_2040163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040163 prefixEnd_2040163 := by exact prefixLift 2040163
  have htrace : WordTrace (prefixWord ++ tailWord_2040163) baseStart_2040163 baseEnd_2040163 := by
    simpa [prefixWord, tailWord_2040163, baseEnd_2040163] using wordTrace_append hprefix tailTrace_2040163
  have hstable : (prefixWord ++ tailWord_2040163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040163).length < 2 ^ (prefixWord ++ tailWord_2040163).sum := by decide
  have hdescent : baseEnd_2040163 < baseStart_2040163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040170 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2040170 : Nat := 118140960795 + 2040170 * 2 ^ 59
def prefixEnd_2040170 : Nat := 4983230072969 + 3 ^ 40 * 2040170 * 2
def baseEnd_2040170 : Nat := 1047587826883388059192435

theorem tailTrace_2040170 : CollatzResearch.WordTrace tailWord_2040170 prefixEnd_2040170 1047587826883388059192435 := by
  unfold tailWord_2040170
  simp only [CollatzResearch.WordTrace]
  refine ⟨18602778254704999535229491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49607408679213332093945309 18602778254704999535229491)
  ·
    refine ⟨27904167382057499302844237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18602778254704999535229491 27904167382057499302844237)
    ·
      refine ⟨10464062768271562238566589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27904167382057499302844237 10464062768271562238566589)
      ·
        refine ⟨3924023538101835839462471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10464062768271562238566589 3924023538101835839462471)
        ·
          refine ⟨5886035307152753759193707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3924023538101835839462471 5886035307152753759193707)
          ·
            refine ⟨8829052960729130638790561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886035307152753759193707 8829052960729130638790561)
            ·
              refine ⟨6621789720546847979092921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829052960729130638790561 6621789720546847979092921)
              ·
                refine ⟨4966342290410135984319691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621789720546847979092921 4966342290410135984319691)
                ·
                  refine ⟨7449513435615203976479537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966342290410135984319691 7449513435615203976479537)
                  ·
                    refine ⟨5587135076711402982359653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7449513435615203976479537 5587135076711402982359653)
                    ·
                      refine ⟨1047587826883388059192435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5587135076711402982359653 1047587826883388059192435)
                      ·
                        rfl

theorem cell23_2040170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2040170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040170 prefixEnd_2040170 := by exact prefixLift 2040170
  have htrace : WordTrace (prefixWord ++ tailWord_2040170) baseStart_2040170 baseEnd_2040170 := by
    simpa [prefixWord, tailWord_2040170, baseEnd_2040170] using wordTrace_append hprefix tailTrace_2040170
  have hstable : (prefixWord ++ tailWord_2040170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040170).length < 2 ^ (prefixWord ++ tailWord_2040170).sum := by decide
  have hdescent : baseEnd_2040170 < baseStart_2040170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040186 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_2040186 : Nat := 118140960795 + 2040186 * 2 ^ 59
def prefixEnd_2040186 : Nat := 4983230072969 + 3 ^ 40 * 2040186 * 2
def baseEnd_2040186 : Nat := 1047596042573859996592361

theorem tailTrace_2040186 : CollatzResearch.WordTrace tailWord_2040186 prefixEnd_2040186 1047596042573859996592361 := by
  unfold tailWord_2040186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18602924146690508218375103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49607797724508021915666941 18602924146690508218375103)
  ·
    refine ⟨27904386220035762327562655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18602924146690508218375103 27904386220035762327562655)
    ·
      refine ⟨41856579330053643491343983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27904386220035762327562655 41856579330053643491343983)
      ·
        refine ⟨62784868995080465237015975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41856579330053643491343983 62784868995080465237015975)
        ·
          refine ⟨94177303492620697855523963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62784868995080465237015975 94177303492620697855523963)
          ·
            refine ⟨141265955238931046783285945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94177303492620697855523963 141265955238931046783285945)
            ·
              refine ⟨105949466429198285087464459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141265955238931046783285945 105949466429198285087464459)
              ·
                refine ⟨158924199643797427631196689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105949466429198285087464459 158924199643797427631196689)
                ·
                  refine ⟨119193149732848070723397517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158924199643797427631196689 119193149732848070723397517)
                  ·
                    refine ⟨44697431149818026521274069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119193149732848070723397517 44697431149818026521274069)
                    ·
                      refine ⟨1047596042573859996592361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 44697431149818026521274069 1047596042573859996592361)
                      ·
                        rfl

theorem cell23_2040186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_2040186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040186 prefixEnd_2040186 := by exact prefixLift 2040186
  have htrace : WordTrace (prefixWord ++ tailWord_2040186) baseStart_2040186 baseEnd_2040186 := by
    simpa [prefixWord, tailWord_2040186, baseEnd_2040186] using wordTrace_append hprefix tailTrace_2040186
  have hstable : (prefixWord ++ tailWord_2040186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040186).length < 2 ^ (prefixWord ++ tailWord_2040186).sum := by decide
  have hdescent : baseEnd_2040186 < baseStart_2040186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040214 : List Nat := [5, 3, 1, 2, 1, 1, 1, 9]
def baseStart_2040214 : Nat := 118140960795 + 2040214 * 2 ^ 59
def prefixEnd_2040214 : Nat := 4983230072969 + 3 ^ 40 * 2040214 * 2
def baseEnd_2040214 : Nat := 38800385927117995816379

theorem tailTrace_2040214 : CollatzResearch.WordTrace tailWord_2040214 prefixEnd_2040214 38800385927117995816379 := by
  unfold tailWord_2040214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650794864416287103469981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49608478553773729103679797 4650794864416287103469981)
  ·
    refine ⟨1744048074156107663801243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4650794864416287103469981 1744048074156107663801243)
    ·
      refine ⟨2616072111234161495701865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1744048074156107663801243 2616072111234161495701865)
      ·
        refine ⟨1962054083425621121776399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2616072111234161495701865 1962054083425621121776399)
        ·
          refine ⟨2943081125138431682664599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962054083425621121776399 2943081125138431682664599)
          ·
            refine ⟨4414621687707647523996899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943081125138431682664599 4414621687707647523996899)
            ·
              refine ⟨6621932531561471285995349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414621687707647523996899 6621932531561471285995349)
              ·
                refine ⟨38800385927117995816379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6621932531561471285995349 38800385927117995816379)
                ·
                  rfl

theorem cell23_2040214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_2040214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040214 prefixEnd_2040214 := by exact prefixLift 2040214
  have htrace : WordTrace (prefixWord ++ tailWord_2040214) baseStart_2040214 baseEnd_2040214 := by
    simpa [prefixWord, tailWord_2040214, baseEnd_2040214] using wordTrace_append hprefix tailTrace_2040214
  have hstable : (prefixWord ++ tailWord_2040214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040214).length < 2 ^ (prefixWord ++ tailWord_2040214).sum := by decide
  have hdescent : baseEnd_2040214 < baseStart_2040214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040217 : List Nat := [1, 2, 1, 2, 1, 4, 4, 2, 1, 3, 2]
def baseStart_2040217 : Nat := 118140960795 + 2040217 * 2 ^ 59
def prefixEnd_2040217 : Nat := 4983230072969 + 3 ^ 40 * 2040217 * 2
def baseEnd_2040217 : Nat := 1047611960474149375304719

theorem tailTrace_2040217 : CollatzResearch.WordTrace tailWord_2040217 prefixEnd_2040217 1047611960474149375304719 := by
  unfold tailWord_2040217
  simp only [CollatzResearch.WordTrace]
  refine ⟨74412827249649725167878905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49608551499766483445252603 74412827249649725167878905)
  ·
    refine ⟨55809620437237293875909179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74412827249649725167878905 55809620437237293875909179)
    ·
      refine ⟨83714430655855940813863769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55809620437237293875909179 83714430655855940813863769)
      ·
        refine ⟨62785822991891955610397827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83714430655855940813863769 62785822991891955610397827)
        ·
          refine ⟨94178734487837933415596741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62785822991891955610397827 94178734487837933415596741)
          ·
            refine ⟨17658512716469612515424389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94178734487837933415596741 17658512716469612515424389)
            ·
              refine ⟨3310971134338052346642073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17658512716469612515424389 3310971134338052346642073)
              ·
                refine ⟨2483228350753539259981555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310971134338052346642073 2483228350753539259981555)
                ·
                  refine ⟨3724842526130308889972333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483228350753539259981555 3724842526130308889972333)
                  ·
                    refine ⟨1396815947298865833739625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3724842526130308889972333 1396815947298865833739625)
                    ·
                      refine ⟨1047611960474149375304719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396815947298865833739625 1047611960474149375304719)
                      ·
                        rfl

theorem cell23_2040217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 3, 2].length) (baseStart_2040217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040217 prefixEnd_2040217 := by exact prefixLift 2040217
  have htrace : WordTrace (prefixWord ++ tailWord_2040217) baseStart_2040217 baseEnd_2040217 := by
    simpa [prefixWord, tailWord_2040217, baseEnd_2040217] using wordTrace_append hprefix tailTrace_2040217
  have hstable : (prefixWord ++ tailWord_2040217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040217).length < 2 ^ (prefixWord ++ tailWord_2040217).sum := by decide
  have hdescent : baseEnd_2040217 < baseStart_2040217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040225 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 1, 2, 2]
def baseStart_2040225 : Nat := 118140960795 + 2040225 * 2 ^ 59
def prefixEnd_2040225 : Nat := 4983230072969 + 3 ^ 40 * 2040225 * 2
def baseEnd_2040225 : Nat := 1047616068319385344004683

theorem tailTrace_2040225 : CollatzResearch.WordTrace tailWord_2040225 prefixEnd_2040225 1047616068319385344004683 := by
  unfold tailWord_2040225
  simp only [CollatzResearch.WordTrace]
  refine ⟨74413119033620742534170129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49608746022413828356113419 74413119033620742534170129)
  ·
    refine ⟨55809839275215556900627597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74413119033620742534170129 55809839275215556900627597)
    ·
      refine ⟨20928689728205833837735349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55809839275215556900627597 20928689728205833837735349)
      ·
        refine ⟨1962064662019296922287689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20928689728205833837735349 1962064662019296922287689)
        ·
          refine ⟨1471548496514472691715767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1962064662019296922287689 1471548496514472691715767)
          ·
            refine ⟨2207322744771709037573651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1471548496514472691715767 2207322744771709037573651)
            ·
              refine ⟨3310984117157563556360477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207322744771709037573651 3310984117157563556360477)
              ·
                refine ⟨1241619043934086333635179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3310984117157563556360477 1241619043934086333635179)
                ·
                  refine ⟨1862428565901129500452769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1241619043934086333635179 1862428565901129500452769)
                  ·
                    refine ⟨1396821424425847125339577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862428565901129500452769 1396821424425847125339577)
                    ·
                      refine ⟨1047616068319385344004683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396821424425847125339577 1047616068319385344004683)
                      ·
                        rfl

theorem cell23_2040225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_2040225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040225 prefixEnd_2040225 := by exact prefixLift 2040225
  have htrace : WordTrace (prefixWord ++ tailWord_2040225) baseStart_2040225 baseEnd_2040225 := by
    simpa [prefixWord, tailWord_2040225, baseEnd_2040225] using wordTrace_append hprefix tailTrace_2040225
  have hstable : (prefixWord ++ tailWord_2040225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040225).length < 2 ^ (prefixWord ++ tailWord_2040225).sum := by decide
  have hdescent : baseEnd_2040225 < baseStart_2040225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040247 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 4, 2, 2]
def baseStart_2040247 : Nat := 118140960795 + 2040247 * 2 ^ 59
def prefixEnd_2040247 : Nat := 4983230072969 + 3 ^ 40 * 2040247 * 2
def baseEnd_2040247 : Nat := 1047627364893784257929581

theorem tailTrace_2040247 : CollatzResearch.WordTrace tailWord_2040247 prefixEnd_2040247 1047627364893784257929581 := by
  unfold tailWord_2040247
  simp only [CollatzResearch.WordTrace]
  refine ⟨74413921439541040291470995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49609280959694026860980663 74413921439541040291470995)
  ·
    refine ⟨111620882159311560437206493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74413921439541040291470995 111620882159311560437206493)
    ·
      refine ⟨41857830809741835163952435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111620882159311560437206493 41857830809741835163952435)
      ·
        refine ⟨62786746214612752745928653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41857830809741835163952435 62786746214612752745928653)
        ·
          refine ⟨23545029830479782279723245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62786746214612752745928653 23545029830479782279723245)
          ·
            refine ⟨8829386186429918354896217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23545029830479782279723245 8829386186429918354896217)
            ·
              refine ⟨6622039639822438766172163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829386186429918354896217 6622039639822438766172163)
              ·
                refine ⟨9933059459733658149258245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622039639822438766172163 9933059459733658149258245)
                ·
                  refine ⟨1862448648700060902985921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9933059459733658149258245 1862448648700060902985921)
                  ·
                    refine ⟨1396836486525045677239441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862448648700060902985921 1396836486525045677239441)
                    ·
                      refine ⟨1047627364893784257929581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396836486525045677239441 1047627364893784257929581)
                      ·
                        rfl

theorem cell23_2040247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 4, 2, 2].length) (baseStart_2040247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040247 prefixEnd_2040247 := by exact prefixLift 2040247
  have htrace : WordTrace (prefixWord ++ tailWord_2040247) baseStart_2040247 baseEnd_2040247 := by
    simpa [prefixWord, tailWord_2040247, baseEnd_2040247] using wordTrace_append hprefix tailTrace_2040247
  have hstable : (prefixWord ++ tailWord_2040247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040247).length < 2 ^ (prefixWord ++ tailWord_2040247).sum := by decide
  have hdescent : baseEnd_2040247 < baseStart_2040247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040264 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 2, 2, 2]
def baseStart_2040264 : Nat := 118140960795 + 2040264 * 2 ^ 59
def prefixEnd_2040264 : Nat := 4983230072969 + 3 ^ 40 * 2040264 * 2
def baseEnd_2040264 : Nat := 1047636094064910691417003

theorem tailTrace_2040264 : CollatzResearch.WordTrace tailWord_2040264 prefixEnd_2040264 1047636094064910691417003 := by
  unfold tailWord_2040264
  simp only [CollatzResearch.WordTrace]
  refine ⟨37207270740239726097419923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49609694320319634796559897 37207270740239726097419923)
  ·
    refine ⟨55810906110359589146129885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37207270740239726097419923 55810906110359589146129885)
    ·
      refine ⟨20929089791384845929798707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55810906110359589146129885 20929089791384845929798707)
      ·
        refine ⟨31393634687077268894698061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20929089791384845929798707 31393634687077268894698061)
        ·
          refine ⟨11772613007653975835511773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31393634687077268894698061 11772613007653975835511773)
          ·
            refine ⟨4414729877870240938316915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11772613007653975835511773 4414729877870240938316915)
            ·
              refine ⟨6622094816805361407475373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414729877870240938316915 6622094816805361407475373)
              ·
                refine ⟨2483285556302010527803265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6622094816805361407475373 2483285556302010527803265)
                ·
                  refine ⟨1862464167226507895852449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2483285556302010527803265 1862464167226507895852449)
                  ·
                    refine ⟨1396848125419880921889337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862464167226507895852449 1396848125419880921889337)
                    ·
                      refine ⟨1047636094064910691417003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396848125419880921889337 1047636094064910691417003)
                      ·
                        rfl

theorem cell23_2040264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 2, 2, 2].length) (baseStart_2040264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040264 prefixEnd_2040264 := by exact prefixLift 2040264
  have htrace : WordTrace (prefixWord ++ tailWord_2040264) baseStart_2040264 baseEnd_2040264 := by
    simpa [prefixWord, tailWord_2040264, baseEnd_2040264] using wordTrace_append hprefix tailTrace_2040264
  have hstable : (prefixWord ++ tailWord_2040264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040264).length < 2 ^ (prefixWord ++ tailWord_2040264).sum := by decide
  have hdescent : baseEnd_2040264 < baseStart_2040264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040303 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 4]
def baseStart_2040303 : Nat := 118140960795 + 2040303 * 2 ^ 59
def prefixEnd_2040303 : Nat := 4983230072969 + 3 ^ 40 * 2040303 * 2
def baseEnd_2040303 : Nat := 1047656119810436038829323

theorem tailTrace_2040303 : CollatzResearch.WordTrace tailWord_2040303 prefixEnd_2040303 1047656119810436038829323 := by
  unfold tailWord_2040303
  simp only [CollatzResearch.WordTrace]
  refine ⟨74415963927338161855509563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49610642618225441237006375 74415963927338161855509563)
  ·
    refine ⟨111623945891007242783264345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74415963927338161855509563 111623945891007242783264345)
    ·
      refine ⟨83717959418255432087448259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111623945891007242783264345 83717959418255432087448259)
      ·
        refine ⟨125576939127383148131172389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83717959418255432087448259 125576939127383148131172389)
        ·
          refine ⟨23545676086384340274594823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125576939127383148131172389 23545676086384340274594823)
          ·
            refine ⟨35318514129576510411892235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23545676086384340274594823 35318514129576510411892235)
            ·
              refine ⟨52977771194364765617838353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35318514129576510411892235 52977771194364765617838353)
              ·
                refine ⟨39733328395773574213378765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52977771194364765617838353 39733328395773574213378765)
                ·
                  refine ⟨14899998148415090330017037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39733328395773574213378765 14899998148415090330017037)
                  ·
                    refine ⟨5587499305655658873756389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14899998148415090330017037 5587499305655658873756389)
                    ·
                      refine ⟨1047656119810436038829323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5587499305655658873756389 1047656119810436038829323)
                      ·
                        rfl

theorem cell23_2040303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_2040303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040303 prefixEnd_2040303 := by exact prefixLift 2040303
  have htrace : WordTrace (prefixWord ++ tailWord_2040303) baseStart_2040303 baseEnd_2040303 := by
    simpa [prefixWord, tailWord_2040303, baseEnd_2040303] using wordTrace_append hprefix tailTrace_2040303
  have hstable : (prefixWord ++ tailWord_2040303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040303).length < 2 ^ (prefixWord ++ tailWord_2040303).sum := by decide
  have hdescent : baseEnd_2040303 < baseStart_2040303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040310 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2040310 : Nat := 118140960795 + 2040310 * 2 ^ 59
def prefixEnd_2040310 : Nat := 4983230072969 + 3 ^ 40 * 2040310 * 2
def baseEnd_2040310 : Nat := 1047659714175017511441791

theorem tailTrace_2040310 : CollatzResearch.WordTrace tailWord_2040310 prefixEnd_2040310 1047659714175017511441791 := by
  unfold tailWord_2040310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651013702394550128188399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 49610812825541868034009589 4651013702394550128188399)
  ·
    refine ⟨6976520553591825192282599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4651013702394550128188399 6976520553591825192282599)
    ·
      refine ⟨10464780830387737788423899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976520553591825192282599 10464780830387737788423899)
      ·
        refine ⟨15697171245581606682635849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10464780830387737788423899 15697171245581606682635849)
        ·
          refine ⟨11772878434186205011976887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15697171245581606682635849 11772878434186205011976887)
          ·
            refine ⟨17659317651279307517965331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772878434186205011976887 17659317651279307517965331)
            ·
              refine ⟨26488976476918961276947997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17659317651279307517965331 26488976476918961276947997)
              ·
                refine ⟨9933366178844610478855499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26488976476918961276947997 9933366178844610478855499)
                ·
                  refine ⟨14900049268266915718283249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9933366178844610478855499 14900049268266915718283249)
                  ·
                    refine ⟨11175036951200186788712437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14900049268266915718283249 11175036951200186788712437)
                    ·
                      refine ⟨1047659714175017511441791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11175036951200186788712437 1047659714175017511441791)
                      ·
                        rfl

theorem cell23_2040310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2040310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040310 prefixEnd_2040310 := by exact prefixLift 2040310
  have htrace : WordTrace (prefixWord ++ tailWord_2040310) baseStart_2040310 baseEnd_2040310 := by
    simpa [prefixWord, tailWord_2040310, baseEnd_2040310] using wordTrace_append hprefix tailTrace_2040310
  have hstable : (prefixWord ++ tailWord_2040310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040310).length < 2 ^ (prefixWord ++ tailWord_2040310).sum := by decide
  have hdescent : baseEnd_2040310 < baseStart_2040310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040377 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 6]
def baseStart_2040377 : Nat := 118140960795 + 2040377 * 2 ^ 59
def prefixEnd_2040377 : Nat := 4983230072969 + 3 ^ 40 * 2040377 * 2
def baseEnd_2040377 : Nat := 116410457486540972144887

theorem tailTrace_2040377 : CollatzResearch.WordTrace tailWord_2040377 prefixEnd_2040377 116410457486540972144887 := by
  unfold tailWord_2040377
  simp only [CollatzResearch.WordTrace]
  refine ⟨74418662929070072493703385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49612441952713381662468923 74418662929070072493703385)
  ·
    refine ⟨55813997196802554370277539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74418662929070072493703385 55813997196802554370277539)
    ·
      refine ⟨83720995795203831555416309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55813997196802554370277539 83720995795203831555416309)
      ·
        refine ⟨7848843355800359208320279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83720995795203831555416309 7848843355800359208320279)
        ·
          refine ⟨11773265033700538812480419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848843355800359208320279 11773265033700538812480419)
          ·
            refine ⟨17659897550550808218720629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773265033700538812480419 17659897550550808218720629)
            ·
              refine ⟨1655615395364138270505059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17659897550550808218720629 1655615395364138270505059)
              ·
                refine ⟨2483423093046207405757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655615395364138270505059 2483423093046207405757589)
                ·
                  refine ⟨116410457486540972144887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2483423093046207405757589 116410457486540972144887)
                  ·
                    rfl

theorem cell23_2040377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 6].length) (baseStart_2040377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040377 prefixEnd_2040377 := by exact prefixLift 2040377
  have htrace : WordTrace (prefixWord ++ tailWord_2040377) baseStart_2040377 baseEnd_2040377 := by
    simpa [prefixWord, tailWord_2040377, baseEnd_2040377] using wordTrace_append hprefix tailTrace_2040377
  have hstable : (prefixWord ++ tailWord_2040377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040377).length < 2 ^ (prefixWord ++ tailWord_2040377).sum := by decide
  have hdescent : baseEnd_2040377 < baseStart_2040377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040410 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_2040410 : Nat := 118140960795 + 2040410 * 2 ^ 59
def prefixEnd_2040410 : Nat := 4983230072969 + 3 ^ 40 * 2040410 * 2
def baseEnd_2040410 : Nat := 1047711062240467120191331

theorem tailTrace_2040410 : CollatzResearch.WordTrace tailWord_2040410 prefixEnd_2040410 1047711062240467120191331 := by
  unfold tailWord_2040410
  simp only [CollatzResearch.WordTrace]
  refine ⟨18604966634487629782413671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49613244358633679419769789 18604966634487629782413671)
  ·
    refine ⟨27907449951731444673620507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18604966634487629782413671 27907449951731444673620507)
    ·
      refine ⟨41861174927597167010430761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27907449951731444673620507 41861174927597167010430761)
      ·
        refine ⟨31395881195697875257823071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41861174927597167010430761 31395881195697875257823071)
        ·
          refine ⟨47093821793546812886734607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31395881195697875257823071 47093821793546812886734607)
          ·
            refine ⟨70640732690320219330101911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47093821793546812886734607 70640732690320219330101911)
            ·
              refine ⟨105961099035480328995152867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70640732690320219330101911 105961099035480328995152867)
              ·
                refine ⟨158941648553220493492729301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105961099035480328995152867 158941648553220493492729301)
                ·
                  refine ⟨3725194887966105316235843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 158941648553220493492729301 3725194887966105316235843)
                  ·
                    refine ⟨5587792331949157974353765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725194887966105316235843 5587792331949157974353765)
                    ·
                      refine ⟨1047711062240467120191331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5587792331949157974353765 1047711062240467120191331)
                      ·
                        rfl

theorem cell23_2040410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_2040410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040410 prefixEnd_2040410 := by exact prefixLift 2040410
  have htrace : WordTrace (prefixWord ++ tailWord_2040410) baseStart_2040410 baseEnd_2040410 := by
    simpa [prefixWord, tailWord_2040410, baseEnd_2040410] using wordTrace_append hprefix tailTrace_2040410
  have hstable : (prefixWord ++ tailWord_2040410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040410).length < 2 ^ (prefixWord ++ tailWord_2040410).sum := by decide
  have hdescent : baseEnd_2040410 < baseStart_2040410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040421 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_2040421 : Nat := 118140960795 + 2040421 * 2 ^ 59
def prefixEnd_2040421 : Nat := 4983230072969 + 3 ^ 40 * 2040421 * 2
def baseEnd_2040421 : Nat := 1047716710527666577153781

theorem tailTrace_2040421 : CollatzResearch.WordTrace tailWord_2040421 prefixEnd_2040421 1047716710527666577153781 := by
  unfold tailWord_2040421
  simp only [CollatzResearch.WordTrace]
  refine ⟨74420267740910668008305117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49613511827273778672203411 74420267740910668008305117)
  ·
    refine ⟨27907600402841500503114419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74420267740910668008305117 27907600402841500503114419)
    ·
      refine ⟨41861400604262250754671629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27907600402841500503114419 41861400604262250754671629)
      ·
        refine ⟨15698025226598344033001861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41861400604262250754671629 15698025226598344033001861)
        ·
          refine ⟨2943379729987189506187849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15698025226598344033001861 2943379729987189506187849)
          ·
            refine ⟨2207534797490392129640887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943379729987189506187849 2207534797490392129640887)
            ·
              refine ⟨3311302196235588194461331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207534797490392129640887 3311302196235588194461331)
              ·
                refine ⟨4966953294353382291691997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311302196235588194461331 4966953294353382291691997)
                ·
                  refine ⟨1862607485382518359384499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4966953294353382291691997 1862607485382518359384499)
                  ·
                    refine ⟨2793911228073777539076749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1862607485382518359384499 2793911228073777539076749)
                    ·
                      refine ⟨1047716710527666577153781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2793911228073777539076749 1047716710527666577153781)
                      ·
                        rfl

theorem cell23_2040421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_2040421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040421 prefixEnd_2040421 := by exact prefixLift 2040421
  have htrace : WordTrace (prefixWord ++ tailWord_2040421) baseStart_2040421 baseEnd_2040421 := by
    simpa [prefixWord, tailWord_2040421, baseEnd_2040421] using wordTrace_append hprefix tailTrace_2040421
  have hstable : (prefixWord ++ tailWord_2040421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040421).length < 2 ^ (prefixWord ++ tailWord_2040421).sum := by decide
  have hdescent : baseEnd_2040421 < baseStart_2040421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040444 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_2040444 : Nat := 118140960795 + 2040444 * 2 ^ 59
def prefixEnd_2040444 : Nat := 4983230072969 + 3 ^ 40 * 2040444 * 2
def baseEnd_2040444 : Nat := 1047728520582719987166175

theorem tailTrace_2040444 : CollatzResearch.WordTrace tailWord_2040444 prefixEnd_2040444 1047728520582719987166175 := by
  unfold tailWord_2040444
  simp only [CollatzResearch.WordTrace]
  refine ⟨37210553309913671468196193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49614071079884895290928257 37210553309913671468196193)
  ·
    refine ⟨27907914982435253601147145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37210553309913671468196193 27907914982435253601147145)
    ·
      refine ⟨20930936236826440200860359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27907914982435253601147145 20930936236826440200860359)
      ·
        refine ⟨31396404355239660301290539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20930936236826440200860359 31396404355239660301290539)
        ·
          refine ⟨47094606532859490451935809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31396404355239660301290539 47094606532859490451935809)
          ·
            refine ⟨35320954899644617838951857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47094606532859490451935809 35320954899644617838951857)
            ·
              refine ⟨26490716174733463379213893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35320954899644617838951857 26490716174733463379213893)
              ·
                refine ⟨4967009282762524383602605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26490716174733463379213893 4967009282762524383602605)
                ·
                  refine ⟨1862628481035946643850977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4967009282762524383602605 1862628481035946643850977)
                  ·
                    refine ⟨1396971360776959982888233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1862628481035946643850977 1396971360776959982888233)
                    ·
                      refine ⟨1047728520582719987166175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1396971360776959982888233 1047728520582719987166175)
                      ·
                        rfl

theorem cell23_2040444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_2040444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040444 prefixEnd_2040444 := by exact prefixLift 2040444
  have htrace : WordTrace (prefixWord ++ tailWord_2040444) baseStart_2040444 baseEnd_2040444 := by
    simpa [prefixWord, tailWord_2040444, baseEnd_2040444] using wordTrace_append hprefix tailTrace_2040444
  have hstable : (prefixWord ++ tailWord_2040444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040444).length < 2 ^ (prefixWord ++ tailWord_2040444).sum := by decide
  have hdescent : baseEnd_2040444 < baseStart_2040444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040447 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 3]
def baseStart_2040447 : Nat := 118140960795 + 2040447 * 2 ^ 59
def prefixEnd_2040447 : Nat := 4983230072969 + 3 ^ 40 * 2040447 * 2
def baseEnd_2040447 : Nat := 1047730061024683475428661

theorem tailTrace_2040447 : CollatzResearch.WordTrace tailWord_2040447 prefixEnd_2040447 1047730061024683475428661 := by
  unfold tailWord_2040447
  simp only [CollatzResearch.WordTrace]
  refine ⟨74421216038816474448751595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49614144025877649632501063 74421216038816474448751595)
  ·
    refine ⟨111631824058224711673127393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74421216038816474448751595 111631824058224711673127393)
    ·
      refine ⟨83723868043668533754845545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111631824058224711673127393 83723868043668533754845545)
      ·
        refine ⟨62792901032751400316134159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83723868043668533754845545 62792901032751400316134159)
        ·
          refine ⟨94189351549127100474201239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62792901032751400316134159 94189351549127100474201239)
          ·
            refine ⟨141284027323690650711301859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94189351549127100474201239 141284027323690650711301859)
            ·
              refine ⟨211926040985535976066952789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141284027323690650711301859 211926040985535976066952789)
              ·
                refine ⟨2483508292799249719534603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 211926040985535976066952789 2483508292799249719534603)
                ·
                  refine ⟨3725262439198874579301905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483508292799249719534603 3725262439198874579301905)
                  ·
                    refine ⟨2793946829399155934476429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725262439198874579301905 2793946829399155934476429)
                    ·
                      refine ⟨1047730061024683475428661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2793946829399155934476429 1047730061024683475428661)
                      ·
                        rfl

theorem cell23_2040447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_2040447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040447 prefixEnd_2040447 := by exact prefixLift 2040447
  have htrace : WordTrace (prefixWord ++ tailWord_2040447) baseStart_2040447 baseEnd_2040447 := by
    simpa [prefixWord, tailWord_2040447, baseEnd_2040447] using wordTrace_append hprefix tailTrace_2040447
  have hstable : (prefixWord ++ tailWord_2040447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040447).length < 2 ^ (prefixWord ++ tailWord_2040447).sum := by decide
  have hdescent : baseEnd_2040447 < baseStart_2040447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040557 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 7]
def baseStart_2040557 : Nat := 118140960795 + 2040557 * 2 ^ 59
def prefixEnd_2040557 : Nat := 4983230072969 + 3 ^ 40 * 2040557 * 2
def baseEnd_2040557 : Nat := 116420727099630893894795

theorem tailTrace_2040557 : CollatzResearch.WordTrace tailWord_2040557 prefixEnd_2040557 116420727099630893894795 := by
  unfold tailWord_2040557
  simp only [CollatzResearch.WordTrace]
  refine ⟨74425228068417963235255925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49616818712278642156837283 74425228068417963235255925)
  ·
    refine ⟨6977365131414184053305243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74425228068417963235255925 6977365131414184053305243)
    ·
      refine ⟨10466047697121276079957865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6977365131414184053305243 10466047697121276079957865)
      ·
        refine ⟨7849535772840957059968399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10466047697121276079957865 7849535772840957059968399)
        ·
          refine ⟨11774303659261435589952599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7849535772840957059968399 11774303659261435589952599)
          ·
            refine ⟨17661455488892153384928899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774303659261435589952599 17661455488892153384928899)
            ·
              refine ⟨26492183233338230077393349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17661455488892153384928899 26492183233338230077393349)
              ·
                refine ⟨4967284356250918139511253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26492183233338230077393349 4967284356250918139511253)
                ·
                  refine ⟨116420727099630893894795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4967284356250918139511253 116420727099630893894795)
                  ·
                    rfl

theorem cell23_2040557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_2040557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040557 prefixEnd_2040557 := by exact prefixLift 2040557
  have htrace : WordTrace (prefixWord ++ tailWord_2040557) baseStart_2040557 baseEnd_2040557 := by
    simpa [prefixWord, tailWord_2040557, baseEnd_2040557] using wordTrace_append hprefix tailTrace_2040557
  have hstable : (prefixWord ++ tailWord_2040557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040557).length < 2 ^ (prefixWord ++ tailWord_2040557).sum := by decide
  have hdescent : baseEnd_2040557 < baseStart_2040557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040597 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_2040597 : Nat := 118140960795 + 2040597 * 2 ^ 59
def prefixEnd_2040597 : Nat := 4983230072969 + 3 ^ 40 * 2040597 * 2
def baseEnd_2040597 : Nat := 1047807083122857888552971

theorem tailTrace_2040597 : CollatzResearch.WordTrace tailWord_2040597 prefixEnd_2040597 1047807083122857888552971 := by
  unfold tailWord_2040597
  simp only [CollatzResearch.WordTrace]
  refine ⟨74426686988273050066712045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49617791325515366711141363 74426686988273050066712045)
  ·
    refine ⟨27910007620602393775017017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74426686988273050066712045 27910007620602393775017017)
    ·
      refine ⟨20932505715451795331262763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27910007620602393775017017 20932505715451795331262763)
      ·
        refine ⟨31398758573177692996894145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20932505715451795331262763 31398758573177692996894145)
        ·
          refine ⟨23549068929883269747670609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31398758573177692996894145 23549068929883269747670609)
          ·
            refine ⟨17661801697412452310752957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23549068929883269747670609 17661801697412452310752957)
            ·
              refine ⟨6623175636529669616532359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17661801697412452310752957 6623175636529669616532359)
              ·
                refine ⟨9934763454794504424798539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623175636529669616532359 9934763454794504424798539)
                ·
                  refine ⟨14902145182191756637197809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934763454794504424798539 14902145182191756637197809)
                  ·
                    refine ⟨11176608886643817477898357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14902145182191756637197809 11176608886643817477898357)
                    ·
                      refine ⟨1047807083122857888552971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11176608886643817477898357 1047807083122857888552971)
                      ·
                        rfl

theorem cell23_2040597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_2040597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040597 prefixEnd_2040597 := by exact prefixLift 2040597
  have htrace : WordTrace (prefixWord ++ tailWord_2040597) baseStart_2040597 baseEnd_2040597 := by
    simpa [prefixWord, tailWord_2040597, baseEnd_2040597] using wordTrace_append hprefix tailTrace_2040597
  have hstable : (prefixWord ++ tailWord_2040597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040597).length < 2 ^ (prefixWord ++ tailWord_2040597).sum := by decide
  have hdescent : baseEnd_2040597 < baseStart_2040597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040701 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 2, 3, 2]
def baseStart_2040701 : Nat := 118140960795 + 2040701 * 2 ^ 59
def prefixEnd_2040701 : Nat := 4983230072969 + 3 ^ 40 * 2040701 * 2
def baseEnd_2040701 : Nat := 1047860485110925481652493

theorem tailTrace_2040701 : CollatzResearch.WordTrace tailWord_2040701 prefixEnd_2040701 1047860485110925481652493 := by
  unfold tailWord_2040701
  simp only [CollatzResearch.WordTrace]
  refine ⟨74430480179896275828497957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49620320119930850552331971 74430480179896275828497957)
  ·
    refine ⟨13955715033730551717843367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74430480179896275828497957 13955715033730551717843367)
    ·
      refine ⟨20933572550595827576765051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13955715033730551717843367 20933572550595827576765051)
      ·
        refine ⟨31400358825893741365147577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20933572550595827576765051 31400358825893741365147577)
        ·
          refine ⟨23550269119420306023860683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31400358825893741365147577 23550269119420306023860683)
          ·
            refine ⟨35325403679130459035791025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23550269119420306023860683 35325403679130459035791025)
            ·
              refine ⟨26494052759347844276843269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35325403679130459035791025 26494052759347844276843269)
              ·
                refine ⟨4967634892377720801908113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26494052759347844276843269 4967634892377720801908113)
                ·
                  refine ⟨3725726169283290601431085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4967634892377720801908113 3725726169283290601431085)
                  ·
                    refine ⟨1397147313481233975536657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725726169283290601431085 1397147313481233975536657)
                    ·
                      refine ⟨1047860485110925481652493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397147313481233975536657 1047860485110925481652493)
                      ·
                        rfl

theorem cell23_2040701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_2040701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040701 prefixEnd_2040701 := by exact prefixLift 2040701
  have htrace : WordTrace (prefixWord ++ tailWord_2040701) baseStart_2040701 baseEnd_2040701 := by
    simpa [prefixWord, tailWord_2040701, baseEnd_2040701] using wordTrace_append hprefix tailTrace_2040701
  have hstable : (prefixWord ++ tailWord_2040701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040701).length < 2 ^ (prefixWord ++ tailWord_2040701).sum := by decide
  have hdescent : baseEnd_2040701 < baseStart_2040701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040802 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2040802 : Nat := 118140960795 + 2040802 * 2 ^ 59
def prefixEnd_2040802 : Nat := 4983230072969 + 3 ^ 40 * 2040802 * 2
def baseEnd_2040802 : Nat := 1047912346657029586489529

theorem tailTrace_2040802 : CollatzResearch.WordTrace tailWord_2040802 prefixEnd_2040802 1047912346657029586489529 := by
  unfold tailWord_2040802
  simp only [CollatzResearch.WordTrace]
  refine ⟨18608540988132592519481165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49622775968353580051949773 18608540988132592519481165)
  ·
    refine ⟨6978202870549722194805437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18608540988132592519481165 6978202870549722194805437)
    ·
      refine ⟨2616826076456145823052039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6978202870549722194805437 2616826076456145823052039)
      ·
        refine ⟨3925239114684218734578059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616826076456145823052039 3925239114684218734578059)
        ·
          refine ⟨5887858672026328101867089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925239114684218734578059 5887858672026328101867089)
          ·
            refine ⟨4415894004019746076400317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5887858672026328101867089 4415894004019746076400317)
            ·
              refine ⟨1655960251507404778650119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4415894004019746076400317 1655960251507404778650119)
              ·
                refine ⟨2483940377261107167975179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1655960251507404778650119 2483940377261107167975179)
                ·
                  refine ⟨3725910565891660751962769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483940377261107167975179 3725910565891660751962769)
                  ·
                    refine ⟨2794432924418745563972077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725910565891660751962769 2794432924418745563972077)
                    ·
                      refine ⟨1047912346657029586489529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2794432924418745563972077 1047912346657029586489529)
                      ·
                        rfl

theorem cell23_2040802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2040802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040802 prefixEnd_2040802 := by exact prefixLift 2040802
  have htrace : WordTrace (prefixWord ++ tailWord_2040802) baseStart_2040802 baseEnd_2040802 := by
    simpa [prefixWord, tailWord_2040802, baseEnd_2040802] using wordTrace_append hprefix tailTrace_2040802
  have hstable : (prefixWord ++ tailWord_2040802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040802).length < 2 ^ (prefixWord ++ tailWord_2040802).sum := by decide
  have hdescent : baseEnd_2040802 < baseStart_2040802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040808 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_2040808 : Nat := 118140960795 + 2040808 * 2 ^ 59
def prefixEnd_2040808 : Nat := 4983230072969 + 3 ^ 40 * 2040808 * 2
def baseEnd_2040808 : Nat := 1047915427540956563014501

theorem tailTrace_2040808 : CollatzResearch.WordTrace tailWord_2040808 prefixEnd_2040808 1047915427540956563014501 := by
  unfold tailWord_2040808
  simp only [CollatzResearch.WordTrace]
  refine ⟨37217191395254316551321539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49622921860339088735095385 37217191395254316551321539)
  ·
    refine ⟨55825787092881474826982309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37217191395254316551321539 55825787092881474826982309)
    ·
      refine ⟨10467335079915276530059183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55825787092881474826982309 10467335079915276530059183)
      ·
        refine ⟨15701002619872914795088775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10467335079915276530059183 15701002619872914795088775)
        ·
          refine ⟨23551503929809372192633163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15701002619872914795088775 23551503929809372192633163)
          ·
            refine ⟨35327255894714058288949745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23551503929809372192633163 35327255894714058288949745)
            ·
              refine ⟨26495441921035543716712309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35327255894714058288949745 26495441921035543716712309)
              ·
                refine ⟨2483947680097082223441779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26495441921035543716712309 2483947680097082223441779)
                ·
                  refine ⟨3725921520145623335162669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483947680097082223441779 3725921520145623335162669)
                  ·
                    refine ⟨1397220570054608750686001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3725921520145623335162669 1397220570054608750686001)
                    ·
                      refine ⟨1047915427540956563014501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397220570054608750686001 1047915427540956563014501)
                      ·
                        rfl

theorem cell23_2040808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_2040808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040808 prefixEnd_2040808 := by exact prefixLift 2040808
  have htrace : WordTrace (prefixWord ++ tailWord_2040808) baseStart_2040808 baseEnd_2040808 := by
    simpa [prefixWord, tailWord_2040808, baseEnd_2040808] using wordTrace_append hprefix tailTrace_2040808
  have hstable : (prefixWord ++ tailWord_2040808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040808).length < 2 ^ (prefixWord ++ tailWord_2040808).sum := by decide
  have hdescent : baseEnd_2040808 < baseStart_2040808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040844 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 9]
def baseStart_2040844 : Nat := 118140960795 + 2040844 * 2 ^ 59
def prefixEnd_2040844 : Nat := 4983230072969 + 3 ^ 40 * 2040844 * 2
def baseEnd_2040844 : Nat := 116437101427168713573815

theorem tailTrace_2040844 : CollatzResearch.WordTrace tailWord_2040844 prefixEnd_2040844 116437101427168713573815 := by
  unfold tailWord_2040844
  simp only [CollatzResearch.WordTrace]
  refine ⟨37217847909189105625476793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49623797212252140833969057 37217847909189105625476793)
  ·
    refine ⟨27913385931891829219107595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37217847909189105625476793 27913385931891829219107595)
    ·
      refine ⟨41870078897837743828661393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27913385931891829219107595 41870078897837743828661393)
      ·
        refine ⟨31402559173378307871496045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41870078897837743828661393 31402559173378307871496045)
        ·
          refine ⟨11775959690016865451811017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31402559173378307871496045 11775959690016865451811017)
          ·
            refine ⟨8831969767512649088858263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11775959690016865451811017 8831969767512649088858263)
            ·
              refine ⟨13247954651268973633287395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8831969767512649088858263 13247954651268973633287395)
              ·
                refine ⟨19871931976903460449931093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13247954651268973633287395 19871931976903460449931093)
                ·
                  refine ⟨116437101427168713573815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 19871931976903460449931093 116437101427168713573815)
                  ·
                    rfl

theorem cell23_2040844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_2040844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040844 prefixEnd_2040844 := by exact prefixLift 2040844
  have htrace : WordTrace (prefixWord ++ tailWord_2040844) baseStart_2040844 baseEnd_2040844 := by
    simpa [prefixWord, tailWord_2040844, baseEnd_2040844] using wordTrace_append hprefix tailTrace_2040844
  have hstable : (prefixWord ++ tailWord_2040844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040844).length < 2 ^ (prefixWord ++ tailWord_2040844).sum := by decide
  have hdescent : baseEnd_2040844 < baseStart_2040844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040878 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 5]
def baseStart_2040878 : Nat := 118140960795 + 2040878 * 2 ^ 59
def prefixEnd_2040878 : Nat := 4983230072969 + 3 ^ 40 * 2040878 * 2
def baseEnd_2040878 : Nat := 116439041242974587682131

theorem tailTrace_2040878 : CollatzResearch.WordTrace tailWord_2040878 prefixEnd_2040878 116439041242974587682131 := by
  unfold tailWord_2040878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9304616987531879382211411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49624623933503356705127525 9304616987531879382211411)
  ·
    refine ⟨13956925481297819073317117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9304616987531879382211411 13956925481297819073317117)
    ·
      refine ⟨5233847055486682152493919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13956925481297819073317117 5233847055486682152493919)
      ·
        refine ⟨7850770583230023228740879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5233847055486682152493919 7850770583230023228740879)
        ·
          refine ⟨11776155874845034843111319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7850770583230023228740879 11776155874845034843111319)
          ·
            refine ⟨17664233812267552264666979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11776155874845034843111319 17664233812267552264666979)
            ·
              refine ⟨26496350718401328397000469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17664233812267552264666979 26496350718401328397000469)
              ·
                refine ⟨1242016439925062268609397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26496350718401328397000469 1242016439925062268609397)
                ·
                  refine ⟨116439041242974587682131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1242016439925062268609397 116439041242974587682131)
                  ·
                    rfl

theorem cell23_2040878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 5].length) (baseStart_2040878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040878 prefixEnd_2040878 := by exact prefixLift 2040878
  have htrace : WordTrace (prefixWord ++ tailWord_2040878) baseStart_2040878 baseEnd_2040878 := by
    simpa [prefixWord, tailWord_2040878, baseEnd_2040878] using wordTrace_append hprefix tailTrace_2040878
  have hstable : (prefixWord ++ tailWord_2040878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040878).length < 2 ^ (prefixWord ++ tailWord_2040878).sum := by decide
  have hdescent : baseEnd_2040878 < baseStart_2040878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040904 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_2040904 : Nat := 118140960795 + 2040904 * 2 ^ 59
def prefixEnd_2040904 : Nat := 4983230072969 + 3 ^ 40 * 2040904 * 2
def baseEnd_2040904 : Nat := 349321573894596062471353

theorem tailTrace_2040904 : CollatzResearch.WordTrace tailWord_2040904 prefixEnd_2040904 349321573894596062471353 := by
  unfold tailWord_2040904
  simp only [CollatzResearch.WordTrace]
  refine ⟨37218942099080420749068883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 49625256132107227665425177 37218942099080420749068883)
  ·
    refine ⟨55828413148620631123603325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37218942099080420749068883 55828413148620631123603325)
    ·
      refine ⟨20935654930732736671351247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55828413148620631123603325 20935654930732736671351247)
      ·
        refine ⟨31403482396099105007026871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20935654930732736671351247 31403482396099105007026871)
        ·
          refine ⟨47105223594148657510540307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31403482396099105007026871 47105223594148657510540307)
          ·
            refine ⟨70657835391222986265810461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47105223594148657510540307 70657835391222986265810461)
            ·
              refine ⟨26496688271708619849678923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70657835391222986265810461 26496688271708619849678923)
              ·
                refine ⟨39745032407562929774518385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26496688271708619849678923 39745032407562929774518385)
                ·
                  refine ⟨29808774305672197330888789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39745032407562929774518385 29808774305672197330888789)
                  ·
                    refine ⟨349321573894596062471353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29808774305672197330888789 349321573894596062471353)
                    ·
                      rfl

theorem cell23_2040904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_2040904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040904 prefixEnd_2040904 := by exact prefixLift 2040904
  have htrace : WordTrace (prefixWord ++ tailWord_2040904) baseStart_2040904 baseEnd_2040904 := by
    simpa [prefixWord, tailWord_2040904, baseEnd_2040904] using wordTrace_append hprefix tailTrace_2040904
  have hstable : (prefixWord ++ tailWord_2040904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040904).length < 2 ^ (prefixWord ++ tailWord_2040904).sum := by decide
  have hdescent : baseEnd_2040904 < baseStart_2040904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040925 : List Nat := [1, 4, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_2040925 : Nat := 118140960795 + 2040925 * 2 ^ 59
def prefixEnd_2040925 : Nat := 4983230072969 + 3 ^ 40 * 2040925 * 2
def baseEnd_2040925 : Nat := 349325168259177535083821

theorem tailTrace_2040925 : CollatzResearch.WordTrace tailWord_2040925 prefixEnd_2040925 349325168259177535083821 := by
  unfold tailWord_2040925
  simp only [CollatzResearch.WordTrace]
  refine ⟨74438650131084762084652229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49625766754056508056434819 74438650131084762084652229)
  ·
    refine ⟨13957246899578392890872293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74438650131084762084652229 13957246899578392890872293)
    ·
      refine ⟨2616983793670948667038555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13957246899578392890872293 2616983793670948667038555)
      ·
        refine ⟨3925475690506423000557833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2616983793670948667038555 3925475690506423000557833)
        ·
          refine ⟨2944106767879817250418375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925475690506423000557833 2944106767879817250418375)
          ·
            refine ⟨4416160151819725875627563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944106767879817250418375 4416160151819725875627563)
            ·
              refine ⟨6624240227729588813441345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416160151819725875627563 6624240227729588813441345)
              ·
                refine ⟨4968180170797191610081009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6624240227729588813441345 4968180170797191610081009)
                ·
                  refine ⟨3726135128097893707560757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4968180170797191610081009 3726135128097893707560757)
                  ·
                    refine ⟨349325168259177535083821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3726135128097893707560757 349325168259177535083821)
                    ·
                      rfl

theorem cell23_2040925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_2040925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040925 prefixEnd_2040925 := by exact prefixLift 2040925
  have htrace : WordTrace (prefixWord ++ tailWord_2040925) baseStart_2040925 baseEnd_2040925 := by
    simpa [prefixWord, tailWord_2040925, baseEnd_2040925] using wordTrace_append hprefix tailTrace_2040925
  have hstable : (prefixWord ++ tailWord_2040925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040925).length < 2 ^ (prefixWord ++ tailWord_2040925).sum := by decide
  have hdescent : baseEnd_2040925 < baseStart_2040925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040951 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 6]
def baseStart_2040951 : Nat := 118140960795 + 2040951 * 2 ^ 59
def prefixEnd_2040951 : Nat := 4983230072969 + 3 ^ 40 * 2040951 * 2
def baseEnd_2040951 : Nat := 116443206141616611502927

theorem tailTrace_2040951 : CollatzResearch.WordTrace tailWord_2040951 prefixEnd_2040951 116443206141616611502927 := by
  unfold tailWord_2040951
  simp only [CollatzResearch.WordTrace]
  refine ⟨74439598428990568525098707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49626398952660379016732471 74439598428990568525098707)
  ·
    refine ⟨111659397643485852787648061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74439598428990568525098707 111659397643485852787648061)
    ·
      refine ⟨41872274116307194795368023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111659397643485852787648061 41872274116307194795368023)
      ·
        refine ⟨62808411174460792193052035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41872274116307194795368023 62808411174460792193052035)
        ·
          refine ⟨94212616761691188289578053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62808411174460792193052035 94212616761691188289578053)
          ·
            refine ⟨17664865642817097804295885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94212616761691188289578053 17664865642817097804295885)
            ·
              refine ⟨6624324616056411676610957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17664865642817097804295885 6624324616056411676610957)
              ·
                refine ⟨2484121731021154378729109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6624324616056411676610957 2484121731021154378729109)
                ·
                  refine ⟨116443206141616611502927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2484121731021154378729109 116443206141616611502927)
                  ·
                    rfl

theorem cell23_2040951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 6].length) (baseStart_2040951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040951 prefixEnd_2040951 := by exact prefixLift 2040951
  have htrace : WordTrace (prefixWord ++ tailWord_2040951) baseStart_2040951 baseEnd_2040951 := by
    simpa [prefixWord, tailWord_2040951, baseEnd_2040951] using wordTrace_append hprefix tailTrace_2040951
  have hstable : (prefixWord ++ tailWord_2040951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040951).length < 2 ^ (prefixWord ++ tailWord_2040951).sum := by decide
  have hdescent : baseEnd_2040951 < baseStart_2040951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2040965 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_2040965 : Nat := 118140960795 + 2040965 * 2 ^ 59
def prefixEnd_2040965 : Nat := 4983230072969 + 3 ^ 40 * 2040965 * 2
def baseEnd_2040965 : Nat := 1047996044003712448751279

theorem tailTrace_2040965 : CollatzResearch.WordTrace tailWord_2040965 prefixEnd_2040965 1047996044003712448751279 := by
  unfold tailWord_2040965
  simp only [CollatzResearch.WordTrace]
  refine ⟨74440109050939848916108349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49626739367293232610738899 74440109050939848916108349)
  ·
    refine ⟨27915040894102443343540631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74440109050939848916108349 27915040894102443343540631)
    ·
      refine ⟨41872561341153665015310947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27915040894102443343540631 41872561341153665015310947)
      ·
        refine ⟨62808842011730497522966421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41872561341153665015310947 62808842011730497522966421)
        ·
          refine ⟨2944164469299867071389051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62808842011730497522966421 2944164469299867071389051)
          ·
            refine ⟨4416246703949800607083577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944164469299867071389051 4416246703949800607083577)
            ·
              refine ⟨3312185027962350455312683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416246703949800607083577 3312185027962350455312683)
              ·
                refine ⟨4968277541943525682969025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312185027962350455312683 4968277541943525682969025)
                ·
                  refine ⟨3726208156457644262226769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4968277541943525682969025 3726208156457644262226769)
                  ·
                    refine ⟨2794656117343233196670077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3726208156457644262226769 2794656117343233196670077)
                    ·
                      refine ⟨1047996044003712448751279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2794656117343233196670077 1047996044003712448751279)
                      ·
                        rfl

theorem cell23_2040965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_2040965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2040965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2040965 prefixEnd_2040965 := by exact prefixLift 2040965
  have htrace : WordTrace (prefixWord ++ tailWord_2040965) baseStart_2040965 baseEnd_2040965 := by
    simpa [prefixWord, tailWord_2040965, baseEnd_2040965] using wordTrace_append hprefix tailTrace_2040965
  have hstable : (prefixWord ++ tailWord_2040965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2040965).length < 2 ^ (prefixWord ++ tailWord_2040965).sum := by decide
  have hdescent : baseEnd_2040965 < baseStart_2040965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2040965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041011 : List Nat := [1, 1, 1, 2, 3, 2, 3, 3, 1, 6]
def baseStart_2041011 : Nat := 118140960795 + 2041011 * 2 ^ 59
def prefixEnd_2041011 : Nat := 4983230072969 + 3 ^ 40 * 2041011 * 2
def baseEnd_2041011 : Nat := 349339888037939756258689

theorem tailTrace_2041011 : CollatzResearch.WordTrace tailWord_2041011 prefixEnd_2041011 349339888037939756258689 := by
  unfold tailWord_2041011
  simp only [CollatzResearch.WordTrace]
  refine ⟨74441786808773198772282887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49627857872515465848188591 74441786808773198772282887)
  ·
    refine ⟨111662680213159798158424331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74441786808773198772282887 111662680213159798158424331)
    ·
      refine ⟨167494020319739697237636497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111662680213159798158424331 167494020319739697237636497)
      ·
        refine ⟨125620515239804772928227373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167494020319739697237636497 125620515239804772928227373)
        ·
          refine ⟨47107693214926789848085265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125620515239804772928227373 47107693214926789848085265)
          ·
            refine ⟨35330769911195092386063949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47107693214926789848085265 35330769911195092386063949)
            ·
              refine ⟨13249038716698159644773981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35330769911195092386063949 13249038716698159644773981)
              ·
                refine ⟨4968389518761809866790243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13249038716698159644773981 4968389518761809866790243)
                ·
                  refine ⟨7452584278142714800185365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968389518761809866790243 7452584278142714800185365)
                  ·
                    refine ⟨349339888037939756258689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7452584278142714800185365 349339888037939756258689)
                    ·
                      rfl

theorem cell23_2041011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 6].length) (baseStart_2041011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041011 prefixEnd_2041011 := by exact prefixLift 2041011
  have htrace : WordTrace (prefixWord ++ tailWord_2041011) baseStart_2041011 baseEnd_2041011 := by
    simpa [prefixWord, tailWord_2041011, baseEnd_2041011] using wordTrace_append hprefix tailTrace_2041011
  have hstable : (prefixWord ++ tailWord_2041011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041011).length < 2 ^ (prefixWord ++ tailWord_2041011).sum := by decide
  have hdescent : baseEnd_2041011 < baseStart_2041011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041018 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_2041018 : Nat := 118140960795 + 2041018 * 2 ^ 59
def prefixEnd_2041018 : Nat := 4983230072969 + 3 ^ 40 * 2041018 * 2
def baseEnd_2041018 : Nat := 1048023258478400741388535

theorem tailTrace_2041018 : CollatzResearch.WordTrace tailWord_2041018 prefixEnd_2041018 1048023258478400741388535 := by
  unfold tailWord_2041018
  simp only [CollatzResearch.WordTrace]
  refine ⟨18610510529936959741946927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 49628028079831892645191805 18610510529936959741946927)
  ·
    refine ⟨27915765794905439612920391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18610510529936959741946927 27915765794905439612920391)
    ·
      refine ⟨41873648692358159419380587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27915765794905439612920391 41873648692358159419380587)
      ·
        refine ⟨62810473038537239129070881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41873648692358159419380587 62810473038537239129070881)
        ·
          refine ⟨47107854778902929346803161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62810473038537239129070881 47107854778902929346803161)
          ·
            refine ⟨35330891084177197010102371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47107854778902929346803161 35330891084177197010102371)
            ·
              refine ⟨52996336626265795515153557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35330891084177197010102371 52996336626265795515153557)
              ·
                refine ⟨2484203279356209164772823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52996336626265795515153557 2484203279356209164772823)
                ·
                  refine ⟨3726304919034313747159235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484203279356209164772823 3726304919034313747159235)
                  ·
                    refine ⟨5589457378551470620738853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3726304919034313747159235 5589457378551470620738853)
                    ·
                      refine ⟨1048023258478400741388535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5589457378551470620738853 1048023258478400741388535)
                      ·
                        rfl

theorem cell23_2041018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_2041018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041018 prefixEnd_2041018 := by exact prefixLift 2041018
  have htrace : WordTrace (prefixWord ++ tailWord_2041018) baseStart_2041018 baseEnd_2041018 := by
    simpa [prefixWord, tailWord_2041018, baseEnd_2041018] using wordTrace_append hprefix tailTrace_2041018
  have hstable : (prefixWord ++ tailWord_2041018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041018).length < 2 ^ (prefixWord ++ tailWord_2041018).sum := by decide
  have hdescent : baseEnd_2041018 < baseStart_2041018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041022 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_2041022 : Nat := 118140960795 + 2041022 * 2 ^ 59
def prefixEnd_2041022 : Nat := 4983230072969 + 3 ^ 40 * 2041022 * 2
def baseEnd_2041022 : Nat := 1048025312401018725738517

theorem tailTrace_2041022 : CollatzResearch.WordTrace tailWord_2041022 prefixEnd_2041022 1048025312401018725738517 := by
  unfold tailWord_2041022
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305273501466668456366665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49628125341155565100622213 9305273501466668456366665)
  ·
    refine ⟨6978955126100001342274999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9305273501466668456366665 6978955126100001342274999)
    ·
      refine ⟨10468432689150002013412499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6978955126100001342274999 10468432689150002013412499)
      ·
        refine ⟨15702649033725003020118749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10468432689150002013412499 15702649033725003020118749)
        ·
          refine ⟨5888493387646876132544531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15702649033725003020118749 5888493387646876132544531)
          ·
            refine ⟨8832740081470314198816797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888493387646876132544531 8832740081470314198816797)
            ·
              refine ⟨3312277530551367824556299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8832740081470314198816797 3312277530551367824556299)
              ·
                refine ⟨4968416295827051736834449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312277530551367824556299 4968416295827051736834449)
                ·
                  refine ⟨3726312221870288802625837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4968416295827051736834449 3726312221870288802625837)
                  ·
                    refine ⟨1397367083201358300984689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3726312221870288802625837 1397367083201358300984689)
                    ·
                      refine ⟨1048025312401018725738517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397367083201358300984689 1048025312401018725738517)
                      ·
                        rfl

theorem cell23_2041022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_2041022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041022 prefixEnd_2041022 := by exact prefixLift 2041022
  have htrace : WordTrace (prefixWord ++ tailWord_2041022) baseStart_2041022 baseEnd_2041022 := by
    simpa [prefixWord, tailWord_2041022, baseEnd_2041022] using wordTrace_append hprefix tailTrace_2041022
  have hstable : (prefixWord ++ tailWord_2041022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041022).length < 2 ^ (prefixWord ++ tailWord_2041022).sum := by decide
  have hdescent : baseEnd_2041022 < baseStart_2041022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041045 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 4, 4]
def baseStart_2041045 : Nat := 118140960795 + 2041045 * 2 ^ 59
def prefixEnd_2041045 : Nat := 4983230072969 + 3 ^ 40 * 2041045 * 2
def baseEnd_2041045 : Nat := 349345707485357378583637

theorem tailTrace_2041045 : CollatzResearch.WordTrace tailWord_2041045 prefixEnd_2041045 349345707485357378583637 := by
  unfold tailWord_2041045
  simp only [CollatzResearch.WordTrace]
  refine ⟨74443026890650022579020589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49628684593766681719347059 74443026890650022579020589)
  ·
    refine ⟨27916135083993758467132721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74443026890650022579020589 27916135083993758467132721)
    ·
      refine ⟨20937101312995318850349541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27916135083993758467132721 20937101312995318850349541)
      ·
        refine ⟨3925706496186622284440539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20937101312995318850349541 3925706496186622284440539)
        ·
          refine ⟨5888559744279933426660809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925706496186622284440539 5888559744279933426660809)
          ·
            refine ⟨4416419808209950069995607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5888559744279933426660809 4416419808209950069995607)
            ·
              refine ⟨6624629712314925104993411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416419808209950069995607 6624629712314925104993411)
              ·
                refine ⟨9936944568472387657490117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624629712314925104993411 9936944568472387657490117)
                ·
                  refine ⟨1863177106588572685779397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9936944568472387657490117 1863177106588572685779397)
                  ·
                    refine ⟨349345707485357378583637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1863177106588572685779397 349345707485357378583637)
                    ·
                      rfl

theorem cell23_2041045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_2041045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041045 prefixEnd_2041045 := by exact prefixLift 2041045
  have htrace : WordTrace (prefixWord ++ tailWord_2041045) baseStart_2041045 baseEnd_2041045 := by
    simpa [prefixWord, tailWord_2041045, baseEnd_2041045] using wordTrace_append hprefix tailTrace_2041045
  have hstable : (prefixWord ++ tailWord_2041045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041045).length < 2 ^ (prefixWord ++ tailWord_2041045).sum := by decide
  have hdescent : baseEnd_2041045 < baseStart_2041045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041081 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 5]
def baseStart_2041081 : Nat := 118140960795 + 2041081 * 2 ^ 59
def prefixEnd_2041081 : Nat := 4983230072969 + 3 ^ 40 * 2041081 * 2
def baseEnd_2041081 : Nat := 1048055607759633994900745

theorem tailTrace_2041081 : CollatzResearch.WordTrace tailWord_2041081 prefixEnd_2041081 1048055607759633994900745 := by
  unfold tailWord_2041081
  simp only [CollatzResearch.WordTrace]
  refine ⟨74444339918519600727331097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49629559945679733818220731 74444339918519600727331097)
  ·
    refine ⟨55833254938889700545498323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74444339918519600727331097 55833254938889700545498323)
    ·
      refine ⟨83749882408334550818247485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55833254938889700545498323 83749882408334550818247485)
      ·
        refine ⟨31406205903125456556842807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83749882408334550818247485 31406205903125456556842807)
        ·
          refine ⟨47109308854688184835264211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31406205903125456556842807 47109308854688184835264211)
          ·
            refine ⟨70663963282032277252896317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47109308854688184835264211 70663963282032277252896317)
            ·
              refine ⟨26498986230762103969836119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70663963282032277252896317 26498986230762103969836119)
              ·
                refine ⟨39748479346143155954754179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26498986230762103969836119 39748479346143155954754179)
                ·
                  refine ⟨59622719019214733932131269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39748479346143155954754179 59622719019214733932131269)
                  ·
                    refine ⟨11179259816102762612274613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59622719019214733932131269 11179259816102762612274613)
                    ·
                      refine ⟨1048055607759633994900745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 11179259816102762612274613 1048055607759633994900745)
                      ·
                        rfl

theorem cell23_2041081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_2041081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041081 prefixEnd_2041081 := by exact prefixLift 2041081
  have htrace : WordTrace (prefixWord ++ tailWord_2041081) baseStart_2041081 baseEnd_2041081 := by
    simpa [prefixWord, tailWord_2041081, baseEnd_2041081] using wordTrace_append hprefix tailTrace_2041081
  have hstable : (prefixWord ++ tailWord_2041081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041081).length < 2 ^ (prefixWord ++ tailWord_2041081).sum := by decide
  have hdescent : baseEnd_2041081 < baseStart_2041081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041086 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_2041086 : Nat := 118140960795 + 2041086 * 2 ^ 59
def prefixEnd_2041086 : Nat := 4983230072969 + 3 ^ 40 * 2041086 * 2
def baseEnd_2041086 : Nat := 1048058175162906475338223

theorem tailTrace_2041086 : CollatzResearch.WordTrace tailWord_2041086 prefixEnd_2041086 1048058175162906475338223 := by
  unfold tailWord_2041086
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305565285437685822657889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 49629681522334324387508741 9305565285437685822657889)
  ·
    refine ⟨6979173964078264366993417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9305565285437685822657889 6979173964078264366993417)
    ·
      refine ⟨5234380473058698275245063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6979173964078264366993417 5234380473058698275245063)
      ·
        refine ⟨7851570709588047412867595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234380473058698275245063 7851570709588047412867595)
        ·
          refine ⟨11777356064382071119301393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7851570709588047412867595 11777356064382071119301393)
          ·
            refine ⟨8833017048286553339476045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11777356064382071119301393 8833017048286553339476045)
            ·
              refine ⟨3312381393107457502303517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8833017048286553339476045 3312381393107457502303517)
              ·
                refine ⟨1242143022415296563363819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3312381393107457502303517 1242143022415296563363819)
                ·
                  refine ⟨1863214533622944845045729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242143022415296563363819 1863214533622944845045729)
                  ·
                    refine ⟨1397410900217208633784297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863214533622944845045729 1397410900217208633784297)
                    ·
                      refine ⟨1048058175162906475338223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397410900217208633784297 1048058175162906475338223)
                      ·
                        rfl

theorem cell23_2041086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_2041086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041086 prefixEnd_2041086 := by exact prefixLift 2041086
  have htrace : WordTrace (prefixWord ++ tailWord_2041086) baseStart_2041086 baseEnd_2041086 := by
    simpa [prefixWord, tailWord_2041086, baseEnd_2041086] using wordTrace_append hprefix tailTrace_2041086
  have hstable : (prefixWord ++ tailWord_2041086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041086).length < 2 ^ (prefixWord ++ tailWord_2041086).sum := by decide
  have hdescent : baseEnd_2041086 < baseStart_2041086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041159 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_2041159 : Nat := 118140960795 + 2041159 * 2 ^ 59
def prefixEnd_2041159 : Nat := 4983230072969 + 3 ^ 40 * 2041159 * 2
def baseEnd_2041159 : Nat := 1048095659250684689725387

theorem tailTrace_2041159 : CollatzResearch.WordTrace tailWord_2041159 prefixEnd_2041159 1048095659250684689725387 := by
  unfold tailWord_2041159
  simp only [CollatzResearch.WordTrace]
  refine ⟨74447184812237020048670531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49631456541491346699113687 74447184812237020048670531)
  ·
    refine ⟨111670777218355530073005797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74447184812237020048670531 111670777218355530073005797)
    ·
      refine ⟨20938270728441661888688587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111670777218355530073005797 20938270728441661888688587)
      ·
        refine ⟨31407406092662492833032881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20938270728441661888688587 31407406092662492833032881)
        ·
          refine ⟨23555554569496869624774661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31407406092662492833032881 23555554569496869624774661)
          ·
            refine ⟨4416666481780663054645249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23555554569496869624774661 4416666481780663054645249)
            ·
              refine ⟨3312499861335497290983937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416666481780663054645249 3312499861335497290983937)
              ·
                refine ⟨2484374896001622968237953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312499861335497290983937 2484374896001622968237953)
                ·
                  refine ⟨1863281172001217226178465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2484374896001622968237953 1863281172001217226178465)
                  ·
                    refine ⟨1397460879000912919633849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1863281172001217226178465 1397460879000912919633849)
                    ·
                      refine ⟨1048095659250684689725387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1397460879000912919633849 1048095659250684689725387)
                      ·
                        rfl

theorem cell23_2041159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_2041159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041159 prefixEnd_2041159 := by exact prefixLift 2041159
  have htrace : WordTrace (prefixWord ++ tailWord_2041159) baseStart_2041159 baseEnd_2041159 := by
    simpa [prefixWord, tailWord_2041159, baseEnd_2041159] using wordTrace_append hprefix tailTrace_2041159
  have hstable : (prefixWord ++ tailWord_2041159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041159).length < 2 ^ (prefixWord ++ tailWord_2041159).sum := by decide
  have hdescent : baseEnd_2041159 < baseStart_2041159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2041175 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 3]
def baseStart_2041175 : Nat := 118140960795 + 2041175 * 2 ^ 59
def prefixEnd_2041175 : Nat := 4983230072969 + 3 ^ 40 * 2041175 * 2
def baseEnd_2041175 : Nat := 1048103874941156627125313

theorem tailTrace_2041175 : CollatzResearch.WordTrace tailWord_2041175 prefixEnd_2041175 1048103874941156627125313 := by
  unfold tailWord_2041175
  simp only [CollatzResearch.WordTrace]
  refine ⟨74447768380179054781252979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 49631845586786036520835319 74447768380179054781252979)
  ·
    refine ⟨111671652570268582171879469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74447768380179054781252979 111671652570268582171879469)
    ·
      refine ⟨41876869713850718314454801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111671652570268582171879469 41876869713850718314454801)
      ·
        refine ⟨31407652285388038735841101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41876869713850718314454801 31407652285388038735841101)
        ·
          refine ⟨11777869607020514525940413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31407652285388038735841101 11777869607020514525940413)
          ·
            refine ⟨4416701102632692947227655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11777869607020514525940413 4416701102632692947227655)
            ·
              refine ⟨6625051653949039420841483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416701102632692947227655 6625051653949039420841483)
              ·
                refine ⟨9937577480923559131262225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625051653949039420841483 9937577480923559131262225)
                ·
                  refine ⟨7453183110692669348446669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9937577480923559131262225 7453183110692669348446669)
                  ·
                    refine ⟨2794943666509751005667501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7453183110692669348446669 2794943666509751005667501)
                    ·
                      refine ⟨1048103874941156627125313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2794943666509751005667501 1048103874941156627125313)
                      ·
                        rfl

theorem cell23_2041175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_2041175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2041175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2041175 prefixEnd_2041175 := by exact prefixLift 2041175
  have htrace : WordTrace (prefixWord ++ tailWord_2041175) baseStart_2041175 baseEnd_2041175 := by
    simpa [prefixWord, tailWord_2041175, baseEnd_2041175] using wordTrace_append hprefix tailTrace_2041175
  have hstable : (prefixWord ++ tailWord_2041175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2041175).length < 2 ^ (prefixWord ++ tailWord_2041175).sum := by decide
  have hdescent : baseEnd_2041175 < baseStart_2041175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2041175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
