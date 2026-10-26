import V185TrunkScan23Chunk0632

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3743243 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 3, 4]
def baseStart_3743243 : Nat := 118140960795 + 3743243 * 2 ^ 59
def prefixEnd_3743243 : Nat := 4983230072969 + 3 ^ 40 * 3743243 * 2
def baseEnd_3743243 : Nat := 640694288526001092749215

theorem tailTrace_3743243 : CollatzResearch.WordTrace tailWord_3743243 prefixEnd_3743243 640694288526001092749215 := by
  unfold tailWord_3743243
  simp only [CollatzResearch.WordTrace]
  refine ⟨136527288377877380852634383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91018192251918253901756255 136527288377877380852634383)
  ·
    refine ⟨204790932566816071278951575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136527288377877380852634383 204790932566816071278951575)
    ·
      refine ⟨307186398850224106918427363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204790932566816071278951575 307186398850224106918427363)
      ·
        refine ⟨460779598275336160377641045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307186398850224106918427363 460779598275336160377641045)
        ·
          refine ⟨5399760917289095629425481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 460779598275336160377641045 5399760917289095629425481)
          ·
            refine ⟨4049820687966821722069111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5399760917289095629425481 4049820687966821722069111)
            ·
              refine ⟨6074731031950232583103667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049820687966821722069111 6074731031950232583103667)
              ·
                refine ⟨9112096547925348874655501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074731031950232583103667 9112096547925348874655501)
                ·
                  refine ⟨3417036205472005827995813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9112096547925348874655501 3417036205472005827995813)
                  ·
                    refine ⟨640694288526001092749215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417036205472005827995813 640694288526001092749215)
                    ·
                      rfl

theorem cell23_3743243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 3, 4].length) (baseStart_3743243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743243 prefixEnd_3743243 := by exact prefixLift 3743243
  have htrace : WordTrace (prefixWord ++ tailWord_3743243) baseStart_3743243 baseEnd_3743243 := by
    simpa [prefixWord, tailWord_3743243, baseEnd_3743243] using wordTrace_append hprefix tailTrace_3743243
  have hstable : (prefixWord ++ tailWord_3743243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743243).length < 2 ^ (prefixWord ++ tailWord_3743243).sum := by decide
  have hdescent : baseEnd_3743243 < baseStart_3743243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743256 : List Nat := [2, 1, 2, 3, 4, 1, 1, 3, 6]
def baseStart_3743256 : Nat := 118140960795 + 3743256 * 2 ^ 59
def prefixEnd_3743256 : Nat := 4983230072969 + 3 ^ 40 * 3743256 * 2
def baseEnd_3743256 : Nat := 213565504536279080820565

theorem tailTrace_3743256 : CollatzResearch.WordTrace tailWord_3743256 prefixEnd_3743256 213565504536279080820565 := by
  unfold tailWord_3743256
  simp only [CollatzResearch.WordTrace]
  refine ⟨68263881263415142036428811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91018508351220189381905081 68263881263415142036428811)
  ·
    refine ⟨102395821895122713054643217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68263881263415142036428811 102395821895122713054643217)
    ·
      refine ⟨76796866421342034790982413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102395821895122713054643217 76796866421342034790982413)
      ·
        refine ⟨28798824908003263046618405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76796866421342034790982413 28798824908003263046618405)
        ·
          refine ⟨5399779670250611821240951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28798824908003263046618405 5399779670250611821240951)
          ·
            refine ⟨8099669505375917731861427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399779670250611821240951 8099669505375917731861427)
            ·
              refine ⟨12149504258063876597792141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8099669505375917731861427 12149504258063876597792141)
              ·
                refine ⟨4556064096773953724172053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12149504258063876597792141 4556064096773953724172053)
                ·
                  refine ⟨213565504536279080820565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4556064096773953724172053 213565504536279080820565)
                  ·
                    rfl

theorem cell23_3743256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 6].length) (baseStart_3743256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743256 prefixEnd_3743256 := by exact prefixLift 3743256
  have htrace : WordTrace (prefixWord ++ tailWord_3743256) baseStart_3743256 baseEnd_3743256 := by
    simpa [prefixWord, tailWord_3743256, baseEnd_3743256] using wordTrace_append hprefix tailTrace_3743256
  have hstable : (prefixWord ++ tailWord_3743256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743256).length < 2 ^ (prefixWord ++ tailWord_3743256).sum := by decide
  have hdescent : baseEnd_3743256 < baseStart_3743256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743316 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_3743316 : Nat := 118140960795 + 3743316 * 2 ^ 59
def prefixEnd_3743316 : Nat := 4983230072969 + 3 ^ 40 * 3743316 * 2
def baseEnd_3743316 : Nat := 640706783221927164211603

theorem tailTrace_3743316 : CollatzResearch.WordTrace tailWord_3743316 prefixEnd_3743316 640706783221927164211603 := by
  unfold tailWord_3743316
  simp only [CollatzResearch.WordTrace]
  refine ⟨68264975453306457160020901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91019967271075276213361201 68264975453306457160020901)
  ·
    refine ⟨12799682897494960717503919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68264975453306457160020901 12799682897494960717503919)
    ·
      refine ⟨19199524346242441076255879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12799682897494960717503919 19199524346242441076255879)
      ·
        refine ⟨28799286519363661614383819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19199524346242441076255879 28799286519363661614383819)
        ·
          refine ⟨43198929779045492421575729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28799286519363661614383819 43198929779045492421575729)
          ·
            refine ⟨32399197334284119316181797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43198929779045492421575729 32399197334284119316181797)
            ·
              refine ⟨6074849500178272371784087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32399197334284119316181797 6074849500178272371784087)
              ·
                refine ⟨9112274250267408557676131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6074849500178272371784087 9112274250267408557676131)
                ·
                  refine ⟨13668411375401112836514197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9112274250267408557676131 13668411375401112836514197)
                  ·
                    refine ⟨640706783221927164211603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13668411375401112836514197 640706783221927164211603)
                    ·
                      rfl

theorem cell23_3743316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_3743316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743316 prefixEnd_3743316 := by exact prefixLift 3743316
  have htrace : WordTrace (prefixWord ++ tailWord_3743316) baseStart_3743316 baseEnd_3743316 := by
    simpa [prefixWord, tailWord_3743316, baseEnd_3743316] using wordTrace_append hprefix tailTrace_3743316
  have hstable : (prefixWord ++ tailWord_3743316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743316).length < 2 ^ (prefixWord ++ tailWord_3743316).sum := by decide
  have hdescent : baseEnd_3743316 < baseStart_3743316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743339 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 3]
def baseStart_3743339 : Nat := 118140960795 + 3743339 * 2 ^ 59
def prefixEnd_3743339 : Nat := 4983230072969 + 3 ^ 40 * 3743339 * 2
def baseEnd_3743339 : Nat := 1922132159720834902647203

theorem tailTrace_3743339 : CollatzResearch.WordTrace tailWord_3743339 prefixEnd_3743339 1922132159720834902647203 := by
  unfold tailWord_3743339
  simp only [CollatzResearch.WordTrace]
  refine ⟨136530789785529589248129071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91020526523686392832086047 136530789785529589248129071)
  ·
    refine ⟨204796184678294383872193607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136530789785529589248129071 204796184678294383872193607)
    ·
      refine ⟨307194277017441575808290411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204796184678294383872193607 307194277017441575808290411)
      ·
        refine ⟨460791415526162363712435617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307194277017441575808290411 460791415526162363712435617)
        ·
          refine ⟨345593561644621772784326713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 460791415526162363712435617 345593561644621772784326713)
          ·
            refine ⟨259195171233466329588245035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345593561644621772784326713 259195171233466329588245035)
            ·
              refine ⟨388792756850199494382367553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259195171233466329588245035 388792756850199494382367553)
              ·
                refine ⟨291594567637649620786775665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388792756850199494382367553 291594567637649620786775665)
                ·
                  refine ⟨218695925728237215590081749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 291594567637649620786775665 218695925728237215590081749)
                  ·
                    refine ⟨5125685759255559740392541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 218695925728237215590081749 5125685759255559740392541)
                    ·
                      refine ⟨1922132159720834902647203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5125685759255559740392541 1922132159720834902647203)
                      ·
                        rfl

theorem cell23_3743339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 7, 3].length) (baseStart_3743339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743339 prefixEnd_3743339 := by exact prefixLift 3743339
  have htrace : WordTrace (prefixWord ++ tailWord_3743339) baseStart_3743339 baseEnd_3743339 := by
    simpa [prefixWord, tailWord_3743339, baseEnd_3743339] using wordTrace_append hprefix tailTrace_3743339
  have hstable : (prefixWord ++ tailWord_3743339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743339).length < 2 ^ (prefixWord ++ tailWord_3743339).sum := by decide
  have hdescent : baseEnd_3743339 < baseStart_3743339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743350 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_3743350 : Nat := 118140960795 + 3743350 * 2 ^ 59
def prefixEnd_3743350 : Nat := 4983230072969 + 3 ^ 40 * 3743350 * 2
def baseEnd_3743350 : Nat := 640712602669344786536551

theorem tailTrace_3743350 : CollatzResearch.WordTrace tailWord_3743350 prefixEnd_3743350 640712602669344786536551 := by
  unfold tailWord_3743350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533199436780608632923719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91020793992326492084519669 8533199436780608632923719)
  ·
    refine ⟨12799799155170912949385579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8533199436780608632923719 12799799155170912949385579)
    ·
      refine ⟨19199698732756369424078369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12799799155170912949385579 19199698732756369424078369)
      ·
        refine ⟨14399774049567277068058777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19199698732756369424078369 14399774049567277068058777)
        ·
          refine ⟨10799830537175457801044083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14399774049567277068058777 10799830537175457801044083)
          ·
            refine ⟨16199745805763186701566125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799830537175457801044083 16199745805763186701566125)
            ·
              refine ⟨6074904677161195013087297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16199745805763186701566125 6074904677161195013087297)
              ·
                refine ⟨4556178507870896259815473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6074904677161195013087297 4556178507870896259815473)
                ·
                  refine ⟨3417133880903172194861605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4556178507870896259815473 3417133880903172194861605)
                  ·
                    refine ⟨640712602669344786536551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417133880903172194861605 640712602669344786536551)
                    ·
                      rfl

theorem cell23_3743350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_3743350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743350 prefixEnd_3743350 := by exact prefixLift 3743350
  have htrace : WordTrace (prefixWord ++ tailWord_3743350) baseStart_3743350 baseEnd_3743350 := by
    simpa [prefixWord, tailWord_3743350, baseEnd_3743350] using wordTrace_append hprefix tailTrace_3743350
  have hstable : (prefixWord ++ tailWord_3743350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743350).length < 2 ^ (prefixWord ++ tailWord_3743350).sum := by decide
  have hdescent : baseEnd_3743350 < baseStart_3743350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743357 : List Nat := [1, 4, 1, 1, 4, 1, 2, 4, 1, 2, 2]
def baseStart_3743357 : Nat := 118140960795 + 3743357 * 2 ^ 59
def prefixEnd_3743357 : Nat := 4983230072969 + 3 ^ 40 * 3743357 * 2
def baseEnd_3743357 : Nat := 1922141402372615832222121

theorem tailTrace_3743357 : CollatzResearch.WordTrace tailWord_3743357 prefixEnd_3743357 1922141402372615832222121 := by
  unfold tailWord_3743357
  simp only [CollatzResearch.WordTrace]
  refine ⟨136531446299464378322284325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91020964199642918881522883 136531446299464378322284325)
  ·
    refine ⟨25599646181149570935428311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136531446299464378322284325 25599646181149570935428311)
    ·
      refine ⟨38399469271724356403142467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25599646181149570935428311 38399469271724356403142467)
      ·
        refine ⟨57599203907586534604713701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38399469271724356403142467 57599203907586534604713701)
        ·
          refine ⟨10799850732672475238383819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57599203907586534604713701 10799850732672475238383819)
          ·
            refine ⟨16199776099008712857575729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10799850732672475238383819 16199776099008712857575729)
            ·
              refine ⟨12149832074256534643181797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16199776099008712857575729 12149832074256534643181797)
              ·
                refine ⟨2278093513923100245596587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12149832074256534643181797 2278093513923100245596587)
                ·
                  refine ⟨3417140270884650368394881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278093513923100245596587 3417140270884650368394881)
                  ·
                    refine ⟨2562855203163487776296161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3417140270884650368394881 2562855203163487776296161)
                    ·
                      refine ⟨1922141402372615832222121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562855203163487776296161 1922141402372615832222121)
                      ·
                        rfl

theorem cell23_3743357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_3743357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743357 prefixEnd_3743357 := by exact prefixLift 3743357
  have htrace : WordTrace (prefixWord ++ tailWord_3743357) baseStart_3743357 baseEnd_3743357 := by
    simpa [prefixWord, tailWord_3743357, baseEnd_3743357] using wordTrace_append hprefix tailTrace_3743357
  have hstable : (prefixWord ++ tailWord_3743357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743357).length < 2 ^ (prefixWord ++ tailWord_3743357).sum := by decide
  have hdescent : baseEnd_3743357 < baseStart_3743357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743380 : List Nat := [2, 4, 2, 2, 2, 2, 2, 7]
def baseStart_3743380 : Nat := 118140960795 + 3743380 * 2 ^ 59
def prefixEnd_3743380 : Nat := 4983230072969 + 3 ^ 40 * 3743380 * 2
def baseEnd_3743380 : Nat := 71190859719543305267945

theorem tailTrace_3743380 : CollatzResearch.WordTrace tailWord_3743380 prefixEnd_3743380 71190859719543305267945 := by
  unfold tailWord_3743380
  simp only [CollatzResearch.WordTrace]
  refine ⟨68266142589190526625185797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91021523452254035500247729 68266142589190526625185797)
  ·
    refine ⟨12799901735473223742222337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68266142589190526625185797 12799901735473223742222337)
    ·
      refine ⟨9599926301604917806666753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12799901735473223742222337 9599926301604917806666753)
      ·
        refine ⟨7199944726203688355000065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9599926301604917806666753 7199944726203688355000065)
        ·
          refine ⟨5399958544652766266250049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7199944726203688355000065 5399958544652766266250049)
          ·
            refine ⟨4049968908489574699687537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5399958544652766266250049 4049968908489574699687537)
            ·
              refine ⟨3037476681367181024765653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4049968908489574699687537 3037476681367181024765653)
              ·
                refine ⟨71190859719543305267945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3037476681367181024765653 71190859719543305267945)
                ·
                  rfl

theorem cell23_3743380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 2, 7].length) (baseStart_3743380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743380 prefixEnd_3743380 := by exact prefixLift 3743380
  have htrace : WordTrace (prefixWord ++ tailWord_3743380) baseStart_3743380 baseEnd_3743380 := by
    simpa [prefixWord, tailWord_3743380, baseEnd_3743380] using wordTrace_append hprefix tailTrace_3743380
  have hstable : (prefixWord ++ tailWord_3743380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743380).length < 2 ^ (prefixWord ++ tailWord_3743380).sum := by decide
  have hdescent : baseEnd_3743380 < baseStart_3743380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743390 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3743390 : Nat := 118140960795 + 3743390 * 2 ^ 59
def prefixEnd_3743390 : Nat := 4983230072969 + 3 ^ 40 * 3743390 * 2
def baseEnd_3743390 : Nat := 1922158347234214203109469

theorem tailTrace_3743390 : CollatzResearch.WordTrace tailWord_3743390 prefixEnd_3743390 1922158347234214203109469 := by
  unfold tailWord_3743390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17066581238543103119779453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91021766605563216638823749 17066581238543103119779453)
  ·
    refine ⟨6399967964453663669917295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17066581238543103119779453 6399967964453663669917295)
    ·
      refine ⟨9599951946680495504875943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6399967964453663669917295 9599951946680495504875943)
      ·
        refine ⟨14399927920020743257313915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9599951946680495504875943 14399927920020743257313915)
        ·
          refine ⟨21599891880031114885970873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14399927920020743257313915 21599891880031114885970873)
          ·
            refine ⟨16199918910023336164478155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21599891880031114885970873 16199918910023336164478155)
            ·
              refine ⟨24299878365035004246717233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16199918910023336164478155 24299878365035004246717233)
              ·
                refine ⟨18224908773776253185037925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24299878365035004246717233 18224908773776253185037925)
                ·
                  refine ⟨3417170395083047472194611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18224908773776253185037925 3417170395083047472194611)
                  ·
                    refine ⟨5125755592624571208291917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417170395083047472194611 5125755592624571208291917)
                    ·
                      refine ⟨1922158347234214203109469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5125755592624571208291917 1922158347234214203109469)
                      ·
                        rfl

theorem cell23_3743390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3743390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743390 prefixEnd_3743390 := by exact prefixLift 3743390
  have htrace : WordTrace (prefixWord ++ tailWord_3743390) baseStart_3743390 baseEnd_3743390 := by
    simpa [prefixWord, tailWord_3743390, baseEnd_3743390] using wordTrace_append hprefix tailTrace_3743390
  have hstable : (prefixWord ++ tailWord_3743390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743390).length < 2 ^ (prefixWord ++ tailWord_3743390).sum := by decide
  have hdescent : baseEnd_3743390 < baseStart_3743390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743391 : List Nat := [1, 1, 2, 7, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3743391 : Nat := 118140960795 + 3743391 * 2 ^ 59
def prefixEnd_3743391 : Nat := 4983230072969 + 3 ^ 40 * 3743391 * 2
def baseEnd_3743391 : Nat := 1922158860714868699196965

theorem tailTrace_3743391 : CollatzResearch.WordTrace tailWord_3743391 prefixEnd_3743391 1922158860714868699196965 := by
  unfold tailWord_3743391
  simp only [CollatzResearch.WordTrace]
  refine ⟨136532686381341202129022027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91021790920894134752681351 136532686381341202129022027)
  ·
    refine ⟨204799029572011803193533041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136532686381341202129022027 204799029572011803193533041)
    ·
      refine ⟨153599272179008852395149781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204799029572011803193533041 153599272179008852395149781)
      ·
        refine ⟨3599982941695519978011323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 153599272179008852395149781 3599982941695519978011323)
        ·
          refine ⟨5399974412543279967016985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599982941695519978011323 5399974412543279967016985)
          ·
            refine ⟨4049980809407459975262739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5399974412543279967016985 4049980809407459975262739)
            ·
              refine ⟨6074971214111189962894109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049980809407459975262739 6074971214111189962894109)
              ·
                refine ⟨2278114205291696236085291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6074971214111189962894109 2278114205291696236085291)
                ·
                  refine ⟨3417171307937544354127937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278114205291696236085291 3417171307937544354127937)
                  ·
                    refine ⟨2562878480953158265595953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3417171307937544354127937 2562878480953158265595953)
                    ·
                      refine ⟨1922158860714868699196965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562878480953158265595953 1922158860714868699196965)
                      ·
                        rfl

theorem cell23_3743391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3743391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743391 prefixEnd_3743391 := by exact prefixLift 3743391
  have htrace : WordTrace (prefixWord ++ tailWord_3743391) baseStart_3743391 baseEnd_3743391 := by
    simpa [prefixWord, tailWord_3743391, baseEnd_3743391] using wordTrace_append hprefix tailTrace_3743391
  have hstable : (prefixWord ++ tailWord_3743391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743391).length < 2 ^ (prefixWord ++ tailWord_3743391).sum := by decide
  have hdescent : baseEnd_3743391 < baseStart_3743391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743429 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_3743429 : Nat := 118140960795 + 3743429 * 2 ^ 59
def prefixEnd_3743429 : Nat := 4983230072969 + 3 ^ 40 * 3743429 * 2
def baseEnd_3743429 : Nat := 1922178372979739550521789

theorem tailTrace_3743429 : CollatzResearch.WordTrace tailWord_3743429 prefixEnd_3743429 1922178372979739550521789 := by
  unfold tailWord_3743429
  simp only [CollatzResearch.WordTrace]
  refine ⟨136534072355203534618905341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91022714903469023079270227 136534072355203534618905341)
  ·
    refine ⟨51200277133201325482089503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136534072355203534618905341 51200277133201325482089503)
    ·
      refine ⟨76800415699801988223134255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51200277133201325482089503 76800415699801988223134255)
      ·
        refine ⟨115200623549702982334701383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76800415699801988223134255 115200623549702982334701383)
        ·
          refine ⟨172800935324554473502052075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115200623549702982334701383 172800935324554473502052075)
          ·
            refine ⟨259201402986831710253078113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172800935324554473502052075 259201402986831710253078113)
            ·
              refine ⟨194401052240123782689808585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259201402986831710253078113 194401052240123782689808585)
              ·
                refine ⟨145800789180092837017356439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194401052240123782689808585 145800789180092837017356439)
                ·
                  refine ⟨218701183770139255526034659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145800789180092837017356439 218701183770139255526034659)
                  ·
                    refine ⟨328051775655208883289051989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218701183770139255526034659 328051775655208883289051989)
                    ·
                      refine ⟨1922178372979739550521789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 328051775655208883289051989 1922178372979739550521789)
                      ·
                        rfl

theorem cell23_3743429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_3743429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743429 prefixEnd_3743429 := by exact prefixLift 3743429
  have htrace : WordTrace (prefixWord ++ tailWord_3743429) baseStart_3743429 baseEnd_3743429 := by
    simpa [prefixWord, tailWord_3743429, baseEnd_3743429] using wordTrace_append hprefix tailTrace_3743429
  have hstable : (prefixWord ++ tailWord_3743429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743429).length < 2 ^ (prefixWord ++ tailWord_3743429).sum := by decide
  have hdescent : baseEnd_3743429 < baseStart_3743429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743434 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_3743434 : Nat := 118140960795 + 3743434 * 2 ^ 59
def prefixEnd_3743434 : Nat := 4983230072969 + 3 ^ 40 * 3743434 * 2
def baseEnd_3743434 : Nat := 1922180940383012030959267

theorem tailTrace_3743434 : CollatzResearch.WordTrace tailWord_3743434 prefixEnd_3743434 1922180940383012030959267 := by
  unfold tailWord_3743434
  simp only [CollatzResearch.WordTrace]
  refine ⟨34133563680046355118209339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91022836480123613648558237 34133563680046355118209339)
  ·
    refine ⟨51200345520069532677314009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34133563680046355118209339 51200345520069532677314009)
    ·
      refine ⟨38400259140052149507985507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51200345520069532677314009 38400259140052149507985507)
      ·
        refine ⟨57600388710078224261978261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38400259140052149507985507 57600388710078224261978261)
        ·
          refine ⟨2700018220784916762280231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57600388710078224261978261 2700018220784916762280231)
          ·
            refine ⟨4050027331177375143420347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700018220784916762280231 4050027331177375143420347)
            ·
              refine ⟨6075040996766062715130521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050027331177375143420347 6075040996766062715130521)
              ·
                refine ⟨4556280747574547036347891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075040996766062715130521 4556280747574547036347891)
                ·
                  refine ⟨6834421121361820554521837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556280747574547036347891 6834421121361820554521837)
                  ·
                    refine ⟨2562907920510682707945689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6834421121361820554521837 2562907920510682707945689)
                    ·
                      refine ⟨1922180940383012030959267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562907920510682707945689 1922180940383012030959267)
                      ·
                        rfl

theorem cell23_3743434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_3743434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743434 prefixEnd_3743434 := by exact prefixLift 3743434
  have htrace : WordTrace (prefixWord ++ tailWord_3743434) baseStart_3743434 baseEnd_3743434 := by
    simpa [prefixWord, tailWord_3743434, baseEnd_3743434] using wordTrace_append hprefix tailTrace_3743434
  have hstable : (prefixWord ++ tailWord_3743434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743434).length < 2 ^ (prefixWord ++ tailWord_3743434).sum := by decide
  have hdescent : baseEnd_3743434 < baseStart_3743434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743439 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_3743439 : Nat := 118140960795 + 3743439 * 2 ^ 59
def prefixEnd_3743439 : Nat := 4983230072969 + 3 ^ 40 * 3743439 * 2
def baseEnd_3743439 : Nat := 1922183507786284511396743

theorem tailTrace_3743439 : CollatzResearch.WordTrace tailWord_3743439 prefixEnd_3743439 1922183507786284511396743 := by
  unfold tailWord_3743439
  simp only [CollatzResearch.WordTrace]
  refine ⟨136534437085167306326769371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91022958056778204217846247 136534437085167306326769371)
  ·
    refine ⟨204801655627750959490154057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136534437085167306326769371 204801655627750959490154057)
    ·
      refine ⟨153601241720813219617615543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204801655627750959490154057 153601241720813219617615543)
      ·
        refine ⟨230401862581219829426423315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153601241720813219617615543 230401862581219829426423315)
        ·
          refine ⟨345602793871829744139634973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230401862581219829426423315 345602793871829744139634973)
          ·
            refine ⟨129601047701936154052363115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345602793871829744139634973 129601047701936154052363115)
            ·
              refine ⟨194401571552904231078544673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129601047701936154052363115 194401571552904231078544673)
              ·
                refine ⟨145801178664678173308908505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194401571552904231078544673 145801178664678173308908505)
                ·
                  refine ⟨109350883998508629981681379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145801178664678173308908505 109350883998508629981681379)
                  ·
                    refine ⟨164026325997762944972522069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109350883998508629981681379 164026325997762944972522069)
                    ·
                      refine ⟨1922183507786284511396743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164026325997762944972522069 1922183507786284511396743)
                      ·
                        rfl

theorem cell23_3743439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_3743439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743439 prefixEnd_3743439 := by exact prefixLift 3743439
  have htrace : WordTrace (prefixWord ++ tailWord_3743439) baseStart_3743439 baseEnd_3743439 := by
    simpa [prefixWord, tailWord_3743439, baseEnd_3743439] using wordTrace_append hprefix tailTrace_3743439
  have hstable : (prefixWord ++ tailWord_3743439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743439).length < 2 ^ (prefixWord ++ tailWord_3743439).sum := by decide
  have hdescent : baseEnd_3743439 < baseStart_3743439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743473 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 2, 5, 2]
def baseStart_3743473 : Nat := 118140960795 + 3743473 * 2 ^ 59
def prefixEnd_3743473 : Nat := 4983230072969 + 3 ^ 40 * 3743473 * 2
def baseEnd_3743473 : Nat := 1922200966128537378371587

theorem tailTrace_3743473 : CollatzResearch.WordTrace tailWord_3743473 prefixEnd_3743473 1922200966128537378371587 := by
  unfold tailWord_3743473
  simp only [CollatzResearch.WordTrace]
  refine ⟨136535677167044130133507073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91023784778029420089004715 136535677167044130133507073)
  ·
    refine ⟨102401757875283097600130305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136535677167044130133507073 102401757875283097600130305)
    ·
      refine ⟨76801318406462323200097729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102401757875283097600130305 76801318406462323200097729)
      ·
        refine ⟨57600988804846742400073297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76801318406462323200097729 57600988804846742400073297)
        ·
          refine ⟨43200741603635056800054973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57600988804846742400073297 43200741603635056800054973)
          ·
            refine ⟨16200278101363146300020615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43200741603635056800054973 16200278101363146300020615)
            ·
              refine ⟨24300417152044719450030923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16200278101363146300020615 24300417152044719450030923)
              ·
                refine ⟨36450625728067079175046385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24300417152044719450030923 36450625728067079175046385)
                ·
                  refine ⟨27337969296050309381284789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36450625728067079175046385 27337969296050309381284789)
                  ·
                    refine ⟨2562934621504716504495449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27337969296050309381284789 2562934621504716504495449)
                    ·
                      refine ⟨1922200966128537378371587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562934621504716504495449 1922200966128537378371587)
                      ·
                        rfl

theorem cell23_3743473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_3743473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743473 prefixEnd_3743473 := by exact prefixLift 3743473
  have htrace : WordTrace (prefixWord ++ tailWord_3743473) baseStart_3743473 baseEnd_3743473 := by
    simpa [prefixWord, tailWord_3743473, baseEnd_3743473] using wordTrace_append hprefix tailTrace_3743473
  have hstable : (prefixWord ++ tailWord_3743473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743473).length < 2 ^ (prefixWord ++ tailWord_3743473).sum := by decide
  have hdescent : baseEnd_3743473 < baseStart_3743473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743490 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 2, 5, 2]
def baseStart_3743490 : Nat := 118140960795 + 3743490 * 2 ^ 59
def prefixEnd_3743490 : Nat := 4983230072969 + 3 ^ 40 * 3743490 * 2
def baseEnd_3743490 : Nat := 1922209695299663811859009

theorem tailTrace_3743490 : CollatzResearch.WordTrace tailWord_3743490 prefixEnd_3743490 1922209695299663811859009 := by
  unfold tailWord_3743490
  simp only [CollatzResearch.WordTrace]
  refine ⟨34134074301995635509218981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91024198138655028024583949 34134074301995635509218981)
  ·
    refine ⟨6400138931624181657978559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34134074301995635509218981 6400138931624181657978559)
    ·
      refine ⟨9600208397436272486967839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6400138931624181657978559 9600208397436272486967839)
      ·
        refine ⟨14400312596154408730451759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600208397436272486967839 14400312596154408730451759)
        ·
          refine ⟨21600468894231613095677639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14400312596154408730451759 21600468894231613095677639)
          ·
            refine ⟨32400703341347419643516459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21600468894231613095677639 32400703341347419643516459)
            ·
              refine ⟨48601055012021129465274689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32400703341347419643516459 48601055012021129465274689)
              ·
                refine ⟨36450791259015847098956017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48601055012021129465274689 36450791259015847098956017)
                ·
                  refine ⟨27338093444261885324217013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36450791259015847098956017 27338093444261885324217013)
                  ·
                    refine ⟨2562946260399551749145345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27338093444261885324217013 2562946260399551749145345)
                    ·
                      refine ⟨1922209695299663811859009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2562946260399551749145345 1922209695299663811859009)
                      ·
                        rfl

theorem cell23_3743490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_3743490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743490 prefixEnd_3743490 := by exact prefixLift 3743490
  have htrace : WordTrace (prefixWord ++ tailWord_3743490) baseStart_3743490 baseEnd_3743490 := by
    simpa [prefixWord, tailWord_3743490, baseEnd_3743490] using wordTrace_append hprefix tailTrace_3743490
  have hstable : (prefixWord ++ tailWord_3743490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743490).length < 2 ^ (prefixWord ++ tailWord_3743490).sum := by decide
  have hdescent : baseEnd_3743490 < baseStart_3743490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743516 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3743516 : Nat := 118140960795 + 3743516 * 2 ^ 59
def prefixEnd_3743516 : Nat := 4983230072969 + 3 ^ 40 * 3743516 * 2
def baseEnd_3743516 : Nat := 1922223045796680710133889

theorem tailTrace_3743516 : CollatzResearch.WordTrace tailWord_3743516 prefixEnd_3743516 1922223045796680710133889 := by
  unfold tailWord_3743516
  simp only [CollatzResearch.WordTrace]
  refine ⟨68268622752944174238661201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91024830337258898984881601 68268622752944174238661201)
  ·
    refine ⟨51201467064708130678995901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68268622752944174238661201 51201467064708130678995901)
    ·
      refine ⟨19200550149265549004623463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51201467064708130678995901 19200550149265549004623463)
      ·
        refine ⟨28800825223898323506935195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19200550149265549004623463 28800825223898323506935195)
        ·
          refine ⟨43201237835847485260402793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28800825223898323506935195 43201237835847485260402793)
          ·
            refine ⟨32400928376885613945302095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43201237835847485260402793 32400928376885613945302095)
            ·
              refine ⟨48601392565328420917953143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32400928376885613945302095 48601392565328420917953143)
              ·
                refine ⟨72902088847992631376929715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48601392565328420917953143 72902088847992631376929715)
                ·
                  refine ⟨109353133271988947065394573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72902088847992631376929715 109353133271988947065394573)
                  ·
                    refine ⟨41007424976995855149522965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109353133271988947065394573 41007424976995855149522965)
                    ·
                      refine ⟨1922223045796680710133889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41007424976995855149522965 1922223045796680710133889)
                      ·
                        rfl

theorem cell23_3743516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3743516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743516 prefixEnd_3743516 := by exact prefixLift 3743516
  have htrace : WordTrace (prefixWord ++ tailWord_3743516) baseStart_3743516 baseEnd_3743516 := by
    simpa [prefixWord, tailWord_3743516, baseEnd_3743516] using wordTrace_append hprefix tailTrace_3743516
  have hstable : (prefixWord ++ tailWord_3743516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743516).length < 2 ^ (prefixWord ++ tailWord_3743516).sum := by decide
  have hdescent : baseEnd_3743516 < baseStart_3743516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743523 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 3]
def baseStart_3743523 : Nat := 118140960795 + 3743523 * 2 ^ 59
def prefixEnd_3743523 : Nat := 4983230072969 + 3 ^ 40 * 3743523 * 2
def baseEnd_3743523 : Nat := 1922226640161262182746357

theorem tailTrace_3743523 : CollatzResearch.WordTrace tailWord_3743523 prefixEnd_3743523 1922226640161262182746357 := by
  unfold tailWord_3743523
  simp only [CollatzResearch.WordTrace]
  refine ⟨136537500816862988672827223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91025000544575325781884815 136537500816862988672827223)
  ·
    refine ⟨204806251225294483009240835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136537500816862988672827223 204806251225294483009240835)
    ·
      refine ⟨307209376837941724513861253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204806251225294483009240835 307209376837941724513861253)
      ·
        refine ⟨57601758157114073346348985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307209376837941724513861253 57601758157114073346348985)
        ·
          refine ⟨43201318617835555009761739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57601758157114073346348985 43201318617835555009761739)
          ·
            refine ⟨64801977926753332514642609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43201318617835555009761739 64801977926753332514642609)
            ·
              refine ⟨48601483445064999385981957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64801977926753332514642609 48601483445064999385981957)
              ·
                refine ⟨9112778145949687384871617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48601483445064999385981957 9112778145949687384871617)
                ·
                  refine ⟨6834583609462265538653713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9112778145949687384871617 6834583609462265538653713)
                  ·
                    refine ⟨5125937707096699153990285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6834583609462265538653713 5125937707096699153990285)
                    ·
                      refine ⟨1922226640161262182746357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5125937707096699153990285 1922226640161262182746357)
                      ·
                        rfl

theorem cell23_3743523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_3743523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743523 prefixEnd_3743523 := by exact prefixLift 3743523
  have htrace : WordTrace (prefixWord ++ tailWord_3743523) baseStart_3743523 baseEnd_3743523 := by
    simpa [prefixWord, tailWord_3743523, baseEnd_3743523] using wordTrace_append hprefix tailTrace_3743523
  have hstable : (prefixWord ++ tailWord_3743523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743523).length < 2 ^ (prefixWord ++ tailWord_3743523).sum := by decide
  have hdescent : baseEnd_3743523 < baseStart_3743523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743540 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_3743540 : Nat := 118140960795 + 3743540 * 2 ^ 59
def prefixEnd_3743540 : Nat := 4983230072969 + 3 ^ 40 * 3743540 * 2
def baseEnd_3743540 : Nat := 1922235369332388616233779

theorem tailTrace_3743540 : CollatzResearch.WordTrace tailWord_3743540 prefixEnd_3743540 1922235369332388616233779 := by
  unfold tailWord_3743540
  simp only [CollatzResearch.WordTrace]
  refine ⟨68269060428900700288098037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91025413905200933717464049 68269060428900700288098037)
  ·
    refine ⟨6400224415209440652009191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68269060428900700288098037 6400224415209440652009191)
    ·
      refine ⟨9600336622814160978013787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6400224415209440652009191 9600336622814160978013787)
      ·
        refine ⟨14400504934221241467020681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600336622814160978013787 14400504934221241467020681)
        ·
          refine ⟨10800378700665931100265511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14400504934221241467020681 10800378700665931100265511)
          ·
            refine ⟨16200568050998896650398267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10800378700665931100265511 16200568050998896650398267)
            ·
              refine ⟨24300852076498344975597401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16200568050998896650398267 24300852076498344975597401)
              ·
                refine ⟨18225639057373758731698051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24300852076498344975597401 18225639057373758731698051)
                ·
                  refine ⟨27338458586060638097547077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18225639057373758731698051 27338458586060638097547077)
                  ·
                    refine ⟨5125960984886369643290077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27338458586060638097547077 5125960984886369643290077)
                    ·
                      refine ⟨1922235369332388616233779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5125960984886369643290077 1922235369332388616233779)
                      ·
                        rfl

theorem cell23_3743540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_3743540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743540 prefixEnd_3743540 := by exact prefixLift 3743540
  have htrace : WordTrace (prefixWord ++ tailWord_3743540) baseStart_3743540 baseEnd_3743540 := by
    simpa [prefixWord, tailWord_3743540, baseEnd_3743540] using wordTrace_append hprefix tailTrace_3743540
  have hstable : (prefixWord ++ tailWord_3743540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743540).length < 2 ^ (prefixWord ++ tailWord_3743540).sum := by decide
  have hdescent : baseEnd_3743540 < baseStart_3743540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743564 : List Nat := [2, 2, 1, 3, 4, 2, 1, 3, 1, 4]
def baseStart_3743564 : Nat := 118140960795 + 3743564 * 2 ^ 59
def prefixEnd_3743564 : Nat := 4983230072969 + 3 ^ 40 * 3743564 * 2
def baseEnd_3743564 : Nat := 640749230956032174111223

theorem tailTrace_3743564 : CollatzResearch.WordTrace tailWord_3743564 prefixEnd_3743564 640749230956032174111223 := by
  unfold tailWord_3743564
  simp only [CollatzResearch.WordTrace]
  refine ⟨68269498104857226337534873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91025997473142968450046497 68269498104857226337534873)
  ·
    refine ⟨51202123578642919753151155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68269498104857226337534873 51202123578642919753151155)
    ·
      refine ⟨76803185367964379629726733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51202123578642919753151155 76803185367964379629726733)
      ·
        refine ⟨28801194512986642361147525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76803185367964379629726733 28801194512986642361147525)
        ·
          refine ⟨5400223971184995442715161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28801194512986642361147525 5400223971184995442715161)
          ·
            refine ⟨4050167978388746582036371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400223971184995442715161 4050167978388746582036371)
            ·
              refine ⟨6075251967583119873054557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050167978388746582036371 6075251967583119873054557)
              ·
                refine ⟨2278219487843669952395459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6075251967583119873054557 2278219487843669952395459)
                ·
                  refine ⟨3417329231765504928593189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278219487843669952395459 3417329231765504928593189)
                  ·
                    refine ⟨640749230956032174111223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417329231765504928593189 640749230956032174111223)
                    ·
                      rfl

theorem cell23_3743564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 3, 1, 4].length) (baseStart_3743564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743564 prefixEnd_3743564 := by exact prefixLift 3743564
  have htrace : WordTrace (prefixWord ++ tailWord_3743564) baseStart_3743564 baseEnd_3743564 := by
    simpa [prefixWord, tailWord_3743564, baseEnd_3743564] using wordTrace_append hprefix tailTrace_3743564
  have hstable : (prefixWord ++ tailWord_3743564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743564).length < 2 ^ (prefixWord ++ tailWord_3743564).sum := by decide
  have hdescent : baseEnd_3743564 < baseStart_3743564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743594 : List Nat := [3, 1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_3743594 : Nat := 118140960795 + 3743594 * 2 ^ 59
def prefixEnd_3743594 : Nat := 4983230072969 + 3 ^ 40 * 3743594 * 2
def baseEnd_3743594 : Nat := 213584788587525711662059

theorem tailTrace_3743594 : CollatzResearch.WordTrace tailWord_3743594 prefixEnd_3743594 213584788587525711662059 := by
  unfold tailWord_3743594
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135022599901441949665459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91026726933070511865774557 34135022599901441949665459)
  ·
    refine ⟨51202533899852162924498189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34135022599901441949665459 51202533899852162924498189)
    ·
      refine ⟨19200950212444561096686821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51202533899852162924498189 19200950212444561096686821)
      ·
        refine ⟨3600178164833355205628779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19200950212444561096686821 3600178164833355205628779)
        ·
          refine ⟨5400267247250032808443169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600178164833355205628779 5400267247250032808443169)
          ·
            refine ⟨4050200435437524606332377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400267247250032808443169 4050200435437524606332377)
            ·
              refine ⟨3037650326578143454749283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050200435437524606332377 3037650326578143454749283)
              ·
                refine ⟨4556475489867215182123925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037650326578143454749283 4556475489867215182123925)
                ·
                  refine ⟨213584788587525711662059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4556475489867215182123925 213584788587525711662059)
                  ·
                    rfl

theorem cell23_3743594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_3743594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743594 prefixEnd_3743594 := by exact prefixLift 3743594
  have htrace : WordTrace (prefixWord ++ tailWord_3743594) baseStart_3743594 baseEnd_3743594 := by
    simpa [prefixWord, tailWord_3743594, baseEnd_3743594] using wordTrace_append hprefix tailTrace_3743594
  have hstable : (prefixWord ++ tailWord_3743594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743594).length < 2 ^ (prefixWord ++ tailWord_3743594).sum := by decide
  have hdescent : baseEnd_3743594 < baseStart_3743594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743610 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_3743610 : Nat := 118140960795 + 3743610 * 2 ^ 59
def prefixEnd_3743610 : Nat := 4983230072969 + 3 ^ 40 * 3743610 * 2
def baseEnd_3743610 : Nat := 1922271312978203342358457

theorem tailTrace_3743610 : CollatzResearch.WordTrace tailWord_3743610 prefixEnd_3743610 1922271312978203342358457 := by
  unfold tailWord_3743610
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135168491886950632811071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91027115978365201687496189 34135168491886950632811071)
  ·
    refine ⟨51202752737830425949216607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34135168491886950632811071 51202752737830425949216607)
    ·
      refine ⟨76804129106745638923824911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51202752737830425949216607 76804129106745638923824911)
      ·
        refine ⟨115206193660118458385737367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76804129106745638923824911 115206193660118458385737367)
        ·
          refine ⟨172809290490177687578606051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115206193660118458385737367 172809290490177687578606051)
          ·
            refine ⟨259213935735266531367909077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172809290490177687578606051 259213935735266531367909077)
            ·
              refine ⟨6075326618795309328935369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 259213935735266531367909077 6075326618795309328935369)
              ·
                refine ⟨4556494964096481996701527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075326618795309328935369 4556494964096481996701527)
                ·
                  refine ⟨6834742446144722995052291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556494964096481996701527 6834742446144722995052291)
                  ·
                    refine ⟨10252113669217084492578437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6834742446144722995052291 10252113669217084492578437)
                    ·
                      refine ⟨1922271312978203342358457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10252113669217084492578437 1922271312978203342358457)
                      ·
                        rfl

theorem cell23_3743610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_3743610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743610 prefixEnd_3743610 := by exact prefixLift 3743610
  have htrace : WordTrace (prefixWord ++ tailWord_3743610) baseStart_3743610 baseEnd_3743610 := by
    simpa [prefixWord, tailWord_3743610, baseEnd_3743610] using wordTrace_append hprefix tailTrace_3743610
  have hstable : (prefixWord ++ tailWord_3743610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743610).length < 2 ^ (prefixWord ++ tailWord_3743610).sum := by decide
  have hdescent : baseEnd_3743610 < baseStart_3743610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743614 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3743614 : Nat := 118140960795 + 3743614 * 2 ^ 59
def prefixEnd_3743614 : Nat := 4983230072969 + 3 ^ 40 * 3743614 * 2
def baseEnd_3743614 : Nat := 1922273366900821326708439

theorem tailTrace_3743614 : CollatzResearch.WordTrace tailWord_3743614 prefixEnd_3743614 1922273366900821326708439 := by
  unfold tailWord_3743614
  simp only [CollatzResearch.WordTrace]
  refine ⟨17067602482441663901798737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91027213239688874142926597 17067602482441663901798737)
  ·
    refine ⟨12800701861831247926349053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17067602482441663901798737 12800701861831247926349053)
    ·
      refine ⟨4800263198186717972380895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12800701861831247926349053 4800263198186717972380895)
      ·
        refine ⟨7200394797280076958571343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800263198186717972380895 7200394797280076958571343)
        ·
          refine ⟨10800592195920115437857015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200394797280076958571343 10800592195920115437857015)
          ·
            refine ⟨16200888293880173156785523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10800592195920115437857015 16200888293880173156785523)
            ·
              refine ⟨24301332440820259735178285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16200888293880173156785523 24301332440820259735178285)
              ·
                refine ⟨9112999665307597400691857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24301332440820259735178285 9112999665307597400691857)
                ·
                  refine ⟨6834749748980698050518893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9112999665307597400691857 6834749748980698050518893)
                  ·
                    refine ⟨2563031155867761768944585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6834749748980698050518893 2563031155867761768944585)
                    ·
                      refine ⟨1922273366900821326708439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563031155867761768944585 1922273366900821326708439)
                      ·
                        rfl

theorem cell23_3743614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3743614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743614 prefixEnd_3743614 := by exact prefixLift 3743614
  have htrace : WordTrace (prefixWord ++ tailWord_3743614) baseStart_3743614 baseEnd_3743614 := by
    simpa [prefixWord, tailWord_3743614, baseEnd_3743614] using wordTrace_append hprefix tailTrace_3743614
  have hstable : (prefixWord ++ tailWord_3743614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743614).length < 2 ^ (prefixWord ++ tailWord_3743614).sum := by decide
  have hdescent : baseEnd_3743614 < baseStart_3743614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743616 : List Nat := [2, 1, 1, 2, 1, 2, 3, 11]
def baseStart_3743616 : Nat := 118140960795 + 3743616 * 2 ^ 59
def prefixEnd_3743616 : Nat := 4983230072969 + 3 ^ 40 * 3743616 * 2
def baseEnd_3743616 : Nat := 71195347920819641440127

theorem tailTrace_3743616 : CollatzResearch.WordTrace tailWord_3743616 prefixEnd_3743616 71195347920819641440127 := by
  unfold tailWord_3743616
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270446402763032777981351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91027261870350710370641801 68270446402763032777981351)
  ·
    refine ⟨102405669604144549166972027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68270446402763032777981351 102405669604144549166972027)
    ·
      refine ⟨153608504406216823750458041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102405669604144549166972027 153608504406216823750458041)
      ·
        refine ⟨115206378304662617812843531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153608504406216823750458041 115206378304662617812843531)
        ·
          refine ⟨172809567456993926719265297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115206378304662617812843531 172809567456993926719265297)
          ·
            refine ⟨129607175592745445039448973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172809567456993926719265297 129607175592745445039448973)
            ·
              refine ⟨48602690847279541889793365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129607175592745445039448973 48602690847279541889793365)
              ·
                refine ⟨71195347920819641440127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 48602690847279541889793365 71195347920819641440127)
                ·
                  rfl

theorem cell23_3743616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 11].length) (baseStart_3743616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743616 prefixEnd_3743616 := by exact prefixLift 3743616
  have htrace : WordTrace (prefixWord ++ tailWord_3743616) baseStart_3743616 baseEnd_3743616 := by
    simpa [prefixWord, tailWord_3743616, baseEnd_3743616] using wordTrace_append hprefix tailTrace_3743616
  have hstable : (prefixWord ++ tailWord_3743616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743616).length < 2 ^ (prefixWord ++ tailWord_3743616).sum := by decide
  have hdescent : baseEnd_3743616 < baseStart_3743616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743673 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3743673 : Nat := 118140960795 + 3743673 * 2 ^ 59
def prefixEnd_3743673 : Nat := 4983230072969 + 3 ^ 40 * 3743673 * 2
def baseEnd_3743673 : Nat := 1922303662259436595870667

theorem tailTrace_3743673 : CollatzResearch.WordTrace tailWord_3743673 prefixEnd_3743673 1922303662259436595870667 := by
  unfold tailWord_3743673
  simp only [CollatzResearch.WordTrace]
  refine ⟨136542971766319564290787673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91028647844213042860525115 136542971766319564290787673)
  ·
    refine ⟨102407228824739673218090755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136542971766319564290787673 102407228824739673218090755)
    ·
      refine ⟨153610843237109509827136133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102407228824739673218090755 153610843237109509827136133)
      ·
        refine ⟨28802033106958033092588025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153610843237109509827136133 28802033106958033092588025)
        ·
          refine ⟨21601524830218524819441019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28802033106958033092588025 21601524830218524819441019)
          ·
            refine ⟨32402287245327787229161529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21601524830218524819441019 32402287245327787229161529)
            ·
              refine ⟨24301715433995840421871147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32402287245327787229161529 24301715433995840421871147)
              ·
                refine ⟨36452573150993760632806721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24301715433995840421871147 36452573150993760632806721)
                ·
                  refine ⟨27339429863245320474605041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36452573150993760632806721 27339429863245320474605041)
                  ·
                    refine ⟨20504572397433990355953781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27339429863245320474605041 20504572397433990355953781)
                    ·
                      refine ⟨1922303662259436595870667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20504572397433990355953781 1922303662259436595870667)
                      ·
                        rfl

theorem cell23_3743673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3743673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743673 prefixEnd_3743673 := by exact prefixLift 3743673
  have htrace : WordTrace (prefixWord ++ tailWord_3743673) baseStart_3743673 baseEnd_3743673 := by
    simpa [prefixWord, tailWord_3743673, baseEnd_3743673] using wordTrace_append hprefix tailTrace_3743673
  have hstable : (prefixWord ++ tailWord_3743673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743673).length < 2 ^ (prefixWord ++ tailWord_3743673).sum := by decide
  have hdescent : baseEnd_3743673 < baseStart_3743673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743708 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3743708 : Nat := 118140960795 + 3743708 * 2 ^ 59
def prefixEnd_3743708 : Nat := 4983230072969 + 3 ^ 40 * 3743708 * 2
def baseEnd_3743708 : Nat := 1922321634082343958933007

theorem tailTrace_3743708 : CollatzResearch.WordTrace tailWord_3743708 prefixEnd_3743708 1922321634082343958933007 := by
  unfold tailWord_3743708
  simp only [CollatzResearch.WordTrace]
  refine ⟨68272124160596382634155889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91029498880795176845541185 68272124160596382634155889)
  ·
    refine ⟨51204093120447286975616917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68272124160596382634155889 51204093120447286975616917)
    ·
      refine ⟨2400191865020966576982043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51204093120447286975616917 2400191865020966576982043)
      ·
        refine ⟨3600287797531449865473065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400191865020966576982043 3600287797531449865473065)
        ·
          refine ⟨2700215848148587399104799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600287797531449865473065 2700215848148587399104799)
          ·
            refine ⟨4050323772222881098657199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700215848148587399104799 4050323772222881098657199)
            ·
              refine ⟨6075485658334321647985799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050323772222881098657199 6075485658334321647985799)
              ·
                refine ⟨9113228487501482471978699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075485658334321647985799 9113228487501482471978699)
                ·
                  refine ⟨13669842731252223707968049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9113228487501482471978699 13669842731252223707968049)
                  ·
                    refine ⟨10252382048439167780976037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13669842731252223707968049 10252382048439167780976037)
                    ·
                      refine ⟨1922321634082343958933007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10252382048439167780976037 1922321634082343958933007)
                      ·
                        rfl

theorem cell23_3743708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3743708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743708 prefixEnd_3743708 := by exact prefixLift 3743708
  have htrace : WordTrace (prefixWord ++ tailWord_3743708) baseStart_3743708 baseEnd_3743708 := by
    simpa [prefixWord, tailWord_3743708, baseEnd_3743708] using wordTrace_append hprefix tailTrace_3743708
  have hstable : (prefixWord ++ tailWord_3743708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743708).length < 2 ^ (prefixWord ++ tailWord_3743708).sum := by decide
  have hdescent : baseEnd_3743708 < baseStart_3743708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743760 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 1, 7, 2]
def baseStart_3743760 : Nat := 118140960795 + 3743760 * 2 ^ 59
def prefixEnd_3743760 : Nat := 4983230072969 + 3 ^ 40 * 3743760 * 2
def baseEnd_3743760 : Nat := 1922348335076377755482767

theorem tailTrace_3743760 : CollatzResearch.WordTrace tailWord_3743760 prefixEnd_3743760 1922348335076377755482767 := by
  unfold tailWord_3743760
  simp only [CollatzResearch.WordTrace]
  refine ⟨68273072458502189074602367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91030763278002918766136489 68273072458502189074602367)
  ·
    refine ⟨102409608687753283611903551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68273072458502189074602367 102409608687753283611903551)
    ·
      refine ⟨153614413031629925417855327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102409608687753283611903551 153614413031629925417855327)
      ·
        refine ⟨230421619547444888126782991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153614413031629925417855327 230421619547444888126782991)
        ·
          refine ⟨345632429321167332190174487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230421619547444888126782991 345632429321167332190174487)
          ·
            refine ⟨518448643981750998285261731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345632429321167332190174487 518448643981750998285261731)
            ·
              refine ⟨777672965972626497427892597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518448643981750998285261731 777672965972626497427892597)
              ·
                refine ⟨72906840559933734133864931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777672965972626497427892597 72906840559933734133864931)
                ·
                  refine ⟨109360260839900601200797397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72906840559933734133864931 109360260839900601200797397)
                  ·
                    refine ⟨2563131113435170340643689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 109360260839900601200797397 2563131113435170340643689)
                    ·
                      refine ⟨1922348335076377755482767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563131113435170340643689 1922348335076377755482767)
                      ·
                        rfl

theorem cell23_3743760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 1, 7, 2].length) (baseStart_3743760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743760 prefixEnd_3743760 := by exact prefixLift 3743760
  have htrace : WordTrace (prefixWord ++ tailWord_3743760) baseStart_3743760 baseEnd_3743760 := by
    simpa [prefixWord, tailWord_3743760, baseEnd_3743760] using wordTrace_append hprefix tailTrace_3743760
  have hstable : (prefixWord ++ tailWord_3743760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743760).length < 2 ^ (prefixWord ++ tailWord_3743760).sum := by decide
  have hdescent : baseEnd_3743760 < baseStart_3743760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743763 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_3743763 : Nat := 118140960795 + 3743763 * 2 ^ 59
def prefixEnd_3743763 : Nat := 4983230072969 + 3 ^ 40 * 3743763 * 2
def baseEnd_3743763 : Nat := 1922349875518341243745253

theorem tailTrace_3743763 : CollatzResearch.WordTrace tailWord_3743763 prefixEnd_3743763 1922349875518341243745253 := by
  unfold tailWord_3743763
  simp only [CollatzResearch.WordTrace]
  refine ⟨136546254335993509661563943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91030836223995673107709295 136546254335993509661563943)
  ·
    refine ⟨204819381503990264492345915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136546254335993509661563943 204819381503990264492345915)
    ·
      refine ⟨307229072255985396738518873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204819381503990264492345915 307229072255985396738518873)
      ·
        refine ⟨230421804191989047553889155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307229072255985396738518873 230421804191989047553889155)
        ·
          refine ⟨345632706287983571330833733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230421804191989047553889155 345632706287983571330833733)
          ·
            refine ⟨64806132428996919624531325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 345632706287983571330833733 64806132428996919624531325)
            ·
              refine ⟨24302299660873844859199247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64806132428996919624531325 24302299660873844859199247)
              ·
                refine ⟨36453449491310767288798871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24302299660873844859199247 36453449491310767288798871)
                ·
                  refine ⟨54680174236966150933198307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36453449491310767288798871 54680174236966150933198307)
                  ·
                    refine ⟨82020261355449226399797461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54680174236966150933198307 82020261355449226399797461)
                    ·
                      refine ⟨1922349875518341243745253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82020261355449226399797461 1922349875518341243745253)
                      ·
                        rfl

theorem cell23_3743763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_3743763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743763 prefixEnd_3743763 := by exact prefixLift 3743763
  have htrace : WordTrace (prefixWord ++ tailWord_3743763) baseStart_3743763 baseEnd_3743763 := by
    simpa [prefixWord, tailWord_3743763, baseEnd_3743763] using wordTrace_append hprefix tailTrace_3743763
  have hstable : (prefixWord ++ tailWord_3743763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743763).length < 2 ^ (prefixWord ++ tailWord_3743763).sum := by decide
  have hdescent : baseEnd_3743763 < baseStart_3743763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743803 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_3743803 : Nat := 118140960795 + 3743803 * 2 ^ 59
def prefixEnd_3743803 : Nat := 4983230072969 + 3 ^ 40 * 3743803 * 2
def baseEnd_3743803 : Nat := 1922370414744521087245069

theorem tailTrace_3743803 : CollatzResearch.WordTrace tailWord_3743803 prefixEnd_3743803 1922370414744521087245069 := by
  unfold tailWord_3743803
  simp only [CollatzResearch.WordTrace]
  refine ⟨136547713255848596493020063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91031808837232397662013375 136547713255848596493020063)
  ·
    refine ⟨204821569883772894739530095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136547713255848596493020063 204821569883772894739530095)
    ·
      refine ⟨307232354825659342109295143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204821569883772894739530095 307232354825659342109295143)
      ·
        refine ⟨460848532238489013163942715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307232354825659342109295143 460848532238489013163942715)
        ·
          refine ⟨691272798357733519745914073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 460848532238489013163942715 691272798357733519745914073)
          ·
            refine ⟨518454598768300139809435555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 691272798357733519745914073 518454598768300139809435555)
            ·
              refine ⟨777681898152450209714153333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 518454598768300139809435555 777681898152450209714153333)
              ·
                refine ⟨72907677951792207160701875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 777681898152450209714153333 72907677951792207160701875)
                ·
                  refine ⟨109361516927688310741052813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72907677951792207160701875 109361516927688310741052813)
                  ·
                    refine ⟨41010568847883116527894805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109361516927688310741052813 41010568847883116527894805)
                    ·
                      refine ⟨1922370414744521087245069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41010568847883116527894805 1922370414744521087245069)
                      ·
                        rfl

theorem cell23_3743803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_3743803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743803 prefixEnd_3743803 := by exact prefixLift 3743803
  have htrace : WordTrace (prefixWord ++ tailWord_3743803) baseStart_3743803 baseEnd_3743803 := by
    simpa [prefixWord, tailWord_3743803, baseEnd_3743803] using wordTrace_append hprefix tailTrace_3743803
  have hstable : (prefixWord ++ tailWord_3743803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743803).length < 2 ^ (prefixWord ++ tailWord_3743803).sum := by decide
  have hdescent : baseEnd_3743803 < baseStart_3743803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743838 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3743838 : Nat := 118140960795 + 3743838 * 2 ^ 59
def prefixEnd_3743838 : Nat := 4983230072969 + 3 ^ 40 * 3743838 * 2
def baseEnd_3743838 : Nat := 640796128855809483435803

theorem tailTrace_3743838 : CollatzResearch.WordTrace tailWord_3743838 prefixEnd_3743838 640796128855809483435803 := by
  unfold tailWord_3743838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17068623726340224683818021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91032659873814531647029445 17068623726340224683818021)
  ·
    refine ⟨3200366948688792128215879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17068623726340224683818021 3200366948688792128215879)
    ·
      refine ⟨4800550423033188192323819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200366948688792128215879 4800550423033188192323819)
      ·
        refine ⟨7200825634549782288485729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800550423033188192323819 7200825634549782288485729)
        ·
          refine ⟨5400619225912336716364297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7200825634549782288485729 5400619225912336716364297)
          ·
            refine ⟨4050464419434252537273223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400619225912336716364297 4050464419434252537273223)
            ·
              refine ⟨6075696629151378805909835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050464419434252537273223 6075696629151378805909835)
              ·
                refine ⟨9113544943727068208864753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075696629151378805909835 9113544943727068208864753)
                ·
                  refine ⟨6835158707795301156648565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9113544943727068208864753 6835158707795301156648565)
                  ·
                    refine ⟨640796128855809483435803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6835158707795301156648565 640796128855809483435803)
                    ·
                      rfl

theorem cell23_3743838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3743838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743838 prefixEnd_3743838 := by exact prefixLift 3743838
  have htrace : WordTrace (prefixWord ++ tailWord_3743838) baseStart_3743838 baseEnd_3743838 := by
    simpa [prefixWord, tailWord_3743838, baseEnd_3743838] using wordTrace_append hprefix tailTrace_3743838
  have hstable : (prefixWord ++ tailWord_3743838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743838).length < 2 ^ (prefixWord ++ tailWord_3743838).sum := by decide
  have hdescent : baseEnd_3743838 < baseStart_3743838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743857 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 3]
def baseStart_3743857 : Nat := 118140960795 + 3743857 * 2 ^ 59
def prefixEnd_3743857 : Nat := 4983230072969 + 3 ^ 40 * 3743857 * 2
def baseEnd_3743857 : Nat := 1922398142699863875969821

theorem tailTrace_3743857 : CollatzResearch.WordTrace tailWord_3743857 prefixEnd_3743857 1922398142699863875969821 := by
  unfold tailWord_3743857
  simp only [CollatzResearch.WordTrace]
  refine ⟨136549682797652963715485825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91033121865101975810323883 136549682797652963715485825)
  ·
    refine ⟨102412262098239722786614369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136549682797652963715485825 102412262098239722786614369)
    ·
      refine ⟨76809196573679792089960777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102412262098239722786614369 76809196573679792089960777)
      ·
        refine ⟨57606897430259844067470583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76809196573679792089960777 57606897430259844067470583)
        ·
          refine ⟨86410346145389766101205875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57606897430259844067470583 86410346145389766101205875)
          ·
            refine ⟨129615519218084649151808813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86410346145389766101205875 129615519218084649151808813)
            ·
              refine ⟨48605819706781743431928305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129615519218084649151808813 48605819706781743431928305)
              ·
                refine ⟨36454364780086307573946229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48605819706781743431928305 36454364780086307573946229)
                ·
                  refine ⟨3417596698133091335057459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36454364780086307573946229 3417596698133091335057459)
                  ·
                    refine ⟨5126395047199637002586189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417596698133091335057459 5126395047199637002586189)
                    ·
                      refine ⟨1922398142699863875969821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5126395047199637002586189 1922398142699863875969821)
                      ·
                        rfl

theorem cell23_3743857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_3743857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743857 prefixEnd_3743857 := by exact prefixLift 3743857
  have htrace : WordTrace (prefixWord ++ tailWord_3743857) baseStart_3743857 baseEnd_3743857 := by
    simpa [prefixWord, tailWord_3743857, baseEnd_3743857] using wordTrace_append hprefix tailTrace_3743857
  have hstable : (prefixWord ++ tailWord_3743857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743857).length < 2 ^ (prefixWord ++ tailWord_3743857).sum := by decide
  have hdescent : baseEnd_3743857 < baseStart_3743857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743925 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3743925 : Nat := 118140960795 + 3743925 * 2 ^ 59
def prefixEnd_3743925 : Nat := 4983230072969 + 3 ^ 40 * 3743925 * 2
def baseEnd_3743925 : Nat := 1922433059384369609919509

theorem tailTrace_3743925 : CollatzResearch.WordTrace tailWord_3743925 prefixEnd_3743925 1922433059384369609919509 := by
  unfold tailWord_3743925
  simp only [CollatzResearch.WordTrace]
  refine ⟨136552162961406611328961229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91034775307604407552640819 136552162961406611328961229)
  ·
    refine ⟨51207061110527479248360461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136552162961406611328961229 51207061110527479248360461)
    ·
      refine ⟨19202647916447804718135173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51207061110527479248360461 19202647916447804718135173)
      ·
        refine ⟨3600496484333963384650345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19202647916447804718135173 3600496484333963384650345)
        ·
          refine ⟨2700372363250472538487759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600496484333963384650345 2700372363250472538487759)
          ·
            refine ⟨4050558544875708807731639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700372363250472538487759 4050558544875708807731639)
            ·
              refine ⟨6075837817313563211597459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050558544875708807731639 6075837817313563211597459)
              ·
                refine ⟨9113756725970344817396189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6075837817313563211597459 9113756725970344817396189)
                ·
                  refine ⟨3417658772238879306523571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9113756725970344817396189 3417658772238879306523571)
                  ·
                    refine ⟨5126488158358318959785357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417658772238879306523571 5126488158358318959785357)
                    ·
                      refine ⟨1922433059384369609919509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5126488158358318959785357 1922433059384369609919509)
                      ·
                        rfl

theorem cell23_3743925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3743925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743925 prefixEnd_3743925 := by exact prefixLift 3743925
  have htrace : WordTrace (prefixWord ++ tailWord_3743925) baseStart_3743925 baseEnd_3743925 := by
    simpa [prefixWord, tailWord_3743925, baseEnd_3743925] using wordTrace_append hprefix tailTrace_3743925
  have hstable : (prefixWord ++ tailWord_3743925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743925).length < 2 ^ (prefixWord ++ tailWord_3743925).sum := by decide
  have hdescent : baseEnd_3743925 < baseStart_3743925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743947 : List Nat := [1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 3]
def baseStart_3743947 : Nat := 118140960795 + 3743947 * 2 ^ 59
def prefixEnd_3743947 : Nat := 4983230072969 + 3 ^ 40 * 3743947 * 2
def baseEnd_3743947 : Nat := 1922444355958768523844407

theorem tailTrace_3743947 : CollatzResearch.WordTrace tailWord_3743947 prefixEnd_3743947 1922444355958768523844407 := by
  unfold tailWord_3743947
  simp only [CollatzResearch.WordTrace]
  refine ⟨136552965367326909086262095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91035310244884606057508063 136552965367326909086262095)
  ·
    refine ⟨204829448050990363629393143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136552965367326909086262095 204829448050990363629393143)
    ·
      refine ⟨307244172076485545444089715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204829448050990363629393143 307244172076485545444089715)
      ·
        refine ⟨460866258114728318166134573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307244172076485545444089715 460866258114728318166134573)
        ·
          refine ⟨172824846793023119312300465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 460866258114728318166134573 172824846793023119312300465)
          ·
            refine ⟨129618635094767339484225349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172824846793023119312300465 129618635094767339484225349)
            ·
              refine ⟨24303494080268876153292253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129618635094767339484225349 24303494080268876153292253)
              ·
                refine ⟨9113810280100828557484595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24303494080268876153292253 9113810280100828557484595)
                ·
                  refine ⟨13670715420151242836226893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9113810280100828557484595 13670715420151242836226893)
                  ·
                    refine ⟨5126518282556716063585085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13670715420151242836226893 5126518282556716063585085)
                    ·
                      refine ⟨1922444355958768523844407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5126518282556716063585085 1922444355958768523844407)
                      ·
                        rfl

theorem cell23_3743947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 3, 3].length) (baseStart_3743947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743947 prefixEnd_3743947 := by exact prefixLift 3743947
  have htrace : WordTrace (prefixWord ++ tailWord_3743947) baseStart_3743947 baseEnd_3743947 := by
    simpa [prefixWord, tailWord_3743947, baseEnd_3743947] using wordTrace_append hprefix tailTrace_3743947
  have hstable : (prefixWord ++ tailWord_3743947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743947).length < 2 ^ (prefixWord ++ tailWord_3743947).sum := by decide
  have hdescent : baseEnd_3743947 < baseStart_3743947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3743948 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3743948 : Nat := 118140960795 + 3743948 * 2 ^ 59
def prefixEnd_3743948 : Nat := 4983230072969 + 3 ^ 40 * 3743948 * 2
def baseEnd_3743948 : Nat := 1922444869439423019931903

theorem tailTrace_3743948 : CollatzResearch.WordTrace tailWord_3743948 prefixEnd_3743948 1922444869439423019931903 := by
  unfold tailWord_3743948
  simp only [CollatzResearch.WordTrace]
  refine ⟨68276500920161643128524249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91035334560215524171365665 68276500920161643128524249)
  ·
    refine ⟨51207375690121232346393187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68276500920161643128524249 51207375690121232346393187)
    ·
      refine ⟨76811063535181848519589781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51207375690121232346393187 76811063535181848519589781)
      ·
        refine ⟨3600518603211649149355771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76811063535181848519589781 3600518603211649149355771)
        ·
          refine ⟨5400777904817473724033657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600518603211649149355771 5400777904817473724033657)
          ·
            refine ⟨4050583428613105293025243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5400777904817473724033657 4050583428613105293025243)
            ·
              refine ⟨6075875142919657939537865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050583428613105293025243 6075875142919657939537865)
              ·
                refine ⟨4556906357189743454653399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6075875142919657939537865 4556906357189743454653399)
                ·
                  refine ⟨6835359535784615181980099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4556906357189743454653399 6835359535784615181980099)
                  ·
                    refine ⟨10253039303676922772970149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6835359535784615181980099 10253039303676922772970149)
                    ·
                      refine ⟨1922444869439423019931903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10253039303676922772970149 1922444869439423019931903)
                      ·
                        rfl

theorem cell23_3743948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3743948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3743948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3743948 prefixEnd_3743948 := by exact prefixLift 3743948
  have htrace : WordTrace (prefixWord ++ tailWord_3743948) baseStart_3743948 baseEnd_3743948 := by
    simpa [prefixWord, tailWord_3743948, baseEnd_3743948] using wordTrace_append hprefix tailTrace_3743948
  have hstable : (prefixWord ++ tailWord_3743948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3743948).length < 2 ^ (prefixWord ++ tailWord_3743948).sum := by decide
  have hdescent : baseEnd_3743948 < baseStart_3743948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3743948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744034 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_3744034 : Nat := 118140960795 + 3744034 * 2 ^ 59
def prefixEnd_3744034 : Nat := 4983230072969 + 3 ^ 40 * 3744034 * 2
def baseEnd_3744034 : Nat := 1922489028775709683456507

theorem tailTrace_3744034 : CollatzResearch.WordTrace tailWord_3744034 prefixEnd_3744034 1922489028775709683456507 := by
  unfold tailWord_3744034
  simp only [CollatzResearch.WordTrace]
  refine ⟨34139034629502930736169789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91037425678674481963119437 34139034629502930736169789)
  ·
    refine ⟨12802137986063599026063671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34139034629502930736169789 12802137986063599026063671)
    ·
      refine ⟨19203206979095398539095507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12802137986063599026063671 19203206979095398539095507)
      ·
        refine ⟨28804810468643097808643261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19203206979095398539095507 28804810468643097808643261)
        ·
          refine ⟨10801803925741161678241223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28804810468643097808643261 10801803925741161678241223)
          ·
            refine ⟨16202705888611742517361835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801803925741161678241223 16202705888611742517361835)
            ·
              refine ⟨24304058832917613776042753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16202705888611742517361835 24304058832917613776042753)
              ·
                refine ⟨18228044124688210332032065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24304058832917613776042753 18228044124688210332032065)
                ·
                  refine ⟨13671033093516157749024049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18228044124688210332032065 13671033093516157749024049)
                  ·
                    refine ⟨10253274820137118311768037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13671033093516157749024049 10253274820137118311768037)
                    ·
                      refine ⟨1922489028775709683456507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10253274820137118311768037 1922489028775709683456507)
                      ·
                        rfl

theorem cell23_3744034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_3744034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744034 prefixEnd_3744034 := by exact prefixLift 3744034
  have htrace : WordTrace (prefixWord ++ tailWord_3744034) baseStart_3744034 baseEnd_3744034 := by
    simpa [prefixWord, tailWord_3744034, baseEnd_3744034] using wordTrace_append hprefix tailTrace_3744034
  have hstable : (prefixWord ++ tailWord_3744034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744034).length < 2 ^ (prefixWord ++ tailWord_3744034).sum := by decide
  have hdescent : baseEnd_3744034 < baseStart_3744034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744044 : List Nat := [2, 2, 1, 1, 1, 3, 4, 4, 5]
def baseStart_3744044 : Nat := 118140960795 + 3744044 * 2 ^ 59
def prefixEnd_3744044 : Nat := 4983230072969 + 3 ^ 40 * 3744044 * 2
def baseEnd_3744044 : Nat := 213610462620250516036829

theorem tailTrace_3744044 : CollatzResearch.WordTrace tailWord_3744044 prefixEnd_3744044 213610462620250516036829 := by
  unfold tailWord_3744044
  simp only [CollatzResearch.WordTrace]
  refine ⟨68278251623987747326271593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91037668831983663101695457 68278251623987747326271593)
  ·
    refine ⟨51208688717990810494703695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68278251623987747326271593 51208688717990810494703695)
    ·
      refine ⟨76813033076986215742055543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51208688717990810494703695 76813033076986215742055543)
      ·
        refine ⟨115219549615479323613083315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76813033076986215742055543 115219549615479323613083315)
        ·
          refine ⟨172829324423218985419624973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115219549615479323613083315 172829324423218985419624973)
          ·
            refine ⟨64810996658707119532359365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172829324423218985419624973 64810996658707119532359365)
            ·
              refine ⟨12152061873507584912317381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64810996658707119532359365 12152061873507584912317381)
              ·
                refine ⟨2278511601282672171059509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12152061873507584912317381 2278511601282672171059509)
                ·
                  refine ⟨213610462620250516036829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2278511601282672171059509 213610462620250516036829)
                  ·
                    rfl

theorem cell23_3744044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 4, 5].length) (baseStart_3744044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744044 prefixEnd_3744044 := by exact prefixLift 3744044
  have htrace : WordTrace (prefixWord ++ tailWord_3744044) baseStart_3744044 baseEnd_3744044 := by
    simpa [prefixWord, tailWord_3744044, baseEnd_3744044] using wordTrace_append hprefix tailTrace_3744044
  have hstable : (prefixWord ++ tailWord_3744044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744044).length < 2 ^ (prefixWord ++ tailWord_3744044).sum := by decide
  have hdescent : baseEnd_3744044 < baseStart_3744044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744164 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 3, 5]
def baseStart_3744164 : Nat := 118140960795 + 3744164 * 2 ^ 59
def prefixEnd_3744164 : Nat := 4983230072969 + 3 ^ 40 * 3744164 * 2
def baseEnd_3744164 : Nat := 640851927086931391610303

theorem tailTrace_3744164 : CollatzResearch.WordTrace tailWord_3744164 prefixEnd_3744164 640851927086931391610303 := by
  unfold tailWord_3744164
  simp only [CollatzResearch.WordTrace]
  refine ⟨68280440003770377573455773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91040586671693836764607697 68280440003770377573455773)
  ·
    refine ⟨25605165001413891590045915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68280440003770377573455773 25605165001413891590045915)
    ·
      refine ⟨38407747502120837385068873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25605165001413891590045915 38407747502120837385068873)
      ·
        refine ⟨28805810626590628038801655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38407747502120837385068873 28805810626590628038801655)
        ·
          refine ⟨43208715939885942058202483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28805810626590628038801655 43208715939885942058202483)
          ·
            refine ⟨64813073909828913087303725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43208715939885942058202483 64813073909828913087303725)
            ·
              refine ⟨24304902716185842407738897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64813073909828913087303725 24304902716185842407738897)
              ·
                refine ⟨18228677037139381805804173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24304902716185842407738897 18228677037139381805804173)
                ·
                  refine ⟨6835753888927268177176565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18228677037139381805804173 6835753888927268177176565)
                  ·
                    refine ⟨640851927086931391610303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6835753888927268177176565 640851927086931391610303)
                    ·
                      rfl

theorem cell23_3744164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_3744164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744164 prefixEnd_3744164 := by exact prefixLift 3744164
  have htrace : WordTrace (prefixWord ++ tailWord_3744164) baseStart_3744164 baseEnd_3744164 := by
    simpa [prefixWord, tailWord_3744164, baseEnd_3744164] using wordTrace_append hprefix tailTrace_3744164
  have hstable : (prefixWord ++ tailWord_3744164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744164).length < 2 ^ (prefixWord ++ tailWord_3744164).sum := by decide
  have hdescent : baseEnd_3744164 < baseStart_3744164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744188 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 1, 5, 2]
def baseStart_3744188 : Nat := 118140960795 + 3744188 * 2 ^ 59
def prefixEnd_3744188 : Nat := 4983230072969 + 3 ^ 40 * 3744188 * 2
def baseEnd_3744188 : Nat := 1922568104796502080930799

theorem tailTrace_3744188 : CollatzResearch.WordTrace tailWord_3744188 prefixEnd_3744188 1922568104796502080930799 := by
  unfold tailWord_3744188
  simp only [CollatzResearch.WordTrace]
  refine ⟨68280877679726903622892609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91041170239635871497190145 68280877679726903622892609)
  ·
    refine ⟨51210658259795177717169457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68280877679726903622892609 51210658259795177717169457)
    ·
      refine ⟨38407993694846383287877093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51210658259795177717169457 38407993694846383287877093)
      ·
        refine ⟨7201498817783696866476955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38407993694846383287877093 7201498817783696866476955)
        ·
          refine ⟨10802248226675545299715433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201498817783696866476955 10802248226675545299715433)
          ·
            refine ⟨8101686170006658974786575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10802248226675545299715433 8101686170006658974786575)
            ·
              refine ⟨12152529255009988462179863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101686170006658974786575 12152529255009988462179863)
              ·
                refine ⟨18228793882514982693269795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12152529255009988462179863 18228793882514982693269795)
                ·
                  refine ⟨27343190823772474039904693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18228793882514982693269795 27343190823772474039904693)
                  ·
                    refine ⟨2563424139728669441241065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27343190823772474039904693 2563424139728669441241065)
                    ·
                      refine ⟨1922568104796502080930799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563424139728669441241065 1922568104796502080930799)
                      ·
                        rfl

theorem cell23_3744188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_3744188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744188 prefixEnd_3744188 := by exact prefixLift 3744188
  have htrace : WordTrace (prefixWord ++ tailWord_3744188) baseStart_3744188 baseEnd_3744188 := by
    simpa [prefixWord, tailWord_3744188, baseEnd_3744188] using wordTrace_append hprefix tailTrace_3744188
  have hstable : (prefixWord ++ tailWord_3744188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744188).length < 2 ^ (prefixWord ++ tailWord_3744188).sum := by decide
  have hdescent : baseEnd_3744188 < baseStart_3744188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744221 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3744221 : Nat := 118140960795 + 3744221 * 2 ^ 59
def prefixEnd_3744221 : Nat := 4983230072969 + 3 ^ 40 * 3744221 * 2
def baseEnd_3744221 : Nat := 1922585049658100451818147

theorem tailTrace_3744221 : CollatzResearch.WordTrace tailWord_3744221 prefixEnd_3744221 1922585049658100451818147 := by
  unfold tailWord_3744221
  simp only [CollatzResearch.WordTrace]
  refine ⟨136562958968334253881736517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91041972645556169254491011 136562958968334253881736517)
  ·
    refine ⟨25605554806562672602825597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136562958968334253881736517 25605554806562672602825597)
    ·
      refine ⟨9602083052461002226059599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25605554806562672602825597 9602083052461002226059599)
      ·
        refine ⟨14403124578691503339089399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602083052461002226059599 14403124578691503339089399)
        ·
          refine ⟨21604686868037255008634099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403124578691503339089399 21604686868037255008634099)
          ·
            refine ⟨32407030302055882512951149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21604686868037255008634099 32407030302055882512951149)
            ·
              refine ⟨12152636363270955942356681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32407030302055882512951149 12152636363270955942356681)
              ·
                refine ⟨9114477272453216956767511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12152636363270955942356681 9114477272453216956767511)
                ·
                  refine ⟨13671715908679825435151267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9114477272453216956767511 13671715908679825435151267)
                  ·
                    refine ⟨20507573863019738152726901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13671715908679825435151267 20507573863019738152726901)
                    ·
                      refine ⟨1922585049658100451818147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20507573863019738152726901 1922585049658100451818147)
                      ·
                        rfl

theorem cell23_3744221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3744221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744221 prefixEnd_3744221 := by exact prefixLift 3744221
  have htrace : WordTrace (prefixWord ++ tailWord_3744221) baseStart_3744221 baseEnd_3744221 := by
    simpa [prefixWord, tailWord_3744221, baseEnd_3744221] using wordTrace_append hprefix tailTrace_3744221
  have hstable : (prefixWord ++ tailWord_3744221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744221).length < 2 ^ (prefixWord ++ tailWord_3744221).sum := by decide
  have hdescent : baseEnd_3744221 < baseStart_3744221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744238 : List Nat := [4, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3]
def baseStart_3744238 : Nat := 118140960795 + 3744238 * 2 ^ 59
def prefixEnd_3744238 : Nat := 4983230072969 + 3 ^ 40 * 3744238 * 2
def baseEnd_3744238 : Nat := 1922593778829226885305569

theorem tailTrace_3744238 : CollatzResearch.WordTrace tailWord_3744238 prefixEnd_3744238 1922593778829226885305569 := by
  unfold tailWord_3744238
  simp only [CollatzResearch.WordTrace]
  refine ⟨17070447376159083223138171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91042386006181777190070245 17070447376159083223138171)
  ·
    refine ⟨25605671064238624834707257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17070447376159083223138171 25605671064238624834707257)
    ·
      refine ⟨19204253298178968626030443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25605671064238624834707257 19204253298178968626030443)
      ·
        refine ⟨28806379947268452939045665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19204253298178968626030443 28806379947268452939045665)
        ·
          refine ⟨21604784960451339704284249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28806379947268452939045665 21604784960451339704284249)
          ·
            refine ⟨16203588720338504778213187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21604784960451339704284249 16203588720338504778213187)
            ·
              refine ⟨24305383080507757167319781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16203588720338504778213187 24305383080507757167319781)
              ·
                refine ⟨4557259327595204468872459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24305383080507757167319781 4557259327595204468872459)
                ·
                  refine ⟨6835888991392806703308689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4557259327595204468872459 6835888991392806703308689)
                  ·
                    refine ⟨5126916743544605027481517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6835888991392806703308689 5126916743544605027481517)
                    ·
                      refine ⟨1922593778829226885305569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5126916743544605027481517 1922593778829226885305569)
                      ·
                        rfl

theorem cell23_3744238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_3744238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744238 prefixEnd_3744238 := by exact prefixLift 3744238
  have htrace : WordTrace (prefixWord ++ tailWord_3744238) baseStart_3744238 baseEnd_3744238 := by
    simpa [prefixWord, tailWord_3744238, baseEnd_3744238] using wordTrace_append hprefix tailTrace_3744238
  have hstable : (prefixWord ++ tailWord_3744238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744238).length < 2 ^ (prefixWord ++ tailWord_3744238).sum := by decide
  have hdescent : baseEnd_3744238 < baseStart_3744238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744258 : List Nat := [3, 4, 1, 2, 2, 2, 9]
def baseStart_3744258 : Nat := 118140960795 + 3744258 * 2 ^ 59
def prefixEnd_3744258 : Nat := 4983230072969 + 3 ^ 40 * 3744258 * 2
def baseEnd_3744258 : Nat := 23735852449905145766117

theorem tailTrace_3744258 : CollatzResearch.WordTrace tailWord_3744258 prefixEnd_3744258 23735852449905145766117 := by
  unfold tailWord_3744258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34141077117300052300208357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91042872312800139467222285 34141077117300052300208357)
  ·
    refine ⟨6401451959493759806289067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34141077117300052300208357 6401451959493759806289067)
    ·
      refine ⟨9602177939240639709433601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6401451959493759806289067 9602177939240639709433601)
      ·
        refine ⟨7201633454430479782075201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9602177939240639709433601 7201633454430479782075201)
        ·
          refine ⟨5401225090822859836556401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7201633454430479782075201 5401225090822859836556401)
          ·
            refine ⟨4050918818117144877417301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5401225090822859836556401 4050918818117144877417301)
            ·
              refine ⟨23735852449905145766117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4050918818117144877417301 23735852449905145766117)
              ·
                rfl

theorem cell23_3744258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 9].length) (baseStart_3744258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744258 prefixEnd_3744258 := by exact prefixLift 3744258
  have htrace : WordTrace (prefixWord ++ tailWord_3744258) baseStart_3744258 baseEnd_3744258 := by
    simpa [prefixWord, tailWord_3744258, baseEnd_3744258] using wordTrace_append hprefix tailTrace_3744258
  have hstable : (prefixWord ++ tailWord_3744258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744258).length < 2 ^ (prefixWord ++ tailWord_3744258).sum := by decide
  have hdescent : baseEnd_3744258 < baseStart_3744258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744262 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_3744262 : Nat := 118140960795 + 3744262 * 2 ^ 59
def prefixEnd_3744262 : Nat := 4983230072969 + 3 ^ 40 * 3744262 * 2
def baseEnd_3744262 : Nat := 640868700788311597135153

theorem tailTrace_3744262 : CollatzResearch.WordTrace tailWord_3744262 prefixEnd_3744262 640868700788311597135153 := by
  unfold tailWord_3744262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4267639198787053683874345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91042969574123811922652693 4267639198787053683874345)
  ·
    refine ⟨3200729399090290262905759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4267639198787053683874345 3200729399090290262905759)
    ·
      refine ⟨4801094098635435394358639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200729399090290262905759 4801094098635435394358639)
      ·
        refine ⟨7201641147953153091537959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801094098635435394358639 7201641147953153091537959)
        ·
          refine ⟨10802461721929729637306939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201641147953153091537959 10802461721929729637306939)
          ·
            refine ⟨16203692582894594455960409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802461721929729637306939 16203692582894594455960409)
            ·
              refine ⟨12152769437170945841970307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16203692582894594455960409 12152769437170945841970307)
              ·
                refine ⟨18229154155756418762955461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12152769437170945841970307 18229154155756418762955461)
                ·
                  refine ⟨3417966404204328518054149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18229154155756418762955461 3417966404204328518054149)
                  ·
                    refine ⟨640868700788311597135153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417966404204328518054149 640868700788311597135153)
                    ·
                      rfl

theorem cell23_3744262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_3744262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744262 prefixEnd_3744262 := by exact prefixLift 3744262
  have htrace : WordTrace (prefixWord ++ tailWord_3744262) baseStart_3744262 baseEnd_3744262 := by
    simpa [prefixWord, tailWord_3744262, baseEnd_3744262] using wordTrace_append hprefix tailTrace_3744262
  have hstable : (prefixWord ++ tailWord_3744262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744262).length < 2 ^ (prefixWord ++ tailWord_3744262).sum := by decide
  have hdescent : baseEnd_3744262 < baseStart_3744262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744264 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3744264 : Nat := 118140960795 + 3744264 * 2 ^ 59
def prefixEnd_3744264 : Nat := 4983230072969 + 3 ^ 40 * 3744264 * 2
def baseEnd_3744264 : Nat := 1922607129326243783580449

theorem tailTrace_3744264 : CollatzResearch.WordTrace tailWord_3744264 prefixEnd_3744264 1922607129326243783580449 := by
  unfold tailWord_3744264
  simp only [CollatzResearch.WordTrace]
  refine ⟨68282263653589236112775923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91043018204785648150367897 68282263653589236112775923)
  ·
    refine ⟨102423395480383854169163885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68282263653589236112775923 102423395480383854169163885)
    ·
      refine ⟨38408773305143945313436457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102423395480383854169163885 38408773305143945313436457)
      ·
        refine ⟨28806579978857958985077343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38408773305143945313436457 28806579978857958985077343)
        ·
          refine ⟨43209869968286938477616015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28806579978857958985077343 43209869968286938477616015)
          ·
            refine ⟨64814804952430407716424023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43209869968286938477616015 64814804952430407716424023)
            ·
              refine ⟨97222207428645611574636035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64814804952430407716424023 97222207428645611574636035)
              ·
                refine ⟨145833311142968417361954053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97222207428645611574636035 145833311142968417361954053)
                ·
                  refine ⟨27343745839306578255366385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145833311142968417361954053 27343745839306578255366385)
                  ·
                    refine ⟨20507809379479933691524789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27343745839306578255366385 20507809379479933691524789)
                    ·
                      refine ⟨1922607129326243783580449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20507809379479933691524789 1922607129326243783580449)
                      ·
                        rfl

theorem cell23_3744264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3744264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744264 prefixEnd_3744264 := by exact prefixLift 3744264
  have htrace : WordTrace (prefixWord ++ tailWord_3744264) baseStart_3744264 baseEnd_3744264 := by
    simpa [prefixWord, tailWord_3744264, baseEnd_3744264] using wordTrace_append hprefix tailTrace_3744264
  have hstable : (prefixWord ++ tailWord_3744264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744264).length < 2 ^ (prefixWord ++ tailWord_3744264).sum := by decide
  have hdescent : baseEnd_3744264 < baseStart_3744264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744268 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_3744268 : Nat := 118140960795 + 3744268 * 2 ^ 59
def prefixEnd_3744268 : Nat := 4983230072969 + 3 ^ 40 * 3744268 * 2
def baseEnd_3744268 : Nat := 1922609183248861767930431

theorem tailTrace_3744268 : CollatzResearch.WordTrace tailWord_3744268 prefixEnd_3744268 1922609183248861767930431 := by
  unfold tailWord_3744268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68282336599581990454348729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91043115466109320605798305 68282336599581990454348729)
  ·
    refine ⟨51211752449686492840761547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68282336599581990454348729 51211752449686492840761547)
    ·
      refine ⟨76817628674529739261142321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51211752449686492840761547 76817628674529739261142321)
      ·
        refine ⟨57613221505897304445856741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76817628674529739261142321 57613221505897304445856741)
        ·
          refine ⟨10802479032355744583598139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57613221505897304445856741 10802479032355744583598139)
          ·
            refine ⟨16203718548533616875397209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802479032355744583598139 16203718548533616875397209)
            ·
              refine ⟨12152788911400212656547907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16203718548533616875397209 12152788911400212656547907)
              ·
                refine ⟨18229183367100318984821861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12152788911400212656547907 18229183367100318984821861)
                ·
                  refine ⟨3417971881331309809654099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18229183367100318984821861 3417971881331309809654099)
                  ·
                    refine ⟨5126957821996964714481149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417971881331309809654099 5126957821996964714481149)
                    ·
                      refine ⟨1922609183248861767930431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5126957821996964714481149 1922609183248861767930431)
                      ·
                        rfl

theorem cell23_3744268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_3744268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744268 prefixEnd_3744268 := by exact prefixLift 3744268
  have htrace : WordTrace (prefixWord ++ tailWord_3744268) baseStart_3744268 baseEnd_3744268 := by
    simpa [prefixWord, tailWord_3744268, baseEnd_3744268] using wordTrace_append hprefix tailTrace_3744268
  have hstable : (prefixWord ++ tailWord_3744268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744268).length < 2 ^ (prefixWord ++ tailWord_3744268).sum := by decide
  have hdescent : baseEnd_3744268 < baseStart_3744268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744269 : List Nat := [1, 7, 1, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_3744269 : Nat := 118140960795 + 3744269 * 2 ^ 59
def prefixEnd_3744269 : Nat := 4983230072969 + 3 ^ 40 * 3744269 * 2
def baseEnd_3744269 : Nat := 1922609696729516264017927

theorem tailTrace_3744269 : CollatzResearch.WordTrace tailWord_3744269 prefixEnd_3744269 1922609696729516264017927 := by
  unfold tailWord_3744269
  simp only [CollatzResearch.WordTrace]
  refine ⟨136564709672160358079483861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91043139781440238719655907 136564709672160358079483861)
  ·
    refine ⟨3200735382941258392487903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 136564709672160358079483861 3200735382941258392487903)
    ·
      refine ⟨4801103074411887588731855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200735382941258392487903 4801103074411887588731855)
      ·
        refine ⟨7201654611617831383097783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801103074411887588731855 7201654611617831383097783)
        ·
          refine ⟨10802481917426747074646675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201654611617831383097783 10802481917426747074646675)
          ·
            refine ⟨16203722876140120611970013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802481917426747074646675 16203722876140120611970013)
            ·
              refine ⟨6076396078552545229488755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16203722876140120611970013 6076396078552545229488755)
              ·
                refine ⟨9114594117828817844233133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076396078552545229488755 9114594117828817844233133)
                ·
                  refine ⟨3417972794185806691587425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9114594117828817844233133 3417972794185806691587425)
                  ·
                    refine ⟨2563479595639355018690569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3417972794185806691587425 2563479595639355018690569)
                    ·
                      refine ⟨1922609696729516264017927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563479595639355018690569 1922609696729516264017927)
                      ·
                        rfl

theorem cell23_3744269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_3744269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744269 prefixEnd_3744269 := by exact prefixLift 3744269
  have htrace : WordTrace (prefixWord ++ tailWord_3744269) baseStart_3744269 baseEnd_3744269 := by
    simpa [prefixWord, tailWord_3744269, baseEnd_3744269] using wordTrace_append hprefix tailTrace_3744269
  have hstable : (prefixWord ++ tailWord_3744269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744269).length < 2 ^ (prefixWord ++ tailWord_3744269).sum := by decide
  have hdescent : baseEnd_3744269 < baseStart_3744269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744279 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 2, 4]
def baseStart_3744279 : Nat := 118140960795 + 3744279 * 2 ^ 59
def prefixEnd_3744279 : Nat := 4983230072969 + 3 ^ 40 * 3744279 * 2
def baseEnd_3744279 : Nat := 640871610512020408297627

theorem tailTrace_3744279 : CollatzResearch.WordTrace tailWord_3744279 prefixEnd_3744279 640871610512020408297627 := by
  unfold tailWord_3744279
  simp only [CollatzResearch.WordTrace]
  refine ⟨136565074402124129787347891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91043382934749419858231927 136565074402124129787347891)
  ·
    refine ⟨204847611603186194681021837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136565074402124129787347891 204847611603186194681021837)
    ·
      refine ⟨76817854351194823005383189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204847611603186194681021837 76817854351194823005383189)
      ·
        refine ⟨3600836922712257328377337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76817854351194823005383189 3600836922712257328377337)
        ·
          refine ⟨2700627692034192996283003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3600836922712257328377337 2700627692034192996283003)
          ·
            refine ⟨4050941538051289494424505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2700627692034192996283003 4050941538051289494424505)
            ·
              refine ⟨3038206153538467120818379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4050941538051289494424505 3038206153538467120818379)
              ·
                refine ⟨4557309230307700681227569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038206153538467120818379 4557309230307700681227569)
                ·
                  refine ⟨3417981922730775510920677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557309230307700681227569 3417981922730775510920677)
                  ·
                    refine ⟨640871610512020408297627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3417981922730775510920677 640871610512020408297627)
                    ·
                      rfl

theorem cell23_3744279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_3744279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744279 prefixEnd_3744279 := by exact prefixLift 3744279
  have htrace : WordTrace (prefixWord ++ tailWord_3744279) baseStart_3744279 baseEnd_3744279 := by
    simpa [prefixWord, tailWord_3744279, baseEnd_3744279] using wordTrace_append hprefix tailTrace_3744279
  have hstable : (prefixWord ++ tailWord_3744279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744279).length < 2 ^ (prefixWord ++ tailWord_3744279).sum := by decide
  have hdescent : baseEnd_3744279 < baseStart_3744279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744285 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 3]
def baseStart_3744285 : Nat := 118140960795 + 3744285 * 2 ^ 59
def prefixEnd_3744285 : Nat := 4983230072969 + 3 ^ 40 * 3744285 * 2
def baseEnd_3744285 : Nat := 1922617912419988201417853

theorem tailTrace_3744285 : CollatzResearch.WordTrace tailWord_3744285 prefixEnd_3744285 1922617912419988201417853 := by
  unfold tailWord_3744285
  simp only [CollatzResearch.WordTrace]
  refine ⟨136565293240102392812066309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91043528826734928541377539 136565293240102392812066309)
  ·
    refine ⟨25605992482519198652262433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136565293240102392812066309 25605992482519198652262433)
    ·
      refine ⟨19204494361889398989196825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25605992482519198652262433 19204494361889398989196825)
      ·
        refine ⟨14403370771417049241897619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19204494361889398989196825 14403370771417049241897619)
        ·
          refine ⟨21605056157125573862846429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403370771417049241897619 21605056157125573862846429)
          ·
            refine ⟨8101896058922090198567411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21605056157125573862846429 8101896058922090198567411)
            ·
              refine ⟨12152844088383135297851117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101896058922090198567411 12152844088383135297851117)
              ·
                refine ⟨4557316533143675736694169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12152844088383135297851117 4557316533143675736694169)
                ·
                  refine ⟨3417987399857756802520627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557316533143675736694169 3417987399857756802520627)
                  ·
                    refine ⟨5126981099786635203780941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3417987399857756802520627 5126981099786635203780941)
                    ·
                      refine ⟨1922617912419988201417853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5126981099786635203780941 1922617912419988201417853)
                      ·
                        rfl

theorem cell23_3744285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_3744285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744285 prefixEnd_3744285 := by exact prefixLift 3744285
  have htrace : WordTrace (prefixWord ++ tailWord_3744285) baseStart_3744285 baseEnd_3744285 := by
    simpa [prefixWord, tailWord_3744285, baseEnd_3744285] using wordTrace_append hprefix tailTrace_3744285
  have hstable : (prefixWord ++ tailWord_3744285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744285).length < 2 ^ (prefixWord ++ tailWord_3744285).sum := by decide
  have hdescent : baseEnd_3744285 < baseStart_3744285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744325 : List Nat := [1, 3, 1, 1, 1, 5, 1, 4, 2, 2, 2]
def baseStart_3744325 : Nat := 118140960795 + 3744325 * 2 ^ 59
def prefixEnd_3744325 : Nat := 4983230072969 + 3 ^ 40 * 3744325 * 2
def baseEnd_3744325 : Nat := 1922638451646168044917669

theorem tailTrace_3744325 : CollatzResearch.WordTrace tailWord_3744325 prefixEnd_3744325 1922638451646168044917669 := by
  unfold tailWord_3744325
  simp only [CollatzResearch.WordTrace]
  refine ⟨136566752159957479643522429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91044501439971653095681619 136566752159957479643522429)
  ·
    refine ⟨51212532059984054866320911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136566752159957479643522429 51212532059984054866320911)
    ·
      refine ⟨76818798089976082299481367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51212532059984054866320911 76818798089976082299481367)
      ·
        refine ⟨115228197134964123449222051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76818798089976082299481367 115228197134964123449222051)
        ·
          refine ⟨172842295702446185173833077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115228197134964123449222051 172842295702446185173833077)
          ·
            refine ⟨16203965222104329860046851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172842295702446185173833077 16203965222104329860046851)
            ·
              refine ⟨24305947833156494790070277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16203965222104329860046851 24305947833156494790070277)
              ·
                refine ⟨4557365218716842773138177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24305947833156494790070277 4557365218716842773138177)
                ·
                  refine ⟨3418023914037632079853633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557365218716842773138177 3418023914037632079853633)
                  ·
                    refine ⟨2563517935528224059890225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3418023914037632079853633 2563517935528224059890225)
                    ·
                      refine ⟨1922638451646168044917669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563517935528224059890225 1922638451646168044917669)
                      ·
                        rfl

theorem cell23_3744325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_3744325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744325 prefixEnd_3744325 := by exact prefixLift 3744325
  have htrace : WordTrace (prefixWord ++ tailWord_3744325) baseStart_3744325 baseEnd_3744325 := by
    simpa [prefixWord, tailWord_3744325, baseEnd_3744325] using wordTrace_append hprefix tailTrace_3744325
  have hstable : (prefixWord ++ tailWord_3744325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744325).length < 2 ^ (prefixWord ++ tailWord_3744325).sum := by decide
  have hdescent : baseEnd_3744325 < baseStart_3744325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744341 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 3]
def baseStart_3744341 : Nat := 118140960795 + 3744341 * 2 ^ 59
def prefixEnd_3744341 : Nat := 4983230072969 + 3 ^ 40 * 3744341 * 2
def baseEnd_3744341 : Nat := 1922646667336639982317595

theorem tailTrace_3744341 : CollatzResearch.WordTrace tailWord_3744341 prefixEnd_3744341 1922646667336639982317595 := by
  unfold tailWord_3744341
  simp only [CollatzResearch.WordTrace]
  refine ⟨136567335727899514376104877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91044890485266342917403251 136567335727899514376104877)
  ·
    refine ⟨51212750897962317891039329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136567335727899514376104877 51212750897962317891039329)
    ·
      refine ⟨38409563173471738418279497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51212750897962317891039329 38409563173471738418279497)
      ·
        refine ⟨28807172380103803813709623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38409563173471738418279497 28807172380103803813709623)
        ·
          refine ⟨43210758570155705720564435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28807172380103803813709623 43210758570155705720564435)
          ·
            refine ⟨64816137855233558580846653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43210758570155705720564435 64816137855233558580846653)
            ·
              refine ⟨24306051695712584467817495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64816137855233558580846653 24306051695712584467817495)
              ·
                refine ⟨36459077543568876701726243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24306051695712584467817495 36459077543568876701726243)
                ·
                  refine ⟨54688616315353315052589365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36459077543568876701726243 54688616315353315052589365)
                  ·
                    refine ⟨5127057779564373286180253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54688616315353315052589365 5127057779564373286180253)
                    ·
                      refine ⟨1922646667336639982317595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5127057779564373286180253 1922646667336639982317595)
                      ·
                        rfl

theorem cell23_3744341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_3744341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744341 prefixEnd_3744341 := by exact prefixLift 3744341
  have htrace : WordTrace (prefixWord ++ tailWord_3744341) baseStart_3744341 baseEnd_3744341 := by
    simpa [prefixWord, tailWord_3744341, baseEnd_3744341] using wordTrace_append hprefix tailTrace_3744341
  have hstable : (prefixWord ++ tailWord_3744341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744341).length < 2 ^ (prefixWord ++ tailWord_3744341).sum := by decide
  have hdescent : baseEnd_3744341 < baseStart_3744341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744348 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 7]
def baseStart_3744348 : Nat := 118140960795 + 3744348 * 2 ^ 59
def prefixEnd_3744348 : Nat := 4983230072969 + 3 ^ 40 * 3744348 * 2
def baseEnd_3744348 : Nat := 213627806855691272770007

theorem tailTrace_3744348 : CollatzResearch.WordTrace tailWord_3744348 prefixEnd_3744348 213627806855691272770007 := by
  unfold tailWord_3744348
  simp only [CollatzResearch.WordTrace]
  refine ⟨68283795519437077285804849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91045060692582769714406465 68283795519437077285804849)
  ·
    refine ⟨51212846639577807964353637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68283795519437077285804849 51212846639577807964353637)
    ·
      refine ⟨9602408744920838993316307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51212846639577807964353637 9602408744920838993316307)
      ·
        refine ⟨14403613117381258489974461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9602408744920838993316307 14403613117381258489974461)
        ·
          refine ⟨5401354919017971933740423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14403613117381258489974461 5401354919017971933740423)
          ·
            refine ⟨8102032378526957900610635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401354919017971933740423 8102032378526957900610635)
            ·
              refine ⟨12153048567790436850915953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102032378526957900610635 12153048567790436850915953)
              ·
                refine ⟨9114786425842827638186965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12153048567790436850915953 9114786425842827638186965)
                ·
                  refine ⟨213627806855691272770007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9114786425842827638186965 213627806855691272770007)
                  ·
                    rfl

theorem cell23_3744348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 7].length) (baseStart_3744348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744348 prefixEnd_3744348 := by exact prefixLift 3744348
  have htrace : WordTrace (prefixWord ++ tailWord_3744348) baseStart_3744348 baseEnd_3744348 := by
    simpa [prefixWord, tailWord_3744348, baseEnd_3744348] using wordTrace_append hprefix tailTrace_3744348
  have hstable : (prefixWord ++ tailWord_3744348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744348).length < 2 ^ (prefixWord ++ tailWord_3744348).sum := by decide
  have hdescent : baseEnd_3744348 < baseStart_3744348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744365 : List Nat := [1, 5, 1, 1, 3, 2, 2, 3, 5]
def baseStart_3744365 : Nat := 118140960795 + 3744365 * 2 ^ 59
def prefixEnd_3744365 : Nat := 4983230072969 + 3 ^ 40 * 3744365 * 2
def baseEnd_3744365 : Nat := 213628776763594209824165

theorem tailTrace_3744365 : CollatzResearch.WordTrace tailWord_3744365 prefixEnd_3744365 213628776763594209824165 := by
  unfold tailWord_3744365
  simp only [CollatzResearch.WordTrace]
  refine ⟨136568211079812566474978549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91045474053208377649985699 136568211079812566474978549)
  ·
    refine ⟨12803269788732428107029239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 136568211079812566474978549 12803269788732428107029239)
    ·
      refine ⟨19204904683098642160543859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12803269788732428107029239 19204904683098642160543859)
      ·
        refine ⟨28807357024647963240815789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19204904683098642160543859 28807357024647963240815789)
        ·
          refine ⟨10802758884242986215305921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28807357024647963240815789 10802758884242986215305921)
          ·
            refine ⟨8102069163182239661479441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10802758884242986215305921 8102069163182239661479441)
            ·
              refine ⟨6076551872386679746109581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8102069163182239661479441 6076551872386679746109581)
              ·
                refine ⟨2278706952145004904791093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6076551872386679746109581 2278706952145004904791093)
                ·
                  refine ⟨213628776763594209824165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2278706952145004904791093 213628776763594209824165)
                  ·
                    rfl

theorem cell23_3744365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_3744365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744365 prefixEnd_3744365 := by exact prefixLift 3744365
  have htrace : WordTrace (prefixWord ++ tailWord_3744365) baseStart_3744365 baseEnd_3744365 := by
    simpa [prefixWord, tailWord_3744365, baseEnd_3744365] using wordTrace_append hprefix tailTrace_3744365
  have hstable : (prefixWord ++ tailWord_3744365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744365).length < 2 ^ (prefixWord ++ tailWord_3744365).sum := by decide
  have hdescent : baseEnd_3744365 < baseStart_3744365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744408 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 3, 4]
def baseStart_3744408 : Nat := 118140960795 + 3744408 * 2 ^ 59
def prefixEnd_3744408 : Nat := 4983230072969 + 3 ^ 40 * 3744408 * 2
def baseEnd_3744408 : Nat := 640893690180163740059929

theorem tailTrace_3744408 : CollatzResearch.WordTrace tailWord_3744408 prefixEnd_3744408 640893690180163740059929 := by
  unfold tailWord_3744408
  simp only [CollatzResearch.WordTrace]
  refine ⟨68284889709328392409396939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91046519612437856545862585 68284889709328392409396939)
  ·
    refine ⟨102427334563992588614095409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68284889709328392409396939 102427334563992588614095409)
    ·
      refine ⟨76820500922994441460571557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102427334563992588614095409 76820500922994441460571557)
      ·
        refine ⟨14403843923061457773857167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76820500922994441460571557 14403843923061457773857167)
        ·
          refine ⟨21605765884592186660785751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14403843923061457773857167 21605765884592186660785751)
          ·
            refine ⟨32408648826888279991178627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21605765884592186660785751 32408648826888279991178627)
            ·
              refine ⟨48612973240332419986767941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32408648826888279991178627 48612973240332419986767941)
              ·
                refine ⟨9114932482562328747518989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48612973240332419986767941 9114932482562328747518989)
                ·
                  refine ⟨3418099680960873280319621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9114932482562328747518989 3418099680960873280319621)
                  ·
                    refine ⟨640893690180163740059929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418099680960873280319621 640893690180163740059929)
                    ·
                      rfl

theorem cell23_3744408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3, 4].length) (baseStart_3744408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744408 prefixEnd_3744408 := by exact prefixLift 3744408
  have htrace : WordTrace (prefixWord ++ tailWord_3744408) baseStart_3744408 baseEnd_3744408 := by
    simpa [prefixWord, tailWord_3744408, baseEnd_3744408] using wordTrace_append hprefix tailTrace_3744408
  have hstable : (prefixWord ++ tailWord_3744408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744408).length < 2 ^ (prefixWord ++ tailWord_3744408).sum := by decide
  have hdescent : baseEnd_3744408 < baseStart_3744408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744442 : List Nat := [3, 1, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_3744442 : Nat := 118140960795 + 3744442 * 2 ^ 59
def prefixEnd_3744442 : Nat := 4983230072969 + 3 ^ 40 * 3744442 * 2
def baseEnd_3744442 : Nat := 640899509627581362384877

theorem tailTrace_3744442 : CollatzResearch.WordTrace tailWord_3744442 prefixEnd_3744442 640899509627581362384877 := by
  unfold tailWord_3744442
  simp only [CollatzResearch.WordTrace]
  refine ⟨34142754875133402156382895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91047346333689072417021053 34142754875133402156382895)
  ·
    refine ⟨51214132312700103234574343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34142754875133402156382895 51214132312700103234574343)
    ·
      refine ⟨76821198469050154851861515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51214132312700103234574343 76821198469050154851861515)
      ·
        refine ⟨115231797703575232277792273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76821198469050154851861515 115231797703575232277792273)
        ·
          refine ⟨86423848277681424208344205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115231797703575232277792273 86423848277681424208344205)
          ·
            refine ⟨32408943104130534078129077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86423848277681424208344205 32408943104130534078129077)
            ·
              refine ⟨3038338416012237569824601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32408943104130534078129077 3038338416012237569824601)
              ·
                refine ⟨2278753812009178177368451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3038338416012237569824601 2278753812009178177368451)
                ·
                  refine ⟨3418130718013767266052677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278753812009178177368451 3418130718013767266052677)
                  ·
                    refine ⟨640899509627581362384877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418130718013767266052677 640899509627581362384877)
                    ·
                      rfl

theorem cell23_3744442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_3744442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744442 prefixEnd_3744442 := by exact prefixLift 3744442
  have htrace : WordTrace (prefixWord ++ tailWord_3744442) baseStart_3744442 baseEnd_3744442 := by
    simpa [prefixWord, tailWord_3744442, baseEnd_3744442] using wordTrace_append hprefix tailTrace_3744442
  have hstable : (prefixWord ++ tailWord_3744442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744442).length < 2 ^ (prefixWord ++ tailWord_3744442).sum := by decide
  have hdescent : baseEnd_3744442 < baseStart_3744442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744505 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 7, 2, 2]
def baseStart_3744505 : Nat := 118140960795 + 3744505 * 2 ^ 59
def prefixEnd_3744505 : Nat := 4983230072969 + 3 ^ 40 * 3744505 * 2
def baseEnd_3744505 : Nat := 1922730878163977340666841

theorem tailTrace_3744505 : CollatzResearch.WordTrace tailWord_3744505 prefixEnd_3744505 1922730878163977340666841 := by
  unfold tailWord_3744505
  simp only [CollatzResearch.WordTrace]
  refine ⟨136573317299305370385074969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91048878199536913590049979 136573317299305370385074969)
  ·
    refine ⟨102429987974479027788806227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136573317299305370385074969 102429987974479027788806227)
    ·
      refine ⟨153644981961718541683209341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102429987974479027788806227 153644981961718541683209341)
      ·
        refine ⟨57616868235644453131203503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153644981961718541683209341 57616868235644453131203503)
        ·
          refine ⟨86425302353466679696805255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57616868235644453131203503 86425302353466679696805255)
          ·
            refine ⟨129637953530200019545207883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86425302353466679696805255 129637953530200019545207883)
            ·
              refine ⟨194456930295300029317811825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129637953530200019545207883 194456930295300029317811825)
              ·
                refine ⟨145842697721475021988358869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194456930295300029317811825 145842697721475021988358869)
                ·
                  refine ⟨3418188227847070827852161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 145842697721475021988358869 3418188227847070827852161)
                  ·
                    refine ⟨2563641170885303120889121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3418188227847070827852161 2563641170885303120889121)
                    ·
                      refine ⟨1922730878163977340666841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563641170885303120889121 1922730878163977340666841)
                      ·
                        rfl

theorem cell23_3744505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_3744505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744505 prefixEnd_3744505 := by exact prefixLift 3744505
  have htrace : WordTrace (prefixWord ++ tailWord_3744505) baseStart_3744505 baseEnd_3744505 := by
    simpa [prefixWord, tailWord_3744505, baseEnd_3744505] using wordTrace_append hprefix tailTrace_3744505
  have hstable : (prefixWord ++ tailWord_3744505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744505).length < 2 ^ (prefixWord ++ tailWord_3744505).sum := by decide
  have hdescent : baseEnd_3744505 < baseStart_3744505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744522 : List Nat := [3, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_3744522 : Nat := 118140960795 + 3744522 * 2 ^ 59
def prefixEnd_3744522 : Nat := 4983230072969 + 3 ^ 40 * 3744522 * 2
def baseEnd_3744522 : Nat := 1922739607335103774154263

theorem tailTrace_3744522 : CollatzResearch.WordTrace tailWord_3744522 prefixEnd_3744522 1922739607335103774154263 := by
  unfold tailWord_3744522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34143484335060945572110955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91049291560162521525629213 34143484335060945572110955)
  ·
    refine ⟨51215226502591418358166433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34143484335060945572110955 51215226502591418358166433)
    ·
      refine ⟨38411419876943563768624825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51215226502591418358166433 38411419876943563768624825)
      ·
        refine ⟨28808564907707672826468619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38411419876943563768624825 28808564907707672826468619)
        ·
          refine ⟨43212847361561509239702929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28808564907707672826468619 43212847361561509239702929)
          ·
            refine ⟨32409635521171131929777197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43212847361561509239702929 32409635521171131929777197)
            ·
              refine ⟨12153613320439174473666449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32409635521171131929777197 12153613320439174473666449)
              ·
                refine ⟨9115209990329380855249837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12153613320439174473666449 9115209990329380855249837)
                ·
                  refine ⟨3418203746373517820718689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9115209990329380855249837 3418203746373517820718689)
                  ·
                    refine ⟨2563652809780138365539017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3418203746373517820718689 2563652809780138365539017)
                    ·
                      refine ⟨1922739607335103774154263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563652809780138365539017 1922739607335103774154263)
                      ·
                        rfl

theorem cell23_3744522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_3744522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744522 prefixEnd_3744522 := by exact prefixLift 3744522
  have htrace : WordTrace (prefixWord ++ tailWord_3744522) baseStart_3744522 baseEnd_3744522 := by
    simpa [prefixWord, tailWord_3744522, baseEnd_3744522] using wordTrace_append hprefix tailTrace_3744522
  have hstable : (prefixWord ++ tailWord_3744522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744522).length < 2 ^ (prefixWord ++ tailWord_3744522).sum := by decide
  have hdescent : baseEnd_3744522 < baseStart_3744522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744566 : List Nat := [5, 1, 2, 2, 2, 1, 3, 1, 2, 4]
def baseStart_3744566 : Nat := 118140960795 + 3744566 * 2 ^ 59
def prefixEnd_3744566 : Nat := 4983230072969 + 3 ^ 40 * 3744566 * 2
def baseEnd_3744566 : Nat := 640920733494633867334687

theorem tailTrace_3744566 : CollatzResearch.WordTrace tailWord_3744566 prefixEnd_3744566 640920733494633867334687 := by
  unfold tailWord_3744566
  simp only [CollatzResearch.WordTrace]
  refine ⟨8535971384505273612690347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91050361434722918535363701 8535971384505273612690347)
  ·
    refine ⟨12803957076757910419035521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8535971384505273612690347 12803957076757910419035521)
    ·
      refine ⟨9602967807568432814276641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12803957076757910419035521 9602967807568432814276641)
      ·
        refine ⟨7202225855676324610707481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9602967807568432814276641 7202225855676324610707481)
        ·
          refine ⟨5401669391757243458030611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7202225855676324610707481 5401669391757243458030611)
          ·
            refine ⟨8102504087635865187045917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401669391757243458030611 8102504087635865187045917)
            ·
              refine ⟨3038439032863449445142219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8102504087635865187045917 3038439032863449445142219)
              ·
                refine ⟨4557658549295174167713329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038439032863449445142219 4557658549295174167713329)
                ·
                  refine ⟨3418243911971380625784997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4557658549295174167713329 3418243911971380625784997)
                  ·
                    refine ⟨640920733494633867334687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418243911971380625784997 640920733494633867334687)
                    ·
                      rfl

theorem cell23_3744566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_3744566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744566 prefixEnd_3744566 := by exact prefixLift 3744566
  have htrace : WordTrace (prefixWord ++ tailWord_3744566) baseStart_3744566 baseEnd_3744566 := by
    simpa [prefixWord, tailWord_3744566, baseEnd_3744566] using wordTrace_append hprefix tailTrace_3744566
  have hstable : (prefixWord ++ tailWord_3744566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744566).length < 2 ^ (prefixWord ++ tailWord_3744566).sum := by decide
  have hdescent : baseEnd_3744566 < baseStart_3744566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744595 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 1, 4, 2]
def baseStart_3744595 : Nat := 118140960795 + 3744595 * 2 ^ 59
def prefixEnd_3744595 : Nat := 4983230072969 + 3 ^ 40 * 3744595 * 2
def baseEnd_3744595 : Nat := 1922777091422881988541427

theorem tailTrace_3744595 : CollatzResearch.WordTrace tailWord_3744595 prefixEnd_3744595 1922777091422881988541427 := by
  unfold tailWord_3744595
  simp only [CollatzResearch.WordTrace]
  refine ⟨136576599868979315755851239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91051066579319543837234159 136576599868979315755851239)
  ·
    refine ⟨204864899803468973633776859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136576599868979315755851239 204864899803468973633776859)
    ·
      refine ⟨307297349705203460450665289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204864899803468973633776859 307297349705203460450665289)
      ·
        refine ⟨230473012278902595337998967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307297349705203460450665289 230473012278902595337998967)
        ·
          refine ⟨345709518418353893006998451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230473012278902595337998967 345709518418353893006998451)
          ·
            refine ⟨518564277627530839510497677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345709518418353893006998451 518564277627530839510497677)
            ·
              refine ⟨194461604110324064816436629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 518564277627530839510497677 194461604110324064816436629)
              ·
                refine ⟨9115387692671440538270467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 194461604110324064816436629 9115387692671440538270467)
                ·
                  refine ⟨13673081539007160807405701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115387692671440538270467 13673081539007160807405701)
                  ·
                    refine ⟨2563702788563842651388569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13673081539007160807405701 2563702788563842651388569)
                    ·
                      refine ⟨1922777091422881988541427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563702788563842651388569 1922777091422881988541427)
                      ·
                        rfl

theorem cell23_3744595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 4, 2].length) (baseStart_3744595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744595 prefixEnd_3744595 := by exact prefixLift 3744595
  have htrace : WordTrace (prefixWord ++ tailWord_3744595) baseStart_3744595 baseEnd_3744595 := by
    simpa [prefixWord, tailWord_3744595, baseEnd_3744595] using wordTrace_append hprefix tailTrace_3744595
  have hstable : (prefixWord ++ tailWord_3744595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744595).length < 2 ^ (prefixWord ++ tailWord_3744595).sum := by decide
  have hdescent : baseEnd_3744595 < baseStart_3744595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744695 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 5, 4]
def baseStart_3744695 : Nat := 118140960795 + 3744695 * 2 ^ 59
def prefixEnd_3744695 : Nat := 4983230072969 + 3 ^ 40 * 3744695 * 2
def baseEnd_3744695 : Nat := 640942813162777199096989

theorem tailTrace_3744695 : CollatzResearch.WordTrace tailWord_3744695 prefixEnd_3744695 640942813162777199096989 := by
  unfold tailWord_3744695
  simp only [CollatzResearch.WordTrace]
  refine ⟨136580247168617032834491539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91053498112411355222994359 136580247168617032834491539)
  ·
    refine ⟨204870370752925549251737309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136580247168617032834491539 204870370752925549251737309)
    ·
      refine ⟨76826389032347080969401491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204870370752925549251737309 76826389032347080969401491)
      ·
        refine ⟨115239583548520621454102237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76826389032347080969401491 115239583548520621454102237)
        ·
          refine ⟨43214843830695233045288339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115239583548520621454102237 43214843830695233045288339)
          ·
            refine ⟨64822265746042849567932509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43214843830695233045288339 64822265746042849567932509)
            ·
              refine ⟨24308349654766068587974691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64822265746042849567932509 24308349654766068587974691)
              ·
                refine ⟨36462524482149102881962037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24308349654766068587974691 36462524482149102881962037)
                ·
                  refine ⟨3418361670201478395183941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36462524482149102881962037 3418361670201478395183941)
                  ·
                    refine ⟨640942813162777199096989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418361670201478395183941 640942813162777199096989)
                    ·
                      rfl

theorem cell23_3744695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_3744695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744695 prefixEnd_3744695 := by exact prefixLift 3744695
  have htrace : WordTrace (prefixWord ++ tailWord_3744695) baseStart_3744695 baseEnd_3744695 := by
    simpa [prefixWord, tailWord_3744695, baseEnd_3744695] using wordTrace_append hprefix tailTrace_3744695
  have hstable : (prefixWord ++ tailWord_3744695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744695).length < 2 ^ (prefixWord ++ tailWord_3744695).sum := by decide
  have hdescent : baseEnd_3744695 < baseStart_3744695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744702 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_3744702 : Nat := 118140960795 + 3744702 * 2 ^ 59
def prefixEnd_3744702 : Nat := 4983230072969 + 3 ^ 40 * 3744702 * 2
def baseEnd_3744702 : Nat := 1922832033852913069903435

theorem tailTrace_3744702 : CollatzResearch.WordTrace tailWord_3744702 prefixEnd_3744702 1922832033852913069903435 := by
  unfold tailWord_3744702
  simp only [CollatzResearch.WordTrace]
  refine ⟨17072562809948959128749545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91053668319727782019997573 17072562809948959128749545)
  ·
    refine ⟨12804422107461719346562159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17072562809948959128749545 12804422107461719346562159)
    ·
      refine ⟨19206633161192579019843239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12804422107461719346562159 19206633161192579019843239)
      ·
        refine ⟨28809949741788868529764859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19206633161192579019843239 28809949741788868529764859)
        ·
          refine ⟨43214924612683302794647289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28809949741788868529764859 43214924612683302794647289)
          ·
            refine ⟨32411193459512477095985467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43214924612683302794647289 32411193459512477095985467)
            ·
              refine ⟨48616790189268715643978201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32411193459512477095985467 48616790189268715643978201)
              ·
                refine ⟨36462592641951536732983651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48616790189268715643978201 36462592641951536732983651)
                ·
                  refine ⟨54693888962927305099475477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36462592641951536732983651 54693888962927305099475477)
                  ·
                    refine ⟨2563776045137217426537913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54693888962927305099475477 2563776045137217426537913)
                    ·
                      refine ⟨1922832033852913069903435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563776045137217426537913 1922832033852913069903435)
                      ·
                        rfl

theorem cell23_3744702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_3744702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744702 prefixEnd_3744702 := by exact prefixLift 3744702
  have htrace : WordTrace (prefixWord ++ tailWord_3744702) baseStart_3744702 baseEnd_3744702 := by
    simpa [prefixWord, tailWord_3744702, baseEnd_3744702] using wordTrace_append hprefix tailTrace_3744702
  have hstable : (prefixWord ++ tailWord_3744702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744702).length < 2 ^ (prefixWord ++ tailWord_3744702).sum := by decide
  have hdescent : baseEnd_3744702 < baseStart_3744702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744729 : List Nat := [1, 2, 1, 2, 5, 1, 2, 4, 1, 4]
def baseStart_3744729 : Nat := 118140960795 + 3744729 * 2 ^ 59
def prefixEnd_3744729 : Nat := 4983230072969 + 3 ^ 40 * 3744729 * 2
def baseEnd_3744729 : Nat := 640948632610194821421937

theorem tailTrace_3744729 : CollatzResearch.WordTrace tailWord_3744729 prefixEnd_3744729 640948632610194821421937 := by
  unfold tailWord_3744729
  simp only [CollatzResearch.WordTrace]
  refine ⟨136581487250493856641229241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91054324833662571094152827 136581487250493856641229241)
  ·
    refine ⟨102436115437870392480921931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136581487250493856641229241 102436115437870392480921931)
    ·
      refine ⟨153654173156805588721382897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102436115437870392480921931 153654173156805588721382897)
      ·
        refine ⟨115240629867604191541037173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153654173156805588721382897 115240629867604191541037173)
        ·
          refine ⟨10803809050087892956972235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115240629867604191541037173 10803809050087892956972235)
          ·
            refine ⟨16205713575131839435458353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10803809050087892956972235 16205713575131839435458353)
            ·
              refine ⟨12154285181348879576593765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16205713575131839435458353 12154285181348879576593765)
              ·
                refine ⟨2278928471502914920611331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12154285181348879576593765 2278928471502914920611331)
                ·
                  refine ⟨3418392707254372380916997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2278928471502914920611331 3418392707254372380916997)
                  ·
                    refine ⟨640948632610194821421937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3418392707254372380916997 640948632610194821421937)
                    ·
                      rfl

theorem cell23_3744729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 4, 1, 4].length) (baseStart_3744729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744729 prefixEnd_3744729 := by exact prefixLift 3744729
  have htrace : WordTrace (prefixWord ++ tailWord_3744729) baseStart_3744729 baseEnd_3744729 := by
    simpa [prefixWord, tailWord_3744729, baseEnd_3744729] using wordTrace_append hprefix tailTrace_3744729
  have hstable : (prefixWord ++ tailWord_3744729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744729).length < 2 ^ (prefixWord ++ tailWord_3744729).sum := by decide
  have hdescent : baseEnd_3744729 < baseStart_3744729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744762 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2]
def baseStart_3744762 : Nat := 118140960795 + 3744762 * 2 ^ 59
def prefixEnd_3744762 : Nat := 4983230072969 + 3 ^ 40 * 3744762 * 2
def baseEnd_3744762 : Nat := 1922862842692182835153159

theorem tailTrace_3744762 : CollatzResearch.WordTrace tailWord_3744762 prefixEnd_3744762 1922862842692182835153159 := by
  unfold tailWord_3744762
  simp only [CollatzResearch.WordTrace]
  refine ⟨34145672714843575819295135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91055127239582868851453693 34145672714843575819295135)
  ·
    refine ⟨51218509072265363728942703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34145672714843575819295135 51218509072265363728942703)
    ·
      refine ⟨76827763608398045593414055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51218509072265363728942703 76827763608398045593414055)
      ·
        refine ⟨115241645412597068390121083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76827763608398045593414055 115241645412597068390121083)
        ·
          refine ⟨172862468118895602585181625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115241645412597068390121083 172862468118895602585181625)
          ·
            refine ⟨129646851089171701938886219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172862468118895602585181625 129646851089171701938886219)
            ·
              refine ⟨194470276633757552908329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129646851089171701938886219 194470276633757552908329329)
              ·
                refine ⟨145852707475318164681246997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194470276633757552908329329 145852707475318164681246997)
                ·
                  refine ⟨6836845662905538969433453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145852707475318164681246997 6836845662905538969433453)
                  ·
                    refine ⟨2563817123589577113537545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6836845662905538969433453 2563817123589577113537545)
                    ·
                      refine ⟨1922862842692182835153159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563817123589577113537545 1922862842692182835153159)
                      ·
                        rfl

theorem cell23_3744762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2].length) (baseStart_3744762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744762 prefixEnd_3744762 := by exact prefixLift 3744762
  have htrace : WordTrace (prefixWord ++ tailWord_3744762) baseStart_3744762 baseEnd_3744762 := by
    simpa [prefixWord, tailWord_3744762, baseEnd_3744762] using wordTrace_append hprefix tailTrace_3744762
  have hstable : (prefixWord ++ tailWord_3744762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744762).length < 2 ^ (prefixWord ++ tailWord_3744762).sum := by decide
  have hdescent : baseEnd_3744762 < baseStart_3744762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744779 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 2, 3, 2]
def baseStart_3744779 : Nat := 118140960795 + 3744779 * 2 ^ 59
def prefixEnd_3744779 : Nat := 4983230072969 + 3 ^ 40 * 3744779 * 2
def baseEnd_3744779 : Nat := 1922871571863309268640581

theorem tailTrace_3744779 : CollatzResearch.WordTrace tailWord_3744779 prefixEnd_3744779 1922871571863309268640581 := by
  unfold tailWord_3744779
  simp only [CollatzResearch.WordTrace]
  refine ⟨136583310900312715180549391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91055540600208476787032927 136583310900312715180549391)
  ·
    refine ⟨204874966350469072770824087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136583310900312715180549391 204874966350469072770824087)
    ·
      refine ⟨307312449525703609156236131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204874966350469072770824087 307312449525703609156236131)
      ·
        refine ⟨460968674288555413734354197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307312449525703609156236131 460968674288555413734354197)
        ·
          refine ⟨21607906607276035018797853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 460968674288555413734354197 21607906607276035018797853)
          ·
            refine ⟨8102964977728513132049195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21607906607276035018797853 8102964977728513132049195)
            ·
              refine ⟨12154447466592769698073793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102964977728513132049195 12154447466592769698073793)
              ·
                refine ⟨9115835599944577273555345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12154447466592769698073793 9115835599944577273555345)
                ·
                  refine ⟨6836876699958432955166509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9115835599944577273555345 6836876699958432955166509)
                  ·
                    refine ⟨2563828762484412358187441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6836876699958432955166509 2563828762484412358187441)
                    ·
                      refine ⟨1922871571863309268640581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563828762484412358187441 1922871571863309268640581)
                      ·
                        rfl

theorem cell23_3744779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 2, 3, 2].length) (baseStart_3744779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744779 prefixEnd_3744779 := by exact prefixLift 3744779
  have htrace : WordTrace (prefixWord ++ tailWord_3744779) baseStart_3744779 baseEnd_3744779 := by
    simpa [prefixWord, tailWord_3744779, baseEnd_3744779] using wordTrace_append hprefix tailTrace_3744779
  have hstable : (prefixWord ++ tailWord_3744779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744779).length < 2 ^ (prefixWord ++ tailWord_3744779).sum := by decide
  have hdescent : baseEnd_3744779 < baseStart_3744779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744805 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_3744805 : Nat := 118140960795 + 3744805 * 2 ^ 59
def prefixEnd_3744805 : Nat := 4983230072969 + 3 ^ 40 * 3744805 * 2
def baseEnd_3744805 : Nat := 1922884922360326166915461

theorem tailTrace_3744805 : CollatzResearch.WordTrace tailWord_3744805 prefixEnd_3744805 1922884922360326166915461 := by
  unfold tailWord_3744805
  simp only [CollatzResearch.WordTrace]
  refine ⟨136584259198218521620995869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91056172798812347747330579 136584259198218521620995869)
  ·
    refine ⟨51219097199331945607873451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136584259198218521620995869 51219097199331945607873451)
    ·
      refine ⟨76828645798997918411810177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51219097199331945607873451 76828645798997918411810177)
      ·
        refine ⟨57621484349248438808857633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76828645798997918411810177 57621484349248438808857633)
        ·
          refine ⟨43216113261936329106643225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57621484349248438808857633 43216113261936329106643225)
          ·
            refine ⟨32412084946452246829982419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43216113261936329106643225 32412084946452246829982419)
            ·
              refine ⟨48618127419678370244973629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32412084946452246829982419 48618127419678370244973629)
              ·
                refine ⟨18231797782379388841865111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48618127419678370244973629 18231797782379388841865111)
                ·
                  refine ⟨27347696673569083262797667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18231797782379388841865111 27347696673569083262797667)
                  ·
                    refine ⟨41021545010353624894196501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27347696673569083262797667 41021545010353624894196501)
                    ·
                      refine ⟨1922884922360326166915461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41021545010353624894196501 1922884922360326166915461)
                      ·
                        rfl

theorem cell23_3744805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_3744805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744805 prefixEnd_3744805 := by exact prefixLift 3744805
  have htrace : WordTrace (prefixWord ++ tailWord_3744805) baseStart_3744805 baseEnd_3744805 := by
    simpa [prefixWord, tailWord_3744805, baseEnd_3744805] using wordTrace_append hprefix tailTrace_3744805
  have hstable : (prefixWord ++ tailWord_3744805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744805).length < 2 ^ (prefixWord ++ tailWord_3744805).sum := by decide
  have hdescent : baseEnd_3744805 < baseStart_3744805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744812 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_3744812 : Nat := 118140960795 + 3744812 * 2 ^ 59
def prefixEnd_3744812 : Nat := 4983230072969 + 3 ^ 40 * 3744812 * 2
def baseEnd_3744812 : Nat := 1922888516724907639527929

theorem tailTrace_3744812 : CollatzResearch.WordTrace tailWord_3744812 prefixEnd_3744812 1922888516724907639527929 := by
  unfold tailWord_3744812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68292257254596580908250345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91056343006128774544333793 68292257254596580908250345)
  ·
    refine ⟨51219192940947435681187759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68292257254596580908250345 51219192940947435681187759)
    ·
      refine ⟨76828789411421153521781639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51219192940947435681187759 76828789411421153521781639)
      ·
        refine ⟨115243184117131730282672459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76828789411421153521781639 115243184117131730282672459)
        ·
          refine ⟨172864776175697595424008689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115243184117131730282672459 172864776175697595424008689)
          ·
            refine ⟨129648582131773196568006517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172864776175697595424008689 129648582131773196568006517)
            ·
              refine ⟨12154554574853737178250611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129648582131773196568006517 12154554574853737178250611)
              ·
                refine ⟨18231831862280605767375917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12154554574853737178250611 18231831862280605767375917)
                ·
                  refine ⟨6836936948355227162765969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18231831862280605767375917 6836936948355227162765969)
                  ·
                    refine ⟨5127702711266420372074477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6836936948355227162765969 5127702711266420372074477)
                    ·
                      refine ⟨1922888516724907639527929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5127702711266420372074477 1922888516724907639527929)
                      ·
                        rfl

theorem cell23_3744812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_3744812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744812 prefixEnd_3744812 := by exact prefixLift 3744812
  have htrace : WordTrace (prefixWord ++ tailWord_3744812) baseStart_3744812 baseEnd_3744812 := by
    simpa [prefixWord, tailWord_3744812, baseEnd_3744812] using wordTrace_append hprefix tailTrace_3744812
  have hstable : (prefixWord ++ tailWord_3744812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744812).length < 2 ^ (prefixWord ++ tailWord_3744812).sum := by decide
  have hdescent : baseEnd_3744812 < baseStart_3744812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744829 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3744829 : Nat := 118140960795 + 3744829 * 2 ^ 59
def prefixEnd_3744829 : Nat := 4983230072969 + 3 ^ 40 * 3744829 * 2
def baseEnd_3744829 : Nat := 1922897245896034073015351

theorem tailTrace_3744829 : CollatzResearch.WordTrace tailWord_3744829 prefixEnd_3744829 1922897245896034073015351 := by
  unfold tailWord_3744829
  simp only [CollatzResearch.WordTrace]
  refine ⟨136585134550131573719869541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91056756366754382479913027 136585134550131573719869541)
  ·
    refine ⟨25609712728149670072475539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136585134550131573719869541 25609712728149670072475539)
    ·
      refine ⟨38414569092224505108713309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25609712728149670072475539 38414569092224505108713309)
      ·
        refine ⟨14405463409584189415767491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38414569092224505108713309 14405463409584189415767491)
        ·
          refine ⟨21608195114376284123651237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14405463409584189415767491 21608195114376284123651237)
          ·
            refine ⟨4051536583945553273184607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21608195114376284123651237 4051536583945553273184607)
            ·
              refine ⟨6077304875918329909776911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051536583945553273184607 6077304875918329909776911)
              ·
                refine ⟨9115957313877494864665367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077304875918329909776911 9115957313877494864665367)
                ·
                  refine ⟨13673935970816242296998051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9115957313877494864665367 13673935970816242296998051)
                  ·
                    refine ⟨20510903956224363445497077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13673935970816242296998051 20510903956224363445497077)
                    ·
                      refine ⟨1922897245896034073015351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20510903956224363445497077 1922897245896034073015351)
                      ·
                        rfl

theorem cell23_3744829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3744829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744829 prefixEnd_3744829 := by exact prefixLift 3744829
  have htrace : WordTrace (prefixWord ++ tailWord_3744829) baseStart_3744829 baseEnd_3744829 := by
    simpa [prefixWord, tailWord_3744829, baseEnd_3744829] using wordTrace_append hprefix tailTrace_3744829
  have hstable : (prefixWord ++ tailWord_3744829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744829).length < 2 ^ (prefixWord ++ tailWord_3744829).sum := by decide
  have hdescent : baseEnd_3744829 < baseStart_3744829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744855 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_3744855 : Nat := 118140960795 + 3744855 * 2 ^ 59
def prefixEnd_3744855 : Nat := 4983230072969 + 3 ^ 40 * 3744855 * 2
def baseEnd_3744855 : Nat := 1922910596393050971290231

theorem tailTrace_3744855 : CollatzResearch.WordTrace tailWord_3744855 prefixEnd_3744855 1922910596393050971290231 := by
  unfold tailWord_3744855
  simp only [CollatzResearch.WordTrace]
  refine ⟨136586082848037380160316019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91057388565358253440210679 136586082848037380160316019)
  ·
    refine ⟨204879124272056070240474029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136586082848037380160316019 204879124272056070240474029)
    ·
      refine ⟨76829671602021026340177761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204879124272056070240474029 76829671602021026340177761)
      ·
        refine ⟨57622253701515769755133321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76829671602021026340177761 57622253701515769755133321)
        ·
          refine ⟨43216690276136827316349991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57622253701515769755133321 43216690276136827316349991)
          ·
            refine ⟨64825035414205240974524987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43216690276136827316349991 64825035414205240974524987)
            ·
              refine ⟨97237553121307861461787481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64825035414205240974524987 97237553121307861461787481)
              ·
                refine ⟨72928164840980896096340611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97237553121307861461787481 72928164840980896096340611)
                ·
                  refine ⟨109392247261471344144510917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72928164840980896096340611 109392247261471344144510917)
                  ·
                    refine ⟨20511046361525877027095797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109392247261471344144510917 20511046361525877027095797)
                    ·
                      refine ⟨1922910596393050971290231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20511046361525877027095797 1922910596393050971290231)
                      ·
                        rfl

theorem cell23_3744855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_3744855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744855 prefixEnd_3744855 := by exact prefixLift 3744855
  have htrace : WordTrace (prefixWord ++ tailWord_3744855) baseStart_3744855 baseEnd_3744855 := by
    simpa [prefixWord, tailWord_3744855, baseEnd_3744855] using wordTrace_append hprefix tailTrace_3744855
  have hstable : (prefixWord ++ tailWord_3744855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744855).length < 2 ^ (prefixWord ++ tailWord_3744855).sum := by decide
  have hdescent : baseEnd_3744855 < baseStart_3744855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3744869 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 3, 3, 2]
def baseStart_3744869 : Nat := 118140960795 + 3744869 * 2 ^ 59
def prefixEnd_3744869 : Nat := 4983230072969 + 3 ^ 40 * 3744869 * 2
def baseEnd_3744869 : Nat := 1922917785122213916515167

theorem tailTrace_3744869 : CollatzResearch.WordTrace tailWord_3744869 prefixEnd_3744869 1922917785122213916515167 := by
  unfold tailWord_3744869
  simp only [CollatzResearch.WordTrace]
  refine ⟨136586593469986660551325661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91057728979991107034217107 136586593469986660551325661)
  ·
    refine ⟨51219972551244997706747123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136586593469986660551325661 51219972551244997706747123)
    ·
      refine ⟨76829958826867496560120685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51219972551244997706747123 76829958826867496560120685)
      ·
        refine ⟨28811234560075311210045257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76829958826867496560120685 28811234560075311210045257)
        ·
          refine ⟨21608425920056483407533943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28811234560075311210045257 21608425920056483407533943)
          ·
            refine ⟨32412638880084725111300915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21608425920056483407533943 32412638880084725111300915)
            ·
              refine ⟨48618958320127087666951373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32412638880084725111300915 48618958320127087666951373)
              ·
                refine ⟨18232109370047657875106765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48618958320127087666951373 18232109370047657875106765)
                ·
                  refine ⟨6837041013767871703165037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18232109370047657875106765 6837041013767871703165037)
                  ·
                    refine ⟨2563890380162951888686889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6837041013767871703165037 2563890380162951888686889)
                    ·
                      refine ⟨1922917785122213916515167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2563890380162951888686889 1922917785122213916515167)
                      ·
                        rfl

theorem cell23_3744869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_3744869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3744869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3744869 prefixEnd_3744869 := by exact prefixLift 3744869
  have htrace : WordTrace (prefixWord ++ tailWord_3744869) baseStart_3744869 baseEnd_3744869 := by
    simpa [prefixWord, tailWord_3744869, baseEnd_3744869] using wordTrace_append hprefix tailTrace_3744869
  have hstable : (prefixWord ++ tailWord_3744869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3744869).length < 2 ^ (prefixWord ++ tailWord_3744869).sum := by decide
  have hdescent : baseEnd_3744869 < baseStart_3744869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3744869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745073 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 3]
def baseStart_3745073 : Nat := 118140960795 + 3745073 * 2 ^ 59
def prefixEnd_3745073 : Nat := 4983230072969 + 3 ^ 40 * 3745073 * 2
def baseEnd_3745073 : Nat := 1923022535175731118364229

theorem tailTrace_3745073 : CollatzResearch.WordTrace tailWord_3745073 prefixEnd_3745073 1923022535175731118364229 := by
  unfold tailWord_3745073
  simp only [CollatzResearch.WordTrace]
  refine ⟨136594033961247603391751873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91062689307498402261167915 136594033961247603391751873)
  ·
    refine ⟨102445525470935702543813905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136594033961247603391751873 102445525470935702543813905)
    ·
      refine ⟨76834144103201776907860429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102445525470935702543813905 76834144103201776907860429)
      ·
        refine ⟨28812804038700666340447661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76834144103201776907860429 28812804038700666340447661)
        ·
          refine ⟨10804801514512749877667873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28812804038700666340447661 10804801514512749877667873)
          ·
            refine ⟨8103601135884562408250905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10804801514512749877667873 8103601135884562408250905)
            ·
              refine ⟨6077700851913421806188179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8103601135884562408250905 6077700851913421806188179)
              ·
                refine ⟨9116551277870132709282269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077700851913421806188179 9116551277870132709282269)
                ·
                  refine ⟨3418706729201299765980851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9116551277870132709282269 3418706729201299765980851)
                  ·
                    refine ⟨5128060093801949648971277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3418706729201299765980851 5128060093801949648971277)
                    ·
                      refine ⟨1923022535175731118364229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128060093801949648971277 1923022535175731118364229)
                      ·
                        rfl

theorem cell23_3745073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_3745073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745073 prefixEnd_3745073 := by exact prefixLift 3745073
  have htrace : WordTrace (prefixWord ++ tailWord_3745073) baseStart_3745073 baseEnd_3745073 := by
    simpa [prefixWord, tailWord_3745073, baseEnd_3745073] using wordTrace_append hprefix tailTrace_3745073
  have hstable : (prefixWord ++ tailWord_3745073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745073).length < 2 ^ (prefixWord ++ tailWord_3745073).sum := by decide
  have hdescent : baseEnd_3745073 < baseStart_3745073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745099 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 3]
def baseStart_3745099 : Nat := 118140960795 + 3745099 * 2 ^ 59
def prefixEnd_3745099 : Nat := 4983230072969 + 3 ^ 40 * 3745099 * 2
def baseEnd_3745099 : Nat := 1923035885672748016639109

theorem tailTrace_3745099 : CollatzResearch.WordTrace tailWord_3745099 prefixEnd_3745099 1923035885672748016639109 := by
  unfold tailWord_3745099
  simp only [CollatzResearch.WordTrace]
  refine ⟨136594982259153409832198351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91063321506102273221465567 136594982259153409832198351)
  ·
    refine ⟨204892473388730114748297527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136594982259153409832198351 204892473388730114748297527)
    ·
      refine ⟨307338710083095172122446291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204892473388730114748297527 307338710083095172122446291)
      ·
        refine ⟨461008065124642758183669437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307338710083095172122446291 461008065124642758183669437)
        ·
          refine ⟨172878024421741034318876039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461008065124642758183669437 172878024421741034318876039)
          ·
            refine ⟨259317036632611551478314059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172878024421741034318876039 259317036632611551478314059)
            ·
              refine ⟨388975554948917327217471089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259317036632611551478314059 388975554948917327217471089)
              ·
                refine ⟨291731666211687995413103317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 388975554948917327217471089 291731666211687995413103317)
                ·
                  refine ⟨6837460926836437392494609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 291731666211687995413103317 6837460926836437392494609)
                  ·
                    refine ⟨5128095695127328044370957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6837460926836437392494609 5128095695127328044370957)
                    ·
                      refine ⟨1923035885672748016639109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128095695127328044370957 1923035885672748016639109)
                      ·
                        rfl

theorem cell23_3745099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 7, 2, 3].length) (baseStart_3745099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745099 prefixEnd_3745099 := by exact prefixLift 3745099
  have htrace : WordTrace (prefixWord ++ tailWord_3745099) baseStart_3745099 baseEnd_3745099 := by
    simpa [prefixWord, tailWord_3745099, baseEnd_3745099] using wordTrace_append hprefix tailTrace_3745099
  have hstable : (prefixWord ++ tailWord_3745099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745099).length < 2 ^ (prefixWord ++ tailWord_3745099).sum := by decide
  have hdescent : baseEnd_3745099 < baseStart_3745099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745129 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 3]
def baseStart_3745129 : Nat := 118140960795 + 3745129 * 2 ^ 59
def prefixEnd_3745129 : Nat := 4983230072969 + 3 ^ 40 * 3745129 * 2
def baseEnd_3745129 : Nat := 1923051290092382899263971

theorem tailTrace_3745129 : CollatzResearch.WordTrace tailWord_3745129 prefixEnd_3745129 1923051290092382899263971 := by
  unfold tailWord_3745129
  simp only [CollatzResearch.WordTrace]
  refine ⟨136596076449044724955790441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91064050966029816637193627 136596076449044724955790441)
  ·
    refine ⟨102447057336783543716842831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136596076449044724955790441 102447057336783543716842831)
    ·
      refine ⟨153670586005175315575264247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102447057336783543716842831 153670586005175315575264247)
      ·
        refine ⟨230505879007762973362896371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153670586005175315575264247 230505879007762973362896371)
        ·
          refine ⟨345758818511644460044344557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230505879007762973362896371 345758818511644460044344557)
          ·
            refine ⟨129659556941866672516629209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 345758818511644460044344557 129659556941866672516629209)
            ·
              refine ⟨97244667706400004387471907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129659556941866672516629209 97244667706400004387471907)
              ·
                refine ⟨145867001559600006581207861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97244667706400004387471907 145867001559600006581207861)
                ·
                  refine ⟨13675031396212500616988237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 145867001559600006581207861 13675031396212500616988237)
                  ·
                    refine ⟨5128136773579687731370589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13675031396212500616988237 5128136773579687731370589)
                    ·
                      refine ⟨1923051290092382899263971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128136773579687731370589 1923051290092382899263971)
                      ·
                        rfl

theorem cell23_3745129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 5, 3, 3].length) (baseStart_3745129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745129 prefixEnd_3745129 := by exact prefixLift 3745129
  have htrace : WordTrace (prefixWord ++ tailWord_3745129) baseStart_3745129 baseEnd_3745129 := by
    simpa [prefixWord, tailWord_3745129, baseEnd_3745129] using wordTrace_append hprefix tailTrace_3745129
  have hstable : (prefixWord ++ tailWord_3745129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745129).length < 2 ^ (prefixWord ++ tailWord_3745129).sum := by decide
  have hdescent : baseEnd_3745129 < baseStart_3745129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745173 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 1, 3, 2]
def baseStart_3745173 : Nat := 118140960795 + 3745173 * 2 ^ 59
def prefixEnd_3745173 : Nat := 4983230072969 + 3 ^ 40 * 3745173 * 2
def baseEnd_3745173 : Nat := 1923073883241180727113769

theorem tailTrace_3745173 : CollatzResearch.WordTrace tailWord_3745173 prefixEnd_3745173 1923073883241180727113769 := by
  unfold tailWord_3745173
  simp only [CollatzResearch.WordTrace]
  refine ⟨136597681260885320470392173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91065120840590213646928115 136597681260885320470392173)
  ·
    refine ⟨51224130472831995176397065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136597681260885320470392173 51224130472831995176397065)
    ·
      refine ⟨38418097854623996382297799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51224130472831995176397065 38418097854623996382297799)
      ·
        refine ⟨57627146781935994573446699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38418097854623996382297799 57627146781935994573446699)
        ·
          refine ⟨86440720172903991860170049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57627146781935994573446699 86440720172903991860170049)
          ·
            refine ⟨64830540129677993895127537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86440720172903991860170049 64830540129677993895127537)
            ·
              refine ⟨48622905097258495421345653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64830540129677993895127537 48622905097258495421345653)
              ·
                refine ⟨4558397352867983945751155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48622905097258495421345653 4558397352867983945751155)
                ·
                  refine ⟨6837596029301975918626733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558397352867983945751155 6837596029301975918626733)
                  ·
                    refine ⟨2564098510988240969485025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6837596029301975918626733 2564098510988240969485025)
                    ·
                      refine ⟨1923073883241180727113769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564098510988240969485025 1923073883241180727113769)
                      ·
                        rfl

theorem cell23_3745173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 1, 3, 2].length) (baseStart_3745173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745173 prefixEnd_3745173 := by exact prefixLift 3745173
  have htrace : WordTrace (prefixWord ++ tailWord_3745173) baseStart_3745173 baseEnd_3745173 := by
    simpa [prefixWord, tailWord_3745173, baseEnd_3745173] using wordTrace_append hprefix tailTrace_3745173
  have hstable : (prefixWord ++ tailWord_3745173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745173).length < 2 ^ (prefixWord ++ tailWord_3745173).sum := by decide
  have hdescent : baseEnd_3745173 < baseStart_3745173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745186 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_3745186 : Nat := 118140960795 + 3745186 * 2 ^ 59
def prefixEnd_3745186 : Nat := 4983230072969 + 3 ^ 40 * 3745186 * 2
def baseEnd_3745186 : Nat := 1923080558489689176251209

theorem tailTrace_3745186 : CollatzResearch.WordTrace tailWord_3745186 prefixEnd_3745186 1923080558489689176251209 := by
  unfold tailWord_3745186
  simp only [CollatzResearch.WordTrace]
  refine ⟨34149538852459555922653853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91065436939892149127076941 34149538852459555922653853)
  ·
    refine ⟨12806077069672333470995195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34149538852459555922653853 12806077069672333470995195)
    ·
      refine ⟨19209115604508500206492793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12806077069672333470995195 19209115604508500206492793)
      ·
        refine ⟨14406836703381375154869595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19209115604508500206492793 14406836703381375154869595)
        ·
          refine ⟨21610255055072062732304393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14406836703381375154869595 21610255055072062732304393)
          ·
            refine ⟨16207691291304047049228295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21610255055072062732304393 16207691291304047049228295)
            ·
              refine ⟨24311536936956070573842443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16207691291304047049228295 24311536936956070573842443)
              ·
                refine ⟨36467305405434105860763665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24311536936956070573842443 36467305405434105860763665)
                ·
                  refine ⟨27350479054075579395572749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36467305405434105860763665 27350479054075579395572749)
                  ·
                    refine ⟨10256429645278342273339781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27350479054075579395572749 10256429645278342273339781)
                    ·
                      refine ⟨1923080558489689176251209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10256429645278342273339781 1923080558489689176251209)
                      ·
                        rfl

theorem cell23_3745186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_3745186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745186 prefixEnd_3745186 := by exact prefixLift 3745186
  have htrace : WordTrace (prefixWord ++ tailWord_3745186) baseStart_3745186 baseEnd_3745186 := by
    simpa [prefixWord, tailWord_3745186, baseEnd_3745186] using wordTrace_append hprefix tailTrace_3745186
  have hstable : (prefixWord ++ tailWord_3745186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745186).length < 2 ^ (prefixWord ++ tailWord_3745186).sum := by decide
  have hdescent : baseEnd_3745186 < baseStart_3745186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745189 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_3745189 : Nat := 118140960795 + 3745189 * 2 ^ 59
def prefixEnd_3745189 : Nat := 4983230072969 + 3 ^ 40 * 3745189 * 2
def baseEnd_3745189 : Nat := 1923082098931652664513695

theorem tailTrace_3745189 : CollatzResearch.WordTrace tailWord_3745189 prefixEnd_3745189 1923082098931652664513695 := by
  unfold tailWord_3745189
  simp only [CollatzResearch.WordTrace]
  refine ⟨136598264828827355202974621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91065509885884903468649747 136598264828827355202974621)
  ·
    refine ⟨51224349310810258201115483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136598264828827355202974621 51224349310810258201115483)
    ·
      refine ⟨76836523966215387301673225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51224349310810258201115483 76836523966215387301673225)
      ·
        refine ⟨57627392974661540476254919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76836523966215387301673225 57627392974661540476254919)
        ·
          refine ⟨86441089461992310714382379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57627392974661540476254919 86441089461992310714382379)
          ·
            refine ⟨129661634192988466071573569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86441089461992310714382379 129661634192988466071573569)
            ·
              refine ⟨97246225644741349553680177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129661634192988466071573569 97246225644741349553680177)
              ·
                refine ⟨72934669233556012165260133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97246225644741349553680177 72934669233556012165260133)
                ·
                  refine ⟨13675250481291752280986275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72934669233556012165260133 13675250481291752280986275)
                  ·
                    refine ⟨20512875721937628421479413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13675250481291752280986275 20512875721937628421479413)
                    ·
                      refine ⟨1923082098931652664513695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20512875721937628421479413 1923082098931652664513695)
                      ·
                        rfl

theorem cell23_3745189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_3745189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745189 prefixEnd_3745189 := by exact prefixLift 3745189
  have htrace : WordTrace (prefixWord ++ tailWord_3745189) baseStart_3745189 baseEnd_3745189 := by
    simpa [prefixWord, tailWord_3745189, baseEnd_3745189] using wordTrace_append hprefix tailTrace_3745189
  have hstable : (prefixWord ++ tailWord_3745189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745189).length < 2 ^ (prefixWord ++ tailWord_3745189).sum := by decide
  have hdescent : baseEnd_3745189 < baseStart_3745189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745218 : List Nat := [3, 5, 2, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3745218 : Nat := 118140960795 + 3745218 * 2 ^ 59
def prefixEnd_3745218 : Nat := 4983230072969 + 3 ^ 40 * 3745218 * 2
def baseEnd_3745218 : Nat := 1923096989870633051051063

theorem tailTrace_3745218 : CollatzResearch.WordTrace tailWord_3745218 prefixEnd_3745218 1923096989870633051051063 := by
  unfold tailWord_3745218
  simp only [CollatzResearch.WordTrace]
  refine ⟨34149830636430573288945077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91066215030481528770520205 34149830636430573288945077)
  ·
    refine ⟨3201546622165366245838601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34149830636430573288945077 3201546622165366245838601)
    ·
      refine ⟨2401159966624024684378951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3201546622165366245838601 2401159966624024684378951)
      ·
        refine ⟨3601739949936037026568427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401159966624024684378951 3601739949936037026568427)
        ·
          refine ⟨5402609924904055539852641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601739949936037026568427 5402609924904055539852641)
          ·
            refine ⟨4051957443678041654889481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5402609924904055539852641 4051957443678041654889481)
            ·
              refine ⟨3038968082758531241167111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4051957443678041654889481 3038968082758531241167111)
              ·
                refine ⟨4558452124137796861750667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038968082758531241167111 4558452124137796861750667)
                ·
                  refine ⟨6837678186206695292626001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558452124137796861750667 6837678186206695292626001)
                  ·
                    refine ⟨5128258639655021469469501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6837678186206695292626001 5128258639655021469469501)
                    ·
                      refine ⟨1923096989870633051051063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128258639655021469469501 1923096989870633051051063)
                      ·
                        rfl

theorem cell23_3745218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3745218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745218 prefixEnd_3745218 := by exact prefixLift 3745218
  have htrace : WordTrace (prefixWord ++ tailWord_3745218) baseStart_3745218 baseEnd_3745218 := by
    simpa [prefixWord, tailWord_3745218, baseEnd_3745218] using wordTrace_append hprefix tailTrace_3745218
  have hstable : (prefixWord ++ tailWord_3745218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745218).length < 2 ^ (prefixWord ++ tailWord_3745218).sum := by decide
  have hdescent : baseEnd_3745218 < baseStart_3745218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745220 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3745220 : Nat := 118140960795 + 3745220 * 2 ^ 59
def prefixEnd_3745220 : Nat := 4983230072969 + 3 ^ 40 * 3745220 * 2
def baseEnd_3745220 : Nat := 1923098016831942043226053

theorem tailTrace_3745220 : CollatzResearch.WordTrace tailWord_3745220 prefixEnd_3745220 1923098016831942043226053 := by
  unfold tailWord_3745220
  simp only [CollatzResearch.WordTrace]
  refine ⟨68299697745857523748676557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91066263661143364998235409 68299697745857523748676557)
  ·
    refine ⟨25612386654696571405753709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68299697745857523748676557 25612386654696571405753709)
    ·
      refine ⟨9604644995511214277157641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25612386654696571405753709 9604644995511214277157641)
      ·
        refine ⟨7203483746633410707868231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9604644995511214277157641 7203483746633410707868231)
        ·
          refine ⟨10805225619950116061802347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203483746633410707868231 10805225619950116061802347)
          ·
            refine ⟨16207838429925174092703521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10805225619950116061802347 16207838429925174092703521)
            ·
              refine ⟨12155878822443880569527641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16207838429925174092703521 12155878822443880569527641)
              ·
                refine ⟨9116909116832910427145731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12155878822443880569527641 9116909116832910427145731)
                ·
                  refine ⟨13675363675249365640718597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9116909116832910427145731 13675363675249365640718597)
                  ·
                    refine ⟨2564130689109256057634737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13675363675249365640718597 2564130689109256057634737)
                    ·
                      refine ⟨1923098016831942043226053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564130689109256057634737 1923098016831942043226053)
                      ·
                        rfl

theorem cell23_3745220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3745220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745220 prefixEnd_3745220 := by exact prefixLift 3745220
  have htrace : WordTrace (prefixWord ++ tailWord_3745220) baseStart_3745220 baseEnd_3745220 := by
    simpa [prefixWord, tailWord_3745220, baseEnd_3745220] using wordTrace_append hprefix tailTrace_3745220
  have hstable : (prefixWord ++ tailWord_3745220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745220).length < 2 ^ (prefixWord ++ tailWord_3745220).sum := by decide
  have hdescent : baseEnd_3745220 < baseStart_3745220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745253 : List Nat := [1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3745253 : Nat := 118140960795 + 3745253 * 2 ^ 59
def prefixEnd_3745253 : Nat := 4983230072969 + 3 ^ 40 * 3745253 * 2
def baseEnd_3745253 : Nat := 1923114961693540414113401

theorem tailTrace_3745253 : CollatzResearch.WordTrace tailWord_3745253 prefixEnd_3745253 1923114961693540414113401 := by
  unfold tailWord_3745253
  simp only [CollatzResearch.WordTrace]
  refine ⟨136600599100595494133304413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91067066067063662755536275 136600599100595494133304413)
  ·
    refine ⟨51225224662723310299989155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136600599100595494133304413 51225224662723310299989155)
    ·
      refine ⟨76837836994084965449983733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51225224662723310299989155 76837836994084965449983733)
      ·
        refine ⟨7203547218195465510935975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76837836994084965449983733 7203547218195465510935975)
        ·
          refine ⟨10805320827293198266403963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203547218195465510935975 10805320827293198266403963)
          ·
            refine ⟨16207981240939797399605945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10805320827293198266403963 16207981240939797399605945)
            ·
              refine ⟨12155985930704848049704459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16207981240939797399605945 12155985930704848049704459)
              ·
                refine ⟨18233978896057272074556689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12155985930704848049704459 18233978896057272074556689)
                ·
                  refine ⟨13675484172042954055917517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18233978896057272074556689 13675484172042954055917517)
                  ·
                    refine ⟨5128306564516107770969069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13675484172042954055917517 5128306564516107770969069)
                    ·
                      refine ⟨1923114961693540414113401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128306564516107770969069 1923114961693540414113401)
                      ·
                        rfl

theorem cell23_3745253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3745253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745253 prefixEnd_3745253 := by exact prefixLift 3745253
  have htrace : WordTrace (prefixWord ++ tailWord_3745253) baseStart_3745253 baseEnd_3745253 := by
    simpa [prefixWord, tailWord_3745253, baseEnd_3745253] using wordTrace_append hprefix tailTrace_3745253
  have hstable : (prefixWord ++ tailWord_3745253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745253).length < 2 ^ (prefixWord ++ tailWord_3745253).sum := by decide
  have hdescent : baseEnd_3745253 < baseStart_3745253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745276 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3745276 : Nat := 118140960795 + 3745276 * 2 ^ 59
def prefixEnd_3745276 : Nat := 4983230072969 + 3 ^ 40 * 3745276 * 2
def baseEnd_3745276 : Nat := 1923126771748593824125795

theorem tailTrace_3745276 : CollatzResearch.WordTrace tailWord_3745276 prefixEnd_3745276 1923126771748593824125795 := by
  unfold tailWord_3745276
  simp only [CollatzResearch.WordTrace]
  refine ⟨68300718989756084530695841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91067625319674779374261121 68300718989756084530695841)
  ·
    refine ⟨51225539242317063398021881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68300718989756084530695841 51225539242317063398021881)
    ·
      refine ⟨38419154431737797548516411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51225539242317063398021881 38419154431737797548516411)
      ·
        refine ⟨57628731647606696322774617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38419154431737797548516411 57628731647606696322774617)
        ·
          refine ⟨43221548735705022242080963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57628731647606696322774617 43221548735705022242080963)
          ·
            refine ⟨64832323103557533363121445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43221548735705022242080963 64832323103557533363121445)
            ·
              refine ⟨12156060581917037505585271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64832323103557533363121445 12156060581917037505585271)
              ·
                refine ⟨18234090872875556258377907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12156060581917037505585271 18234090872875556258377907)
                ·
                  refine ⟨27351136309313334387566861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18234090872875556258377907 27351136309313334387566861)
                  ·
                    refine ⟨10256676115992500395337573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27351136309313334387566861 10256676115992500395337573)
                    ·
                      refine ⟨1923126771748593824125795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10256676115992500395337573 1923126771748593824125795)
                      ·
                        rfl

theorem cell23_3745276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3745276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745276 prefixEnd_3745276 := by exact prefixLift 3745276
  have htrace : WordTrace (prefixWord ++ tailWord_3745276) baseStart_3745276 baseEnd_3745276 := by
    simpa [prefixWord, tailWord_3745276, baseEnd_3745276] using wordTrace_append hprefix tailTrace_3745276
  have hstable : (prefixWord ++ tailWord_3745276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745276).length < 2 ^ (prefixWord ++ tailWord_3745276).sum := by decide
  have hdescent : baseEnd_3745276 < baseStart_3745276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745300 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3745300 : Nat := 118140960795 + 3745300 * 2 ^ 59
def prefixEnd_3745300 : Nat := 4983230072969 + 3 ^ 40 * 3745300 * 2
def baseEnd_3745300 : Nat := 1923139095284301730225685

theorem tailTrace_3745300 : CollatzResearch.WordTrace tailWord_3745300 prefixEnd_3745300 1923139095284301730225685 := by
  unfold tailWord_3745300
  simp only [CollatzResearch.WordTrace]
  refine ⟨68301156665712610580132677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91068208887616814106843569 68301156665712610580132677)
  ·
    refine ⟨12806466874821114483774877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68301156665712610580132677 12806466874821114483774877)
    ·
      refine ⟨4802425078057917931415579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12806466874821114483774877 4802425078057917931415579)
      ·
        refine ⟨7203637617086876897123369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4802425078057917931415579 7203637617086876897123369)
        ·
          refine ⟨5402728212815157672842527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7203637617086876897123369 5402728212815157672842527)
          ·
            refine ⟨8104092319222736509263791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402728212815157672842527 8104092319222736509263791)
            ·
              refine ⟨12156138478834104763895687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104092319222736509263791 12156138478834104763895687)
              ·
                refine ⟨18234207718251157145843531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12156138478834104763895687 18234207718251157145843531)
                ·
                  refine ⟨27351311577376735718765297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18234207718251157145843531 27351311577376735718765297)
                  ·
                    refine ⟨20513483683032551789073973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27351311577376735718765297 20513483683032551789073973)
                    ·
                      refine ⟨1923139095284301730225685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20513483683032551789073973 1923139095284301730225685)
                      ·
                        rfl

theorem cell23_3745300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3745300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745300 prefixEnd_3745300 := by exact prefixLift 3745300
  have htrace : WordTrace (prefixWord ++ tailWord_3745300) baseStart_3745300 baseEnd_3745300 := by
    simpa [prefixWord, tailWord_3745300, baseEnd_3745300] using wordTrace_append hprefix tailTrace_3745300
  have hstable : (prefixWord ++ tailWord_3745300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745300).length < 2 ^ (prefixWord ++ tailWord_3745300).sum := by decide
  have hdescent : baseEnd_3745300 < baseStart_3745300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745383 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_3745383 : Nat := 118140960795 + 3745383 * 2 ^ 59
def prefixEnd_3745383 : Nat := 4983230072969 + 3 ^ 40 * 3745383 * 2
def baseEnd_3745383 : Nat := 1923181714178624905487803

theorem tailTrace_3745383 : CollatzResearch.WordTrace tailWord_3745383 prefixEnd_3745383 1923181714178624905487803 := by
  unfold tailWord_3745383
  simp only [CollatzResearch.WordTrace]
  refine ⟨136605340590124526335536803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91070227060083017557024535 136605340590124526335536803)
  ·
    refine ⟨204908010885186789503305205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136605340590124526335536803 204908010885186789503305205)
    ·
      refine ⟨19210126020486261515934863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204908010885186789503305205 19210126020486261515934863)
      ·
        refine ⟨28815189030729392273902295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19210126020486261515934863 28815189030729392273902295)
        ·
          refine ⟨43222783546094088410853443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28815189030729392273902295 43222783546094088410853443)
          ·
            refine ⟨64834175319141132616280165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43222783546094088410853443 64834175319141132616280165)
            ·
              refine ⟨12156407872338962365552531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64834175319141132616280165 12156407872338962365552531)
              ·
                refine ⟨18234611808508443548328797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12156407872338962365552531 18234611808508443548328797)
                ·
                  refine ⟨6837979428190666330623299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18234611808508443548328797 6837979428190666330623299)
                  ·
                    refine ⟨10256969142285999495934949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6837979428190666330623299 10256969142285999495934949)
                    ·
                      refine ⟨1923181714178624905487803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10256969142285999495934949 1923181714178624905487803)
                      ·
                        rfl

theorem cell23_3745383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_3745383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745383 prefixEnd_3745383 := by exact prefixLift 3745383
  have htrace : WordTrace (prefixWord ++ tailWord_3745383) baseStart_3745383 baseEnd_3745383 := by
    simpa [prefixWord, tailWord_3745383, baseEnd_3745383] using wordTrace_append hprefix tailTrace_3745383
  have hstable : (prefixWord ++ tailWord_3745383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745383).length < 2 ^ (prefixWord ++ tailWord_3745383).sum := by decide
  have hdescent : baseEnd_3745383 < baseStart_3745383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745394 : List Nat := [3, 2, 1, 2, 3, 2, 2, 3, 1, 1, 3]
def baseStart_3745394 : Nat := 118140960795 + 3745394 * 2 ^ 59
def prefixEnd_3745394 : Nat := 4983230072969 + 3 ^ 40 * 3745394 * 2
def baseEnd_3745394 : Nat := 1923187362465824362450253

theorem tailTrace_3745394 : CollatzResearch.WordTrace tailWord_3745394 prefixEnd_3745394 1923187362465824362450253 := by
  unfold tailWord_3745394
  simp only [CollatzResearch.WordTrace]
  refine ⟨34151435448271168803546809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91070494528723116809458157 34151435448271168803546809)
  ·
    refine ⟨25613576586203376602660107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34151435448271168803546809 25613576586203376602660107)
    ·
      refine ⟨38420364879305064903990161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25613576586203376602660107 38420364879305064903990161)
      ·
        refine ⟨28815273659478798677992621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38420364879305064903990161 28815273659478798677992621)
        ·
          refine ⟨10805727622304549504247233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28815273659478798677992621 10805727622304549504247233)
          ·
            refine ⟨8104295716728412128185425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10805727622304549504247233 8104295716728412128185425)
            ·
              refine ⟨6078221787546309096139069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8104295716728412128185425 6078221787546309096139069)
              ·
                refine ⟨2279333170329865911052151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6078221787546309096139069 2279333170329865911052151)
                ·
                  refine ⟨3418999755494798866578227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279333170329865911052151 3418999755494798866578227)
                  ·
                    refine ⟨5128499633242198299867341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3418999755494798866578227 5128499633242198299867341)
                    ·
                      refine ⟨1923187362465824362450253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128499633242198299867341 1923187362465824362450253)
                      ·
                        rfl

theorem cell23_3745394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_3745394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745394 prefixEnd_3745394 := by exact prefixLift 3745394
  have htrace : WordTrace (prefixWord ++ tailWord_3745394) baseStart_3745394 baseEnd_3745394 := by
    simpa [prefixWord, tailWord_3745394, baseEnd_3745394] using wordTrace_append hprefix tailTrace_3745394
  have hstable : (prefixWord ++ tailWord_3745394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745394).length < 2 ^ (prefixWord ++ tailWord_3745394).sum := by decide
  have hdescent : baseEnd_3745394 < baseStart_3745394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745397 : List Nat := [1, 3, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_3745397 : Nat := 118140960795 + 3745397 * 2 ^ 59
def prefixEnd_3745397 : Nat := 4983230072969 + 3 ^ 40 * 3745397 * 2
def baseEnd_3745397 : Nat := 641062967635929283570913

theorem tailTrace_3745397 : CollatzResearch.WordTrace tailWord_3745397 prefixEnd_3745397 641062967635929283570913 := by
  unfold tailWord_3745397
  simp only [CollatzResearch.WordTrace]
  refine ⟨136605851212073806726546445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91070567474715871151030963 136605851212073806726546445)
  ·
    refine ⟨51227194204527677522454917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136605851212073806726546445 51227194204527677522454917)
    ·
      refine ⟨9605098913348939535460297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51227194204527677522454917 9605098913348939535460297)
      ·
        refine ⟨7203824185011704651595223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9605098913348939535460297 7203824185011704651595223)
        ·
          refine ⟨10805736277517556977392835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203824185011704651595223 10805736277517556977392835)
          ·
            refine ⟨16208604416276335466089253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10805736277517556977392835 16208604416276335466089253)
            ·
              refine ⟨3039113328051812899891735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16208604416276335466089253 3039113328051812899891735)
              ·
                refine ⟨4558669992077719349837603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039113328051812899891735 4558669992077719349837603)
                ·
                  refine ⟨6838004988116579024756405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558669992077719349837603 6838004988116579024756405)
                  ·
                    refine ⟨641062967635929283570913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6838004988116579024756405 641062967635929283570913)
                    ·
                      rfl

theorem cell23_3745397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_3745397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745397 prefixEnd_3745397 := by exact prefixLift 3745397
  have htrace : WordTrace (prefixWord ++ tailWord_3745397) baseStart_3745397 baseEnd_3745397 := by
    simpa [prefixWord, tailWord_3745397, baseEnd_3745397] using wordTrace_append hprefix tailTrace_3745397
  have hstable : (prefixWord ++ tailWord_3745397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745397).length < 2 ^ (prefixWord ++ tailWord_3745397).sum := by decide
  have hdescent : baseEnd_3745397 < baseStart_3745397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745433 : List Nat := [1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 3]
def baseStart_3745433 : Nat := 118140960795 + 3745433 * 2 ^ 59
def prefixEnd_3745433 : Nat := 4983230072969 + 3 ^ 40 * 3745433 * 2
def baseEnd_3745433 : Nat := 1923207388211349709862573

theorem tailTrace_3745433 : CollatzResearch.WordTrace tailWord_3745433 prefixEnd_3745433 1923207388211349709862573 := by
  unfold tailWord_3745433
  simp only [CollatzResearch.WordTrace]
  refine ⟨136607164239943384874856953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91071442826628923249904635 136607164239943384874856953)
  ·
    refine ⟨102455373179957538656142715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136607164239943384874856953 102455373179957538656142715)
    ·
      refine ⟨153683059769936307984214073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102455373179957538656142715 153683059769936307984214073)
      ·
        refine ⟨115262294827452230988160555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153683059769936307984214073 115262294827452230988160555)
        ·
          refine ⟨172893442241178346482240833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115262294827452230988160555 172893442241178346482240833)
          ·
            refine ⟨129670081680883759861680625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172893442241178346482240833 129670081680883759861680625)
            ·
              refine ⟨97252561260662819896260469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129670081680883759861680625 97252561260662819896260469)
              ·
                refine ⟨9117427618187139365274419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97252561260662819896260469 9117427618187139365274419)
                ·
                  refine ⟨13676141427280709047911629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9117427618187139365274419 13676141427280709047911629)
                  ·
                    refine ⟨5128553035230265892966861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13676141427280709047911629 5128553035230265892966861)
                    ·
                      refine ⟨1923207388211349709862573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128553035230265892966861 1923207388211349709862573)
                      ·
                        rfl

theorem cell23_3745433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_3745433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745433 prefixEnd_3745433 := by exact prefixLift 3745433
  have htrace : WordTrace (prefixWord ++ tailWord_3745433) baseStart_3745433 baseEnd_3745433 := by
    simpa [prefixWord, tailWord_3745433, baseEnd_3745433] using wordTrace_append hprefix tailTrace_3745433
  have hstable : (prefixWord ++ tailWord_3745433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745433).length < 2 ^ (prefixWord ++ tailWord_3745433).sum := by decide
  have hdescent : baseEnd_3745433 < baseStart_3745433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745440 : List Nat := [2, 1, 1, 4, 3, 3, 2, 7]
def baseStart_3745440 : Nat := 118140960795 + 3745440 * 2 ^ 59
def prefixEnd_3745440 : Nat := 4983230072969 + 3 ^ 40 * 3745440 * 2
def baseEnd_3745440 : Nat := 71230036391701154906483

theorem tailTrace_3745440 : CollatzResearch.WordTrace tailWord_3745440 prefixEnd_3745440 71230036391701154906483 := by
  unfold tailWord_3745440
  simp only [CollatzResearch.WordTrace]
  refine ⟨68303709775459012535180887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91071613033945350046907849 68303709775459012535180887)
  ·
    refine ⟨102455564663188518802771331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68303709775459012535180887 102455564663188518802771331)
    ·
      refine ⟨153683346994782778204156997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102455564663188518802771331 153683346994782778204156997)
      ·
        refine ⟨28815627561521770913279437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153683346994782778204156997 28815627561521770913279437)
        ·
          refine ⟨10805860335570664092479789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28815627561521770913279437 10805860335570664092479789)
          ·
            refine ⟨4052197625838999034679921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10805860335570664092479789 4052197625838999034679921)
            ·
              refine ⟨3039148219379249276009941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4052197625838999034679921 3039148219379249276009941)
              ·
                refine ⟨71230036391701154906483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3039148219379249276009941 71230036391701154906483)
                ·
                  rfl

theorem cell23_3745440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 7].length) (baseStart_3745440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745440 prefixEnd_3745440 := by exact prefixLift 3745440
  have htrace : WordTrace (prefixWord ++ tailWord_3745440) baseStart_3745440 baseEnd_3745440 := by
    simpa [prefixWord, tailWord_3745440, baseEnd_3745440] using wordTrace_append hprefix tailTrace_3745440
  have hstable : (prefixWord ++ tailWord_3745440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745440).length < 2 ^ (prefixWord ++ tailWord_3745440).sum := by decide
  have hdescent : baseEnd_3745440 < baseStart_3745440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745474 : List Nat := [3, 5, 1, 2, 1, 1, 2, 8]
def baseStart_3745474 : Nat := 118140960795 + 3745474 * 2 ^ 59
def prefixEnd_3745474 : Nat := 4983230072969 + 3 ^ 40 * 3745474 * 2
def baseEnd_3745474 : Nat := 71230682996969779609255

theorem tailTrace_3745474 : CollatzResearch.WordTrace tailWord_3745474 prefixEnd_3745474 71230682996969779609255 := by
  unfold tailWord_3745474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34152164908198712219274869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91072439755196565918066317 34152164908198712219274869)
  ·
    refine ⟨3201765460143629270557019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34152164908198712219274869 3201765460143629270557019)
    ·
      refine ⟨4802648190215443905835529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3201765460143629270557019 4802648190215443905835529)
      ·
        refine ⟨3601986142661582929376647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4802648190215443905835529 3601986142661582929376647)
        ·
          refine ⟨5402979213992374394064971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3601986142661582929376647 5402979213992374394064971)
          ·
            refine ⟨8104468820988561591097457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402979213992374394064971 8104468820988561591097457)
            ·
              refine ⟨6078351615741421193323093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8104468820988561591097457 6078351615741421193323093)
              ·
                refine ⟨71230682996969779609255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6078351615741421193323093 71230682996969779609255)
                ·
                  rfl

theorem cell23_3745474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_3745474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745474 prefixEnd_3745474 := by exact prefixLift 3745474
  have htrace : WordTrace (prefixWord ++ tailWord_3745474) baseStart_3745474 baseEnd_3745474 := by
    simpa [prefixWord, tailWord_3745474, baseEnd_3745474] using wordTrace_append hprefix tailTrace_3745474
  have hstable : (prefixWord ++ tailWord_3745474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745474).length < 2 ^ (prefixWord ++ tailWord_3745474).sum := by decide
  have hdescent : baseEnd_3745474 < baseStart_3745474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745478 : List Nat := [6, 1, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_3745478 : Nat := 118140960795 + 3745478 * 2 ^ 59
def prefixEnd_3745478 : Nat := 4983230072969 + 3 ^ 40 * 3745478 * 2
def baseEnd_3745478 : Nat := 641076831613600677933289

theorem tailTrace_3745478 : CollatzResearch.WordTrace tailWord_3745478 prefixEnd_3745478 641076831613600677933289 := by
  unfold tailWord_3745478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269025172649386173757659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91072537016520238373496725 4269025172649386173757659)
  ·
    refine ⟨6403537758974079260636489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4269025172649386173757659 6403537758974079260636489)
    ·
      refine ⟨4802653319230559445477367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6403537758974079260636489 4802653319230559445477367)
      ·
        refine ⟨7203979978845839168216051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4802653319230559445477367 7203979978845839168216051)
        ·
          refine ⟨10805969968268758752324077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203979978845839168216051 10805969968268758752324077)
          ·
            refine ⟨4052238738100784532121529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10805969968268758752324077 4052238738100784532121529)
            ·
              refine ⟨3039179053575588399091147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4052238738100784532121529 3039179053575588399091147)
              ·
                refine ⟨4558768580363382598636721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039179053575588399091147 4558768580363382598636721)
                ·
                  refine ⟨3419076435272536948977541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4558768580363382598636721 3419076435272536948977541)
                  ·
                    refine ⟨641076831613600677933289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3419076435272536948977541 641076831613600677933289)
                    ·
                      rfl

theorem cell23_3745478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_3745478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745478 prefixEnd_3745478 := by exact prefixLift 3745478
  have htrace : WordTrace (prefixWord ++ tailWord_3745478) baseStart_3745478 baseEnd_3745478 := by
    simpa [prefixWord, tailWord_3745478, baseEnd_3745478] using wordTrace_append hprefix tailTrace_3745478
  have hstable : (prefixWord ++ tailWord_3745478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745478).length < 2 ^ (prefixWord ++ tailWord_3745478).sum := by decide
  have hdescent : baseEnd_3745478 < baseStart_3745478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745484 : List Nat := [2, 2, 1, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_3745484 : Nat := 118140960795 + 3745484 * 2 ^ 59
def prefixEnd_3745484 : Nat := 4983230072969 + 3 ^ 40 * 3745484 * 2
def baseEnd_3745484 : Nat := 1923233575724729010324839

theorem tailTrace_3745484 : CollatzResearch.WordTrace tailWord_3745484 prefixEnd_3745484 1923233575724729010324839 := by
  unfold tailWord_3745484
  simp only [CollatzResearch.WordTrace]
  refine ⟨68304512181379310292481753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91072682908505747056642337 68304512181379310292481753)
  ·
    refine ⟨51228384136034482719361315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68304512181379310292481753 51228384136034482719361315)
    ·
      refine ⟨76842576204051724079041973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51228384136034482719361315 76842576204051724079041973)
      ·
        refine ⟨7203991519129849132410185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76842576204051724079041973 7203991519129849132410185)
        ·
          refine ⟨5402993639347386849307639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7203991519129849132410185 5402993639347386849307639)
          ·
            refine ⟨8104490459021080273961459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402993639347386849307639 8104490459021080273961459)
            ·
              refine ⟨12156735688531620410942189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104490459021080273961459 12156735688531620410942189)
              ·
                refine ⟨4558775883199357654103321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12156735688531620410942189 4558775883199357654103321)
                ·
                  refine ⟨3419081912399518240577491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4558775883199357654103321 3419081912399518240577491)
                  ·
                    refine ⟨5128622868599277360866237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3419081912399518240577491 5128622868599277360866237)
                    ·
                      refine ⟨1923233575724729010324839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128622868599277360866237 1923233575724729010324839)
                      ·
                        rfl

theorem cell23_3745484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_3745484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745484 prefixEnd_3745484 := by exact prefixLift 3745484
  have htrace : WordTrace (prefixWord ++ tailWord_3745484) baseStart_3745484 baseEnd_3745484 := by
    simpa [prefixWord, tailWord_3745484, baseEnd_3745484] using wordTrace_append hprefix tailTrace_3745484
  have hstable : (prefixWord ++ tailWord_3745484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745484).length < 2 ^ (prefixWord ++ tailWord_3745484).sum := by decide
  have hdescent : baseEnd_3745484 < baseStart_3745484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745540 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 1, 5, 3]
def baseStart_3745540 : Nat := 118140960795 + 3745540 * 2 ^ 59
def prefixEnd_3745540 : Nat := 4983230072969 + 3 ^ 40 * 3745540 * 2
def baseEnd_3745540 : Nat := 1923262330641380791224581

theorem tailTrace_3745540 : CollatzResearch.WordTrace tailWord_3745540 prefixEnd_3745540 1923262330641380791224581 := by
  unfold tailWord_3745540
  simp only [CollatzResearch.WordTrace]
  refine ⟨68305533425277871074501037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91074044567037161432668049 68305533425277871074501037)
  ·
    refine ⟨25614575034479201652937889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68305533425277871074501037 25614575034479201652937889)
    ·
      refine ⟨19210931275859401239703417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25614575034479201652937889 19210931275859401239703417)
      ·
        refine ⟨14408198456894550929777563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19210931275859401239703417 14408198456894550929777563)
        ·
          refine ⟨21612297685341826394666345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14408198456894550929777563 21612297685341826394666345)
          ·
            refine ⟨16209223264006369795999759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21612297685341826394666345 16209223264006369795999759)
            ·
              refine ⟨24313834896009554693999639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16209223264006369795999759 24313834896009554693999639)
              ·
                refine ⟨36470752344014332040999459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24313834896009554693999639 36470752344014332040999459)
                ·
                  refine ⟨54706128516021498061499189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36470752344014332040999459 54706128516021498061499189)
                  ·
                    refine ⟨5128699548377015443265549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54706128516021498061499189 5128699548377015443265549)
                    ·
                      refine ⟨1923262330641380791224581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128699548377015443265549 1923262330641380791224581)
                      ·
                        rfl

theorem cell23_3745540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_3745540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745540 prefixEnd_3745540 := by exact prefixLift 3745540
  have htrace : WordTrace (prefixWord ++ tailWord_3745540) baseStart_3745540 baseEnd_3745540 := by
    simpa [prefixWord, tailWord_3745540, baseEnd_3745540] using wordTrace_append hprefix tailTrace_3745540
  have hstable : (prefixWord ++ tailWord_3745540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745540).length < 2 ^ (prefixWord ++ tailWord_3745540).sum := by decide
  have hdescent : baseEnd_3745540 < baseStart_3745540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745560 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 2, 5]
def baseStart_3745560 : Nat := 118140960795 + 3745560 * 2 ^ 59
def prefixEnd_3745560 : Nat := 4983230072969 + 3 ^ 40 * 3745560 * 2
def baseEnd_3745560 : Nat := 641090866751490237658163

theorem tailTrace_3745560 : CollatzResearch.WordTrace tailWord_3745560 prefixEnd_3745560 641090866751490237658163 := by
  unfold tailWord_3745560
  simp only [CollatzResearch.WordTrace]
  refine ⟨68305898155241642782365067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91074530873655523709820089 68305898155241642782365067)
  ·
    refine ⟨102458847232862464173547601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68305898155241642782365067 102458847232862464173547601)
    ·
      refine ⟨76844135424646848130160701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102458847232862464173547601 76844135424646848130160701)
      ·
        refine ⟨28816550784242568048810263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76844135424646848130160701 28816550784242568048810263)
        ·
          refine ⟨43224826176363852073215395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28816550784242568048810263 43224826176363852073215395)
          ·
            refine ⟨64837239264545778109823093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43224826176363852073215395 64837239264545778109823093)
            ·
              refine ⟨6078491181051166697795915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64837239264545778109823093 6078491181051166697795915)
              ·
                refine ⟨9117736771576750046693873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6078491181051166697795915 9117736771576750046693873)
                ·
                  refine ⟨6838302578682562535020405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9117736771576750046693873 6838302578682562535020405)
                  ·
                    refine ⟨641090866751490237658163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6838302578682562535020405 641090866751490237658163)
                    ·
                      rfl

theorem cell23_3745560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 2, 5].length) (baseStart_3745560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745560 prefixEnd_3745560 := by exact prefixLift 3745560
  have htrace : WordTrace (prefixWord ++ tailWord_3745560) baseStart_3745560 baseEnd_3745560 := by
    simpa [prefixWord, tailWord_3745560, baseEnd_3745560] using wordTrace_append hprefix tailTrace_3745560
  have hstable : (prefixWord ++ tailWord_3745560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745560).length < 2 ^ (prefixWord ++ tailWord_3745560).sum := by decide
  have hdescent : baseEnd_3745560 < baseStart_3745560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745563 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4]
def baseStart_3745563 : Nat := 118140960795 + 3745563 * 2 ^ 59
def prefixEnd_3745563 : Nat := 4983230072969 + 3 ^ 40 * 3745563 * 2
def baseEnd_3745563 : Nat := 1923274140696434201236975

theorem tailTrace_3745563 : CollatzResearch.WordTrace tailWord_3745563 prefixEnd_3745563 1923274140696434201236975 := by
  unfold tailWord_3745563
  simp only [CollatzResearch.WordTrace]
  refine ⟨136611905729472417077089343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91074603819648278051392895 136611905729472417077089343)
  ·
    refine ⟨204917858594208625615634015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136611905729472417077089343 204917858594208625615634015)
    ·
      refine ⟨307376787891312938423451023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204917858594208625615634015 307376787891312938423451023)
      ·
        refine ⟨461065181836969407635176535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307376787891312938423451023 461065181836969407635176535)
        ·
          refine ⟨691597772755454111452764803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461065181836969407635176535 691597772755454111452764803)
          ·
            refine ⟨1037396659133181167179147205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 691597772755454111452764803 1037396659133181167179147205)
            ·
              refine ⟨194511873587471468846090101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1037396659133181167179147205 194511873587471468846090101)
              ·
                refine ⟨18235488148825450204320947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194511873587471468846090101 18235488148825450204320947)
                ·
                  refine ⟨27353232223238175306481421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18235488148825450204320947 27353232223238175306481421)
                  ·
                    refine ⟨10257462083714315739930533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27353232223238175306481421 10257462083714315739930533)
                    ·
                      refine ⟨1923274140696434201236975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10257462083714315739930533 1923274140696434201236975)
                      ·
                        rfl

theorem cell23_3745563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 4].length) (baseStart_3745563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745563 prefixEnd_3745563 := by exact prefixLift 3745563
  have htrace : WordTrace (prefixWord ++ tailWord_3745563) baseStart_3745563 baseEnd_3745563 := by
    simpa [prefixWord, tailWord_3745563, baseEnd_3745563] using wordTrace_append hprefix tailTrace_3745563
  have hstable : (prefixWord ++ tailWord_3745563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745563).length < 2 ^ (prefixWord ++ tailWord_3745563).sum := by decide
  have hdescent : baseEnd_3745563 < baseStart_3745563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745620 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 8]
def baseStart_3745620 : Nat := 118140960795 + 3745620 * 2 ^ 59
def prefixEnd_3745620 : Nat := 4983230072969 + 3 ^ 40 * 3745620 * 2
def baseEnd_3745620 : Nat := 213700378788193386469357

theorem tailTrace_3745620 : CollatzResearch.WordTrace tailWord_3745620 prefixEnd_3745620 213700378788193386469357 := by
  unfold tailWord_3745620
  simp only [CollatzResearch.WordTrace]
  refine ⟨68306992345132957905957157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91075989793510610541276209 68306992345132957905957157)
  ·
    refine ⟨12807561064712429607366967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68306992345132957905957157 12807561064712429607366967)
    ·
      refine ⟨19211341597068644411050451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12807561064712429607366967 19211341597068644411050451)
      ·
        refine ⟨28817012395602966616575677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19211341597068644411050451 28817012395602966616575677)
        ·
          refine ⟨10806379648351112481215879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28817012395602966616575677 10806379648351112481215879)
          ·
            refine ⟨16209569472526668721823819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10806379648351112481215879 16209569472526668721823819)
            ·
              refine ⟨24314354208790003082735729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16209569472526668721823819 24314354208790003082735729)
              ·
                refine ⟨18235765656592502312051797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24314354208790003082735729 18235765656592502312051797)
                ·
                  refine ⟨213700378788193386469357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18235765656592502312051797 213700378788193386469357)
                  ·
                    rfl

theorem cell23_3745620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_3745620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745620 prefixEnd_3745620 := by exact prefixLift 3745620
  have htrace : WordTrace (prefixWord ++ tailWord_3745620) baseStart_3745620 baseEnd_3745620 := by
    simpa [prefixWord, tailWord_3745620, baseEnd_3745620] using wordTrace_append hprefix tailTrace_3745620
  have hstable : (prefixWord ++ tailWord_3745620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745620).length < 2 ^ (prefixWord ++ tailWord_3745620).sum := by decide
  have hdescent : baseEnd_3745620 < baseStart_3745620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745634 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_3745634 : Nat := 118140960795 + 3745634 * 2 ^ 59
def prefixEnd_3745634 : Nat := 4983230072969 + 3 ^ 40 * 3745634 * 2
def baseEnd_3745634 : Nat := 1923310597822903423449149

theorem tailTrace_3745634 : CollatzResearch.WordTrace tailWord_3745634 prefixEnd_3745634 1923310597822903423449149 := by
  unfold tailWord_3745634
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153623828053799050730989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91076330208143464135282637 34153623828053799050730989)
  ·
    refine ⟨12807608935520174644024121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34153623828053799050730989 12807608935520174644024121)
    ·
      refine ⟨9605706701640130983018091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12807608935520174644024121 9605706701640130983018091)
      ·
        refine ⟨14408560052460196474527137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9605706701640130983018091 14408560052460196474527137)
        ·
          refine ⟨10806420039345147355895353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14408560052460196474527137 10806420039345147355895353)
          ·
            refine ⟨8104815029508860516921515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10806420039345147355895353 8104815029508860516921515)
            ·
              refine ⟨12157222544263290775382273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104815029508860516921515 12157222544263290775382273)
              ·
                refine ⟨9117916908197468081536705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12157222544263290775382273 9117916908197468081536705)
                ·
                  refine ⟨6838437681148101061152529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9117916908197468081536705 6838437681148101061152529)
                  ·
                    refine ⟨5128828260861075795864397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6838437681148101061152529 5128828260861075795864397)
                    ·
                      refine ⟨1923310597822903423449149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128828260861075795864397 1923310597822903423449149)
                      ·
                        rfl

theorem cell23_3745634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_3745634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745634 prefixEnd_3745634 := by exact prefixLift 3745634
  have htrace : WordTrace (prefixWord ++ tailWord_3745634) baseStart_3745634 baseEnd_3745634 := by
    simpa [prefixWord, tailWord_3745634, baseEnd_3745634] using wordTrace_append hprefix tailTrace_3745634
  have hstable : (prefixWord ++ tailWord_3745634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745634).length < 2 ^ (prefixWord ++ tailWord_3745634).sum := by decide
  have hdescent : baseEnd_3745634 < baseStart_3745634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745643 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7]
def baseStart_3745643 : Nat := 118140960795 + 3745643 * 2 ^ 59
def prefixEnd_3745643 : Nat := 4983230072969 + 3 ^ 40 * 3745643 * 2
def baseEnd_3745643 : Nat := 1923315219148793888236607

theorem tailTrace_3745643 : CollatzResearch.WordTrace tailWord_3745643 prefixEnd_3745643 1923315219148793888236607 := by
  unfold tailWord_3745643
  simp only [CollatzResearch.WordTrace]
  refine ⟨136614823569182590740001583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91076549046121727160001055 136614823569182590740001583)
  ·
    refine ⟨204922235353773886110002375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136614823569182590740001583 204922235353773886110002375)
    ·
      refine ⟨307383353030660829165003563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204922235353773886110002375 307383353030660829165003563)
      ·
        refine ⟨461075029545991243747505345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307383353030660829165003563 461075029545991243747505345)
        ·
          refine ⟨345806272159493432810629009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 461075029545991243747505345 345806272159493432810629009)
          ·
            refine ⟨259354704119620074607971757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345806272159493432810629009 259354704119620074607971757)
            ·
              refine ⟨97258014044857527977989409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259354704119620074607971757 97258014044857527977989409)
              ·
                refine ⟨72943510533643145983492057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97258014044857527977989409 72943510533643145983492057)
                ·
                  refine ⟨54707632900232359487619043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72943510533643145983492057 54707632900232359487619043)
                  ·
                    refine ⟨82061449350348539231428565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54707632900232359487619043 82061449350348539231428565)
                    ·
                      refine ⟨1923315219148793888236607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82061449350348539231428565 1923315219148793888236607)
                      ·
                        rfl

theorem cell23_3745643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 7].length) (baseStart_3745643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745643 prefixEnd_3745643 := by exact prefixLift 3745643
  have htrace : WordTrace (prefixWord ++ tailWord_3745643) baseStart_3745643 baseEnd_3745643 := by
    simpa [prefixWord, tailWord_3745643, baseEnd_3745643] using wordTrace_append hprefix tailTrace_3745643
  have hstable : (prefixWord ++ tailWord_3745643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745643).length < 2 ^ (prefixWord ++ tailWord_3745643).sum := by decide
  have hdescent : baseEnd_3745643 < baseStart_3745643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745650 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_3745650 : Nat := 118140960795 + 3745650 * 2 ^ 59
def prefixEnd_3745650 : Nat := 4983230072969 + 3 ^ 40 * 3745650 * 2
def baseEnd_3745650 : Nat := 641106271171125120283025

theorem tailTrace_3745650 : CollatzResearch.WordTrace tailWord_3745650 prefixEnd_3745650 641106271171125120283025 := by
  unfold tailWord_3745650
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153769720039307733876601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91076719253438153957004269 34153769720039307733876601)
  ·
    refine ⟨25615327290029480800407451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34153769720039307733876601 25615327290029480800407451)
    ·
      refine ⟨38422990935044221200611177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25615327290029480800407451 38422990935044221200611177)
      ·
        refine ⟨28817243201283165900458383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38422990935044221200611177 28817243201283165900458383)
        ·
          refine ⟨43225864801924748850687575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28817243201283165900458383 43225864801924748850687575)
          ·
            refine ⟨64838797202887123276031363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43225864801924748850687575 64838797202887123276031363)
            ·
              refine ⟨97258195804330684914047045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64838797202887123276031363 97258195804330684914047045)
              ·
                refine ⟨18235911713312003421383821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97258195804330684914047045 18235911713312003421383821)
                ·
                  refine ⟨6838466892492001283018933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18235911713312003421383821 6838466892492001283018933)
                  ·
                    refine ⟨641106271171125120283025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6838466892492001283018933 641106271171125120283025)
                    ·
                      rfl

theorem cell23_3745650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_3745650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745650 prefixEnd_3745650 := by exact prefixLift 3745650
  have htrace : WordTrace (prefixWord ++ tailWord_3745650) baseStart_3745650 baseEnd_3745650 := by
    simpa [prefixWord, tailWord_3745650, baseEnd_3745650] using wordTrace_append hprefix tailTrace_3745650
  have hstable : (prefixWord ++ tailWord_3745650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745650).length < 2 ^ (prefixWord ++ tailWord_3745650).sum := by decide
  have hdescent : baseEnd_3745650 < baseStart_3745650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745654 : List Nat := [5, 1, 1, 3, 2, 1, 1, 3, 6]
def baseStart_3745654 : Nat := 118140960795 + 3745654 * 2 ^ 59
def prefixEnd_3745654 : Nat := 4983230072969 + 3 ^ 40 * 3745654 * 2
def baseEnd_3745654 : Nat := 213702318603999260577673

theorem tailTrace_3745654 : CollatzResearch.WordTrace tailWord_3745654 prefixEnd_3745654 213702318603999260577673 := by
  unfold tailWord_3745654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538451548258921226165751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91076816514761826412434677 8538451548258921226165751)
  ·
    refine ⟨12807677322388381839248627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8538451548258921226165751 12807677322388381839248627)
    ·
      refine ⟨19211515983582572758872941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12807677322388381839248627 19211515983582572758872941)
      ·
        refine ⟨7204318493843464784577353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19211515983582572758872941 7204318493843464784577353)
        ·
          refine ⟨5403238870382598588433015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204318493843464784577353 5403238870382598588433015)
          ·
            refine ⟨8104858305573897882649523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403238870382598588433015 8104858305573897882649523)
            ·
              refine ⟨12157287458360846823974285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104858305573897882649523 12157287458360846823974285)
              ·
                refine ⟨4558982796885317558990357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12157287458360846823974285 4558982796885317558990357)
                ·
                  refine ⟨213702318603999260577673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4558982796885317558990357 213702318603999260577673)
                  ·
                    rfl

theorem cell23_3745654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_3745654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745654 prefixEnd_3745654 := by exact prefixLift 3745654
  have htrace : WordTrace (prefixWord ++ tailWord_3745654) baseStart_3745654 baseEnd_3745654 := by
    simpa [prefixWord, tailWord_3745654, baseEnd_3745654] using wordTrace_append hprefix tailTrace_3745654
  have hstable : (prefixWord ++ tailWord_3745654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745654).length < 2 ^ (prefixWord ++ tailWord_3745654).sum := by decide
  have hdescent : baseEnd_3745654 < baseStart_3745654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745657 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 4, 3, 2]
def baseStart_3745657 : Nat := 118140960795 + 3745657 * 2 ^ 59
def prefixEnd_3745657 : Nat := 4983230072969 + 3 ^ 40 * 3745657 * 2
def baseEnd_3745657 : Nat := 1923322407877956833461543

theorem tailTrace_3745657 : CollatzResearch.WordTrace tailWord_3745657 prefixEnd_3745657 1923322407877956833461543 := by
  unfold tailWord_3745657
  simp only [CollatzResearch.WordTrace]
  refine ⟨136615334191131871131011225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91076889460754580754007483 136615334191131871131011225)
  ·
    refine ⟨102461500643348903348258419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136615334191131871131011225 102461500643348903348258419)
    ·
      refine ⟨153692250965023355022387629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102461500643348903348258419 153692250965023355022387629)
      ·
        refine ⟨57634594111883758133395361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153692250965023355022387629 57634594111883758133395361)
        ·
          refine ⟨43225945583912818600046521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57634594111883758133395361 43225945583912818600046521)
          ·
            refine ⟨32419459187934613950034891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43225945583912818600046521 32419459187934613950034891)
            ·
              refine ⟨48629188781901920925052337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32419459187934613950034891 48629188781901920925052337)
              ·
                refine ⟨36471891586426440693789253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48629188781901920925052337 36471891586426440693789253)
                ·
                  refine ⟨6838479672454957630085485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36471891586426440693789253 6838479672454957630085485)
                  ·
                    refine ⟨2564429877170609111282057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6838479672454957630085485 2564429877170609111282057)
                    ·
                      refine ⟨1923322407877956833461543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564429877170609111282057 1923322407877956833461543)
                      ·
                        rfl

theorem cell23_3745657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_3745657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745657 prefixEnd_3745657 := by exact prefixLift 3745657
  have htrace : WordTrace (prefixWord ++ tailWord_3745657) baseStart_3745657 baseEnd_3745657 := by
    simpa [prefixWord, tailWord_3745657, baseEnd_3745657] using wordTrace_append hprefix tailTrace_3745657
  have hstable : (prefixWord ++ tailWord_3745657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745657).length < 2 ^ (prefixWord ++ tailWord_3745657).sum := by decide
  have hdescent : baseEnd_3745657 < baseStart_3745657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745667 : List Nat := [1, 1, 1, 3, 4, 2, 3, 2, 1, 5]
def baseStart_3745667 : Nat := 118140960795 + 3745667 * 2 ^ 59
def prefixEnd_3745667 : Nat := 4983230072969 + 3 ^ 40 * 3745667 * 2
def baseEnd_3745667 : Nat := 641109180894833931445499

theorem tailTrace_3745667 : CollatzResearch.WordTrace tailWord_3745667 prefixEnd_3745667 641109180894833931445499 := by
  unfold tailWord_3745667
  simp only [CollatzResearch.WordTrace]
  refine ⟨136615698921095642838875255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91077132614063761892583503 136615698921095642838875255)
  ·
    refine ⟨204923548381643464258312883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136615698921095642838875255 204923548381643464258312883)
    ·
      refine ⟨307385322572465196387469325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204923548381643464258312883 307385322572465196387469325)
      ·
        refine ⟨115269495964674448645300997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307385322572465196387469325 115269495964674448645300997)
        ·
          refine ⟨21613030493376459120993937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115269495964674448645300997 21613030493376459120993937)
          ·
            refine ⟨16209772870032344340745453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21613030493376459120993937 16209772870032344340745453)
            ·
              refine ⟨6078664826262129127779545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16209772870032344340745453 6078664826262129127779545)
              ·
                refine ⟨4558998619696596845834659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6078664826262129127779545 4558998619696596845834659)
                ·
                  refine ⟨6838497929544895268751989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4558998619696596845834659 6838497929544895268751989)
                  ·
                    refine ⟨641109180894833931445499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6838497929544895268751989 641109180894833931445499)
                    ·
                      rfl

theorem cell23_3745667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2, 1, 5].length) (baseStart_3745667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745667 prefixEnd_3745667 := by exact prefixLift 3745667
  have htrace : WordTrace (prefixWord ++ tailWord_3745667) baseStart_3745667 baseEnd_3745667 := by
    simpa [prefixWord, tailWord_3745667, baseEnd_3745667] using wordTrace_append hprefix tailTrace_3745667
  have hstable : (prefixWord ++ tailWord_3745667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745667).length < 2 ^ (prefixWord ++ tailWord_3745667).sum := by decide
  have hdescent : baseEnd_3745667 < baseStart_3745667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745698 : List Nat := [3, 3, 1, 2, 3, 1, 1, 4, 1, 1, 3]
def baseStart_3745698 : Nat := 118140960795 + 3745698 * 2 ^ 59
def prefixEnd_3745698 : Nat := 4983230072969 + 3 ^ 40 * 3745698 * 2
def baseEnd_3745698 : Nat := 1923343460584791173048855

theorem tailTrace_3745698 : CollatzResearch.WordTrace tailWord_3745698 prefixEnd_3745698 1923343460584791173048855 := by
  unfold tailWord_3745698
  simp only [CollatzResearch.WordTrace]
  refine ⟨34154207395995833783313437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91077886389322223422169165 34154207395995833783313437)
  ·
    refine ⟨12807827773498437668742539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34154207395995833783313437 12807827773498437668742539)
    ·
      refine ⟨19211741660247656503113809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12807827773498437668742539 19211741660247656503113809)
      ·
        refine ⟨14408806245185742377335357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19211741660247656503113809 14408806245185742377335357)
        ·
          refine ⟨5403302341944653391500759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14408806245185742377335357 5403302341944653391500759)
          ·
            refine ⟨8104953512916980087251139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403302341944653391500759 8104953512916980087251139)
            ·
              refine ⟨12157430269375470130876709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8104953512916980087251139 12157430269375470130876709)
              ·
                refine ⟨2279518175507900649539383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12157430269375470130876709 2279518175507900649539383)
                ·
                  refine ⟨3419277263261850974309075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279518175507900649539383 3419277263261850974309075)
                  ·
                    refine ⟨5128915894892776461463613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3419277263261850974309075 5128915894892776461463613)
                    ·
                      refine ⟨1923343460584791173048855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128915894892776461463613 1923343460584791173048855)
                      ·
                        rfl

theorem cell23_3745698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_3745698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745698 prefixEnd_3745698 := by exact prefixLift 3745698
  have htrace : WordTrace (prefixWord ++ tailWord_3745698) baseStart_3745698 baseEnd_3745698 := by
    simpa [prefixWord, tailWord_3745698, baseEnd_3745698] using wordTrace_append hprefix tailTrace_3745698
  have hstable : (prefixWord ++ tailWord_3745698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745698).length < 2 ^ (prefixWord ++ tailWord_3745698).sum := by decide
  have hdescent : baseEnd_3745698 < baseStart_3745698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745717 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3745717 : Nat := 118140960795 + 3745717 * 2 ^ 59
def prefixEnd_3745717 : Nat := 4983230072969 + 3 ^ 40 * 3745717 * 2
def baseEnd_3745717 : Nat := 1923353216717226598711267

theorem tailTrace_3745717 : CollatzResearch.WordTrace tailWord_3745717 prefixEnd_3745717 1923353216717226598711267 := by
  unfold tailWord_3745717
  simp only [CollatzResearch.WordTrace]
  refine ⟨136617522570914501378195405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91078348380609667585463603 136617522570914501378195405)
  ·
    refine ⟨51231570964092938016823277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136617522570914501378195405 51231570964092938016823277)
    ·
      refine ⟨19211839111534851756308729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51231570964092938016823277 19211839111534851756308729)
      ·
        refine ⟨14408879333651138817231547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19211839111534851756308729 14408879333651138817231547)
        ·
          refine ⟨21613319000476708225847321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14408879333651138817231547 21613319000476708225847321)
          ·
            refine ⟨16209989250357531169385491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21613319000476708225847321 16209989250357531169385491)
            ·
              refine ⟨24314983875536296754078237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16209989250357531169385491 24314983875536296754078237)
              ·
                refine ⟨9118118953326111282779339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24314983875536296754078237 9118118953326111282779339)
                ·
                  refine ⟨13677178429989166924169009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118118953326111282779339 13677178429989166924169009)
                  ·
                    refine ⟨10257883822491875193126757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13677178429989166924169009 10257883822491875193126757)
                    ·
                      refine ⟨1923353216717226598711267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10257883822491875193126757 1923353216717226598711267)
                      ·
                        rfl

theorem cell23_3745717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3745717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745717 prefixEnd_3745717 := by exact prefixLift 3745717
  have htrace : WordTrace (prefixWord ++ tailWord_3745717) baseStart_3745717 baseEnd_3745717 := by
    simpa [prefixWord, tailWord_3745717, baseEnd_3745717] using wordTrace_append hprefix tailTrace_3745717
  have hstable : (prefixWord ++ tailWord_3745717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745717).length < 2 ^ (prefixWord ++ tailWord_3745717).sum := by decide
  have hdescent : baseEnd_3745717 < baseStart_3745717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745737 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 3]
def baseStart_3745737 : Nat := 118140960795 + 3745737 * 2 ^ 59
def prefixEnd_3745737 : Nat := 4983230072969 + 3 ^ 40 * 3745737 * 2
def baseEnd_3745737 : Nat := 1923363486330316520461175

theorem tailTrace_3745737 : CollatzResearch.WordTrace tailWord_3745737 prefixEnd_3745737 1923363486330316520461175 := by
  unfold tailWord_3745737
  simp only [CollatzResearch.WordTrace]
  refine ⟨136618252030842044793923465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91078834687228029862615643 136618252030842044793923465)
  ·
    refine ⟨102463689023131533595442599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136618252030842044793923465 102463689023131533595442599)
    ·
      refine ⟨153695533534697300393163899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102463689023131533595442599 153695533534697300393163899)
      ·
        refine ⟨230543300302045950589745849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153695533534697300393163899 230543300302045950589745849)
        ·
          refine ⟨172907475226534462942309387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230543300302045950589745849 172907475226534462942309387)
          ·
            refine ⟨259361212839801694413464081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172907475226534462942309387 259361212839801694413464081)
            ·
              refine ⟨194520909629851270810098061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259361212839801694413464081 194520909629851270810098061)
              ·
                refine ⟨72945341111194226553786773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194520909629851270810098061 72945341111194226553786773)
                ·
                  refine ⟨3419312864587229369708755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72945341111194226553786773 3419312864587229369708755)
                  ·
                    refine ⟨5128969296880844054563133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3419312864587229369708755 5128969296880844054563133)
                    ·
                      refine ⟨1923363486330316520461175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5128969296880844054563133 1923363486330316520461175)
                      ·
                        rfl

theorem cell23_3745737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 1, 3].length) (baseStart_3745737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745737 prefixEnd_3745737 := by exact prefixLift 3745737
  have htrace : WordTrace (prefixWord ++ tailWord_3745737) baseStart_3745737 baseEnd_3745737 := by
    simpa [prefixWord, tailWord_3745737, baseEnd_3745737] using wordTrace_append hprefix tailTrace_3745737
  have hstable : (prefixWord ++ tailWord_3745737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745737).length < 2 ^ (prefixWord ++ tailWord_3745737).sum := by decide
  have hdescent : baseEnd_3745737 < baseStart_3745737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745760 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_3745760 : Nat := 118140960795 + 3745760 * 2 ^ 59
def prefixEnd_3745760 : Nat := 4983230072969 + 3 ^ 40 * 3745760 * 2
def baseEnd_3745760 : Nat := 1923375296385369930473569

theorem tailTrace_3745760 : CollatzResearch.WordTrace tailWord_3745760 prefixEnd_3745760 1923375296385369930473569 := by
  unfold tailWord_3745760
  simp only [CollatzResearch.WordTrace]
  refine ⟨68309545454879359861005367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91079393939839146481340489 68309545454879359861005367)
  ·
    refine ⟨102464318182319039791508051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68309545454879359861005367 102464318182319039791508051)
    ·
      refine ⟨153696477273478559687262077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102464318182319039791508051 153696477273478559687262077)
      ·
        refine ⟨57636178977554459882723279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153696477273478559687262077 57636178977554459882723279)
        ·
          refine ⟨86454268466331689824084919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57636178977554459882723279 86454268466331689824084919)
          ·
            refine ⟨129681402699497534736127379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86454268466331689824084919 129681402699497534736127379)
            ·
              refine ⟨194522104049246302104191069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129681402699497534736127379 194522104049246302104191069)
              ·
                refine ⟨72945789018467363289071651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194522104049246302104191069 72945789018467363289071651)
                ·
                  refine ⟨109418683527701044933607477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72945789018467363289071651 109418683527701044933607477)
                  ·
                    refine ⟨10258001580721972962525701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109418683527701044933607477 10258001580721972962525701)
                    ·
                      refine ⟨1923375296385369930473569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10258001580721972962525701 1923375296385369930473569)
                      ·
                        rfl

theorem cell23_3745760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_3745760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745760 prefixEnd_3745760 := by exact prefixLift 3745760
  have htrace : WordTrace (prefixWord ++ tailWord_3745760) baseStart_3745760 baseEnd_3745760 := by
    simpa [prefixWord, tailWord_3745760, baseEnd_3745760] using wordTrace_append hprefix tailTrace_3745760
  have hstable : (prefixWord ++ tailWord_3745760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745760).length < 2 ^ (prefixWord ++ tailWord_3745760).sum := by decide
  have hdescent : baseEnd_3745760 < baseStart_3745760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745797 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_3745797 : Nat := 118140960795 + 3745797 * 2 ^ 59
def prefixEnd_3745797 : Nat := 4983230072969 + 3 ^ 40 * 3745797 * 2
def baseEnd_3745797 : Nat := 1923394295169586285710899

theorem tailTrace_3745797 : CollatzResearch.WordTrace tailWord_3745797 prefixEnd_3745797 1923394295169586285710899 := by
  unfold tailWord_3745797
  simp only [CollatzResearch.WordTrace]
  refine ⟨136620440410624675041107645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91080293607083116694071763 136620440410624675041107645)
  ·
    refine ⟨51232665153984253140415367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136620440410624675041107645 51232665153984253140415367)
    ·
      refine ⟨76848997730976379710623051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51232665153984253140415367 76848997730976379710623051)
      ·
        refine ⟨115273496596464569565934577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76848997730976379710623051 115273496596464569565934577)
        ·
          refine ⟨86455122447348427174450933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115273496596464569565934577 86455122447348427174450933)
          ·
            refine ⟨8105167729438915047604775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86455122447348427174450933 8105167729438915047604775)
            ·
              refine ⟨12157751594158372571407163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105167729438915047604775 12157751594158372571407163)
              ·
                refine ⟨18236627391237558857110745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12157751594158372571407163 18236627391237558857110745)
                ·
                  refine ⟨13677470543428169142833059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18236627391237558857110745 13677470543428169142833059)
                  ·
                    refine ⟨20516205815142253714249589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13677470543428169142833059 20516205815142253714249589)
                    ·
                      refine ⟨1923394295169586285710899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20516205815142253714249589 1923394295169586285710899)
                      ·
                        rfl

theorem cell23_3745797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_3745797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745797 prefixEnd_3745797 := by exact prefixLift 3745797
  have htrace : WordTrace (prefixWord ++ tailWord_3745797) baseStart_3745797 baseEnd_3745797 := by
    simpa [prefixWord, tailWord_3745797, baseEnd_3745797] using wordTrace_append hprefix tailTrace_3745797
  have hstable : (prefixWord ++ tailWord_3745797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745797).length < 2 ^ (prefixWord ++ tailWord_3745797).sum := by decide
  have hdescent : baseEnd_3745797 < baseStart_3745797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745827 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 3]
def baseStart_3745827 : Nat := 118140960795 + 3745827 * 2 ^ 59
def prefixEnd_3745827 : Nat := 4983230072969 + 3 ^ 40 * 3745827 * 2
def baseEnd_3745827 : Nat := 1923409699589221168335761

theorem tailTrace_3745827 : CollatzResearch.WordTrace tailWord_3745827 prefixEnd_3745827 1923409699589221168335761 := by
  unfold tailWord_3745827
  simp only [CollatzResearch.WordTrace]
  refine ⟨136621534600515990164699735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91081023067010660109799823 136621534600515990164699735)
  ·
    refine ⟨204932301900773985247049603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136621534600515990164699735 204932301900773985247049603)
    ·
      refine ⟨307398452851160977870574405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204932301900773985247049603 307398452851160977870574405)
      ·
        refine ⟨57637209909592683350732701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307398452851160977870574405 57637209909592683350732701)
        ·
          refine ⟨21613953716097256256524763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57637209909592683350732701 21613953716097256256524763)
          ·
            refine ⟨32420930574145884384787145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21613953716097256256524763 32420930574145884384787145)
            ·
              refine ⟨24315697930609413288590359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32420930574145884384787145 24315697930609413288590359)
              ·
                refine ⟨36473546895914119932885539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24315697930609413288590359 36473546895914119932885539)
                ·
                  refine ⟨54710320343871179899328309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36473546895914119932885539 54710320343871179899328309)
                  ·
                    refine ⟨5129092532237923115562029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54710320343871179899328309 5129092532237923115562029)
                    ·
                      refine ⟨1923409699589221168335761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129092532237923115562029 1923409699589221168335761)
                      ·
                        rfl

theorem cell23_3745827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_3745827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745827 prefixEnd_3745827 := by exact prefixLift 3745827
  have htrace : WordTrace (prefixWord ++ tailWord_3745827) baseStart_3745827 baseEnd_3745827 := by
    simpa [prefixWord, tailWord_3745827, baseEnd_3745827] using wordTrace_append hprefix tailTrace_3745827
  have hstable : (prefixWord ++ tailWord_3745827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745827).length < 2 ^ (prefixWord ++ tailWord_3745827).sum := by decide
  have hdescent : baseEnd_3745827 < baseStart_3745827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745832 : List Nat := [2, 1, 5, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3745832 : Nat := 118140960795 + 3745832 * 2 ^ 59
def prefixEnd_3745832 : Nat := 4983230072969 + 3 ^ 40 * 3745832 * 2
def baseEnd_3745832 : Nat := 1923412266992493648773239

theorem tailTrace_3745832 : CollatzResearch.WordTrace tailWord_3745832 prefixEnd_3745832 1923412266992493648773239 := by
  unfold tailWord_3745832
  simp only [CollatzResearch.WordTrace]
  refine ⟨68310858482748938009315875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91081144643665250679087833 68310858482748938009315875)
  ·
    refine ⟨102466287724123407013973813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68310858482748938009315875 102466287724123407013973813)
    ·
      refine ⟨9606214474136569407560045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102466287724123407013973813 9606214474136569407560045)
      ·
        refine ⟨3602330427801213527835017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9606214474136569407560045 3602330427801213527835017)
        ·
          refine ⟨2701747820850910145876263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3602330427801213527835017 2701747820850910145876263)
          ·
            refine ⟨4052621731276365218814395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701747820850910145876263 4052621731276365218814395)
            ·
              refine ⟨6078932596914547828221593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052621731276365218814395 6078932596914547828221593)
              ·
                refine ⟨4559199447685910871166195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6078932596914547828221593 4559199447685910871166195)
                ·
                  refine ⟨6838799171528866306749293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559199447685910871166195 6838799171528866306749293)
                  ·
                    refine ⟨2564549689323324865030985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6838799171528866306749293 2564549689323324865030985)
                    ·
                      refine ⟨1923412266992493648773239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564549689323324865030985 1923412266992493648773239)
                      ·
                        rfl

theorem cell23_3745832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3745832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745832 prefixEnd_3745832 := by exact prefixLift 3745832
  have htrace : WordTrace (prefixWord ++ tailWord_3745832) baseStart_3745832 baseEnd_3745832 := by
    simpa [prefixWord, tailWord_3745832, baseEnd_3745832] using wordTrace_append hprefix tailTrace_3745832
  have hstable : (prefixWord ++ tailWord_3745832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745832).length < 2 ^ (prefixWord ++ tailWord_3745832).sum := by decide
  have hdescent : baseEnd_3745832 < baseStart_3745832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745847 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 2, 5]
def baseStart_3745847 : Nat := 118140960795 + 3745847 * 2 ^ 59
def prefixEnd_3745847 : Nat := 4983230072969 + 3 ^ 40 * 3745847 * 2
def baseEnd_3745847 : Nat := 641139989734103696695223

theorem tailTrace_3745847 : CollatzResearch.WordTrace tailWord_3745847 prefixEnd_3745847 641139989734103696695223 := by
  unfold tailWord_3745847
  simp only [CollatzResearch.WordTrace]
  refine ⟨136622264060443533580427795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91081509373629022386951863 136622264060443533580427795)
  ·
    refine ⟨204933396090665300370641693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136622264060443533580427795 204933396090665300370641693)
    ·
      refine ⟨76850023533999487638990635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204933396090665300370641693 76850023533999487638990635)
      ·
        refine ⟨115275035300999231458485953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76850023533999487638990635 115275035300999231458485953)
        ·
          refine ⟨86456276475749423593864465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115275035300999231458485953 86456276475749423593864465)
          ·
            refine ⟨64842207356812067695398349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86456276475749423593864465 64842207356812067695398349)
            ·
              refine ⟨24315827758804525385774381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64842207356812067695398349 24315827758804525385774381)
              ·
                refine ⟨9118435409551697019665393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24315827758804525385774381 9118435409551697019665393)
                ·
                  refine ⟨6838826557163772764749045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9118435409551697019665393 6838826557163772764749045)
                  ·
                    refine ⟨641139989734103696695223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6838826557163772764749045 641139989734103696695223)
                    ·
                      rfl

theorem cell23_3745847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_3745847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745847 prefixEnd_3745847 := by exact prefixLift 3745847
  have htrace : WordTrace (prefixWord ++ tailWord_3745847) baseStart_3745847 baseEnd_3745847 := by
    simpa [prefixWord, tailWord_3745847, baseEnd_3745847] using wordTrace_append hprefix tailTrace_3745847
  have hstable : (prefixWord ++ tailWord_3745847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745847).length < 2 ^ (prefixWord ++ tailWord_3745847).sum := by decide
  have hdescent : baseEnd_3745847 < baseStart_3745847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745878 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3745878 : Nat := 118140960795 + 3745878 * 2 ^ 59
def prefixEnd_3745878 : Nat := 4983230072969 + 3 ^ 40 * 3745878 * 2
def baseEnd_3745878 : Nat := 1923435887102600468798027

theorem tailTrace_3745878 : CollatzResearch.WordTrace tailWord_3745878 prefixEnd_3745878 1923435887102600468798027 := by
  unfold tailWord_3745878
  simp only [CollatzResearch.WordTrace]
  refine ⟨8538962170208201617175393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91082263148887483916537525 8538962170208201617175393)
  ·
    refine ⟨6404221627656151212881545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8538962170208201617175393 6404221627656151212881545)
    ·
      refine ⟨4803166220742113409661159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6404221627656151212881545 4803166220742113409661159)
      ·
        refine ⟨7204749331113170114491739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803166220742113409661159 7204749331113170114491739)
        ·
          refine ⟨10807123996669755171737609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204749331113170114491739 10807123996669755171737609)
          ·
            refine ⟨8105342997502316378803207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10807123996669755171737609 8105342997502316378803207)
            ·
              refine ⟨12158014496253474568204811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105342997502316378803207 12158014496253474568204811)
              ·
                refine ⟨18237021744380211852307217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158014496253474568204811 18237021744380211852307217)
                ·
                  refine ⟨13677766308285158889230413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18237021744380211852307217 13677766308285158889230413)
                  ·
                    refine ⟨5129162365606934583461405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13677766308285158889230413 5129162365606934583461405)
                    ·
                      refine ⟨1923435887102600468798027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129162365606934583461405 1923435887102600468798027)
                      ·
                        rfl

theorem cell23_3745878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3745878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745878 prefixEnd_3745878 := by exact prefixLift 3745878
  have htrace : WordTrace (prefixWord ++ tailWord_3745878) baseStart_3745878 baseEnd_3745878 := by
    simpa [prefixWord, tailWord_3745878, baseEnd_3745878] using wordTrace_append hprefix tailTrace_3745878
  have hstable : (prefixWord ++ tailWord_3745878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745878).length < 2 ^ (prefixWord ++ tailWord_3745878).sum := by decide
  have hdescent : baseEnd_3745878 < baseStart_3745878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745898 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_3745898 : Nat := 118140960795 + 3745898 * 2 ^ 59
def prefixEnd_3745898 : Nat := 4983230072969 + 3 ^ 40 * 3745898 * 2
def baseEnd_3745898 : Nat := 641148718905230130182645

theorem tailTrace_3745898 : CollatzResearch.WordTrace tailWord_3745898 prefixEnd_3745898 641148718905230130182645 := by
  unfold tailWord_3745898
  simp only [CollatzResearch.WordTrace]
  refine ⟨34156031045814692322633587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91082749455505846193689565 34156031045814692322633587)
  ·
    refine ⟨51234046568722038483950381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34156031045814692322633587 51234046568722038483950381)
    ·
      refine ⟨19212767463270764431481393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51234046568722038483950381 19212767463270764431481393)
      ·
        refine ⟨14409575597453073323611045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19212767463270764431481393 14409575597453073323611045)
        ·
          refine ⟨2701795424522451248177071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14409575597453073323611045 2701795424522451248177071)
          ·
            refine ⟨4052693136783676872265607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701795424522451248177071 4052693136783676872265607)
            ·
              refine ⟨6079039705175515308398411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052693136783676872265607 6079039705175515308398411)
              ·
                refine ⟨9118559557763272962597617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079039705175515308398411 9118559557763272962597617)
                ·
                  refine ⟨6838919668322454721948213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9118559557763272962597617 6838919668322454721948213)
                  ·
                    refine ⟨641148718905230130182645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6838919668322454721948213 641148718905230130182645)
                    ·
                      rfl

theorem cell23_3745898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_3745898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745898 prefixEnd_3745898 := by exact prefixLift 3745898
  have htrace : WordTrace (prefixWord ++ tailWord_3745898) baseStart_3745898 baseEnd_3745898 := by
    simpa [prefixWord, tailWord_3745898, baseEnd_3745898] using wordTrace_append hprefix tailTrace_3745898
  have hstable : (prefixWord ++ tailWord_3745898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745898).length < 2 ^ (prefixWord ++ tailWord_3745898).sum := by decide
  have hdescent : baseEnd_3745898 < baseStart_3745898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745904 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3]
def baseStart_3745904 : Nat := 118140960795 + 3745904 * 2 ^ 59
def prefixEnd_3745904 : Nat := 4983230072969 + 3 ^ 40 * 3745904 * 2
def baseEnd_3745904 : Nat := 1923449237599617367072907

theorem tailTrace_3745904 : CollatzResearch.WordTrace tailWord_3745904 prefixEnd_3745904 1923449237599617367072907 := by
  unfold tailWord_3745904
  simp only [CollatzResearch.WordTrace]
  refine ⟨68312171510618516157626383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91082895347491354876835177 68312171510618516157626383)
  ·
    refine ⟨102468257265927774236439575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68312171510618516157626383 102468257265927774236439575)
    ·
      refine ⟨153702385898891661354659363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102468257265927774236439575 153702385898891661354659363)
      ·
        refine ⟨230553578848337492031989045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153702385898891661354659363 230553578848337492031989045)
        ·
          refine ⟨21614398017031639877998973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230553578848337492031989045 21614398017031639877998973)
          ·
            refine ⟨8105399256386864954249615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21614398017031639877998973 8105399256386864954249615)
            ·
              refine ⟨12158098884580297431374423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105399256386864954249615 12158098884580297431374423)
              ·
                refine ⟨18237148326870446147061635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12158098884580297431374423 18237148326870446147061635)
                ·
                  refine ⟨27355722490305669220592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18237148326870446147061635 27355722490305669220592453)
                  ·
                    refine ⟨5129197966932312978861085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27355722490305669220592453 5129197966932312978861085)
                    ·
                      refine ⟨1923449237599617367072907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129197966932312978861085 1923449237599617367072907)
                      ·
                        rfl

theorem cell23_3745904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 3].length) (baseStart_3745904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745904 prefixEnd_3745904 := by exact prefixLift 3745904
  have htrace : WordTrace (prefixWord ++ tailWord_3745904) baseStart_3745904 baseEnd_3745904 := by
    simpa [prefixWord, tailWord_3745904, baseEnd_3745904] using wordTrace_append hprefix tailTrace_3745904
  have hstable : (prefixWord ++ tailWord_3745904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745904).length < 2 ^ (prefixWord ++ tailWord_3745904).sum := by decide
  have hdescent : baseEnd_3745904 < baseStart_3745904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745911 : List Nat := [1, 1, 3, 1, 1, 5, 1, 5, 1, 4]
def baseStart_3745911 : Nat := 118140960795 + 3745911 * 2 ^ 59
def prefixEnd_3745911 : Nat := 4983230072969 + 3 ^ 40 * 3745911 * 2
def baseEnd_3745911 : Nat := 641150943988066279895125

theorem tailTrace_3745911 : CollatzResearch.WordTrace tailWord_3745911 prefixEnd_3745911 641150943988066279895125 := by
  unfold tailWord_3745911
  simp only [CollatzResearch.WordTrace]
  refine ⟨136624598332211672510757587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91083065554807781673838391 136624598332211672510757587)
  ·
    refine ⟨204936897498317508766136381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136624598332211672510757587 204936897498317508766136381)
    ·
      refine ⟨76851336561869065787301143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 204936897498317508766136381 76851336561869065787301143)
      ·
        refine ⟨115277004842803598680951715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76851336561869065787301143 115277004842803598680951715)
        ·
          refine ⟨172915507264205398021427573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115277004842803598680951715 172915507264205398021427573)
          ·
            refine ⟨16210828806019256064508835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172915507264205398021427573 16210828806019256064508835)
            ·
              refine ⟨24316243209028884096763253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16210828806019256064508835 24316243209028884096763253)
              ·
                refine ⟨2279647800846457884071555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24316243209028884096763253 2279647800846457884071555)
                ·
                  refine ⟨3419471701269686826107333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279647800846457884071555 3419471701269686826107333)
                  ·
                    refine ⟨641150943988066279895125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3419471701269686826107333 641150943988066279895125)
                    ·
                      rfl

theorem cell23_3745911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_3745911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745911 prefixEnd_3745911 := by exact prefixLift 3745911
  have htrace : WordTrace (prefixWord ++ tailWord_3745911) baseStart_3745911 baseEnd_3745911 := by
    simpa [prefixWord, tailWord_3745911, baseEnd_3745911] using wordTrace_append hprefix tailTrace_3745911
  have hstable : (prefixWord ++ tailWord_3745911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745911).length < 2 ^ (prefixWord ++ tailWord_3745911).sum := by decide
  have hdescent : baseEnd_3745911 < baseStart_3745911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745927 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_3745927 : Nat := 118140960795 + 3745927 * 2 ^ 59
def prefixEnd_3745927 : Nat := 4983230072969 + 3 ^ 40 * 3745927 * 2
def baseEnd_3745927 : Nat := 1923461047654670777085301

theorem tailTrace_3745927 : CollatzResearch.WordTrace tailWord_3745927 prefixEnd_3745927 1923461047654670777085301 := by
  unfold tailWord_3745927
  simp only [CollatzResearch.WordTrace]
  refine ⟨136625181900153707243340035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91083454600102471495560023 136625181900153707243340035)
  ·
    refine ⟨204937772850230560865010053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136625181900153707243340035 204937772850230560865010053)
    ·
      refine ⟨38425832409418230162189385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 204937772850230560865010053 38425832409418230162189385)
      ·
        refine ⟨28819374307063672621642039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38425832409418230162189385 28819374307063672621642039)
        ·
          refine ⟨43229061460595508932463059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28819374307063672621642039 43229061460595508932463059)
          ·
            refine ⟨64843592190893263398694589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43229061460595508932463059 64843592190893263398694589)
            ·
              refine ⟨24316347071584973774510471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64843592190893263398694589 24316347071584973774510471)
              ·
                refine ⟨36474520607377460661765707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24316347071584973774510471 36474520607377460661765707)
                ·
                  refine ⟨54711780911066190992648561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36474520607377460661765707 54711780911066190992648561)
                  ·
                    refine ⟨41033835683299643244486421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54711780911066190992648561 41033835683299643244486421)
                    ·
                      refine ⟨1923461047654670777085301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41033835683299643244486421 1923461047654670777085301)
                      ·
                        rfl

theorem cell23_3745927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_3745927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745927 prefixEnd_3745927 := by exact prefixLift 3745927
  have htrace : WordTrace (prefixWord ++ tailWord_3745927) baseStart_3745927 baseEnd_3745927 := by
    simpa [prefixWord, tailWord_3745927, baseEnd_3745927] using wordTrace_append hprefix tailTrace_3745927
  have hstable : (prefixWord ++ tailWord_3745927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745927).length < 2 ^ (prefixWord ++ tailWord_3745927).sum := by decide
  have hdescent : baseEnd_3745927 < baseStart_3745927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745928 : List Nat := [2, 1, 3, 4, 1, 1, 2, 4, 1, 4]
def baseStart_3745928 : Nat := 118140960795 + 3745928 * 2 ^ 59
def prefixEnd_3745928 : Nat := 4983230072969 + 3 ^ 40 * 3745928 * 2
def baseEnd_3745928 : Nat := 641153853711775091057599

theorem tailTrace_3745928 : CollatzResearch.WordTrace tailWord_3745928 prefixEnd_3745928 641153853711775091057599 := by
  unfold tailWord_3745928
  simp only [CollatzResearch.WordTrace]
  refine ⟨68312609186575042207063219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91083478915433389609417625 68312609186575042207063219)
  ·
    refine ⟨102468913779862563310594829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68312609186575042207063219 102468913779862563310594829)
    ·
      refine ⟨38425842667448461241473061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102468913779862563310594829 38425842667448461241473061)
      ·
        refine ⟨7204845500146586482776199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38425842667448461241473061 7204845500146586482776199)
        ·
          refine ⟨10807268250219879724164299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7204845500146586482776199 10807268250219879724164299)
          ·
            refine ⟨16210902375329819586246449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807268250219879724164299 16210902375329819586246449)
            ·
              refine ⟨12158176781497364689684837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16210902375329819586246449 12158176781497364689684837)
              ·
                refine ⟨2279658146530755879315907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12158176781497364689684837 2279658146530755879315907)
                ·
                  refine ⟨3419487219796133818973861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279658146530755879315907 3419487219796133818973861)
                  ·
                    refine ⟨641153853711775091057599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3419487219796133818973861 641153853711775091057599)
                    ·
                      rfl

theorem cell23_3745928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_3745928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745928 prefixEnd_3745928 := by exact prefixLift 3745928
  have htrace : WordTrace (prefixWord ++ tailWord_3745928) baseStart_3745928 baseEnd_3745928 := by
    simpa [prefixWord, tailWord_3745928, baseEnd_3745928] using wordTrace_append hprefix tailTrace_3745928
  have hstable : (prefixWord ++ tailWord_3745928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745928).length < 2 ^ (prefixWord ++ tailWord_3745928).sum := by decide
  have hdescent : baseEnd_3745928 < baseStart_3745928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745962 : List Nat := [3, 1, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3745962 : Nat := 118140960795 + 3745962 * 2 ^ 59
def prefixEnd_3745962 : Nat := 4983230072969 + 3 ^ 40 * 3745962 * 2
def baseEnd_3745962 : Nat := 641159673159192713382547

theorem tailTrace_3745962 : CollatzResearch.WordTrace tailWord_3745962 prefixEnd_3745962 641159673159192713382547 := by
  unfold tailWord_3745962
  simp only [CollatzResearch.WordTrace]
  refine ⟨34156614613756727055216035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91084305636684605480576093 34156614613756727055216035)
  ·
    refine ⟨51234921920635090582824053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34156614613756727055216035 51234921920635090582824053)
    ·
      refine ⟨4803273930059539742139755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51234921920635090582824053 4803273930059539742139755)
      ·
        refine ⟨7204910895089309613209633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4803273930059539742139755 7204910895089309613209633)
        ·
          refine ⟨5403683171316982209907225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7204910895089309613209633 5403683171316982209907225)
          ·
            refine ⟨4052762378487736657430419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5403683171316982209907225 4052762378487736657430419)
            ·
              refine ⟨6079143567731604986145629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052762378487736657430419 6079143567731604986145629)
              ·
                refine ⟨2279678837899351869804611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6079143567731604986145629 2279678837899351869804611)
                ·
                  refine ⟨3419518256849027804706917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279678837899351869804611 3419518256849027804706917)
                  ·
                    refine ⟨641159673159192713382547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3419518256849027804706917 641159673159192713382547)
                    ·
                      rfl

theorem cell23_3745962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3745962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745962 prefixEnd_3745962 := by exact prefixLift 3745962
  have htrace : WordTrace (prefixWord ++ tailWord_3745962) baseStart_3745962 baseEnd_3745962 := by
    simpa [prefixWord, tailWord_3745962, baseEnd_3745962] using wordTrace_append hprefix tailTrace_3745962
  have hstable : (prefixWord ++ tailWord_3745962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745962).length < 2 ^ (prefixWord ++ tailWord_3745962).sum := by decide
  have hdescent : baseEnd_3745962 < baseStart_3745962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745967 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 3, 6]
def baseStart_3745967 : Nat := 118140960795 + 3745967 * 2 ^ 59
def prefixEnd_3745967 : Nat := 4983230072969 + 3 ^ 40 * 3745967 * 2
def baseEnd_3745967 : Nat := 641160528960283540195039

theorem tailTrace_3745967 : CollatzResearch.WordTrace tailWord_3745967 prefixEnd_3745967 641160528960283540195039 := by
  unfold tailWord_3745967
  simp only [CollatzResearch.WordTrace]
  refine ⟨136626640820008794074796155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91084427213339196049864103 136626640820008794074796155)
  ·
    refine ⟨204939961230013191112194233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136626640820008794074796155 204939961230013191112194233)
    ·
      refine ⟨153704970922509893334145675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204939961230013191112194233 153704970922509893334145675)
      ·
        refine ⟨230557456383764840001218513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153704970922509893334145675 230557456383764840001218513)
        ·
          refine ⟨172918092287823630000913885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230557456383764840001218513 172918092287823630000913885)
          ·
            refine ⟨64844284607933861250342707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172918092287823630000913885 64844284607933861250342707)
            ·
              refine ⟨97266426911900791875514061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64844284607933861250342707 97266426911900791875514061)
              ·
                refine ⟨36474910091962796953317773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97266426911900791875514061 36474910091962796953317773)
                ·
                  refine ⟨13678091284486048857494165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36474910091962796953317773 13678091284486048857494165)
                  ·
                    refine ⟨641160528960283540195039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13678091284486048857494165 641160528960283540195039)
                    ·
                      rfl

theorem cell23_3745967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 3, 6].length) (baseStart_3745967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745967 prefixEnd_3745967 := by exact prefixLift 3745967
  have htrace : WordTrace (prefixWord ++ tailWord_3745967) baseStart_3745967 baseEnd_3745967 := by
    simpa [prefixWord, tailWord_3745967, baseEnd_3745967] using wordTrace_append hprefix tailTrace_3745967
  have hstable : (prefixWord ++ tailWord_3745967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745967).length < 2 ^ (prefixWord ++ tailWord_3745967).sum := by decide
  have hdescent : baseEnd_3745967 < baseStart_3745967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745972 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3745972 : Nat := 118140960795 + 3745972 * 2 ^ 59
def prefixEnd_3745972 : Nat := 4983230072969 + 3 ^ 40 * 3745972 * 2
def baseEnd_3745972 : Nat := 1923484154284123101022595

theorem tailTrace_3745972 : CollatzResearch.WordTrace tailWord_3745972 prefixEnd_3745972 1923484154284123101022595 := by
  unfold tailWord_3745972
  simp only [CollatzResearch.WordTrace]
  refine ⟨68313411592495339964364085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91084548789993786619152113 68313411592495339964364085)
  ·
    refine ⟨6404382336796438121659133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68313411592495339964364085 6404382336796438121659133)
    ·
      refine ⟨2401643376298664295622175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6404382336796438121659133 2401643376298664295622175)
      ·
        refine ⟨3602465064447996443433263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401643376298664295622175 3602465064447996443433263)
        ·
          refine ⟨5403697596671994665149895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602465064447996443433263 5403697596671994665149895)
          ·
            refine ⟨8105546395007991997724843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403697596671994665149895 8105546395007991997724843)
            ·
              refine ⟨12158319592511987996587265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105546395007991997724843 12158319592511987996587265)
              ·
                refine ⟨9118739694383990997440449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12158319592511987996587265 9118739694383990997440449)
                ·
                  refine ⟨6839054770787993248080337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9118739694383990997440449 6839054770787993248080337)
                  ·
                    refine ⟨5129291078090994936060253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839054770787993248080337 5129291078090994936060253)
                    ·
                      refine ⟨1923484154284123101022595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129291078090994936060253 1923484154284123101022595)
                      ·
                        rfl

theorem cell23_3745972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3745972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745972 prefixEnd_3745972 := by exact prefixLift 3745972
  have htrace : WordTrace (prefixWord ++ tailWord_3745972) baseStart_3745972 baseEnd_3745972 := by
    simpa [prefixWord, tailWord_3745972, baseEnd_3745972] using wordTrace_append hprefix tailTrace_3745972
  have hstable : (prefixWord ++ tailWord_3745972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745972).length < 2 ^ (prefixWord ++ tailWord_3745972).sum := by decide
  have hdescent : baseEnd_3745972 < baseStart_3745972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3745994 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_3745994 : Nat := 118140960795 + 3745994 * 2 ^ 59
def prefixEnd_3745994 : Nat := 4983230072969 + 3 ^ 40 * 3745994 * 2
def baseEnd_3745994 : Nat := 1923495450858522014947493

theorem tailTrace_3745994 : CollatzResearch.WordTrace tailWord_3745994 prefixEnd_3745994 1923495450858522014947493 := by
  unfold tailWord_3745994
  simp only [CollatzResearch.WordTrace]
  refine ⟨34156906397727744421507259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91085083727273985124019357 34156906397727744421507259)
  ·
    refine ⟨51235359596591616632260889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34156906397727744421507259 51235359596591616632260889)
    ·
      refine ⟨38426519697443712474195667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51235359596591616632260889 38426519697443712474195667)
      ·
        refine ⟨57639779546165568711293501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38426519697443712474195667 57639779546165568711293501)
        ·
          refine ⟨21614917329812088266735063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57639779546165568711293501 21614917329812088266735063)
          ·
            refine ⟨32422375994718132400102595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21614917329812088266735063 32422375994718132400102595)
            ·
              refine ⟨48633563992077198600153893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32422375994718132400102595 48633563992077198600153893)
              ·
                refine ⟨9118793248514474737528855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48633563992077198600153893 9118793248514474737528855)
                ·
                  refine ⟨13678189872771712106293283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118793248514474737528855 13678189872771712106293283)
                  ·
                    refine ⟨20517284809157568159439925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13678189872771712106293283 20517284809157568159439925)
                    ·
                      refine ⟨1923495450858522014947493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20517284809157568159439925 1923495450858522014947493)
                      ·
                        rfl

theorem cell23_3745994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_3745994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3745994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3745994 prefixEnd_3745994 := by exact prefixLift 3745994
  have htrace : WordTrace (prefixWord ++ tailWord_3745994) baseStart_3745994 baseEnd_3745994 := by
    simpa [prefixWord, tailWord_3745994, baseEnd_3745994] using wordTrace_append hprefix tailTrace_3745994
  have hstable : (prefixWord ++ tailWord_3745994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3745994).length < 2 ^ (prefixWord ++ tailWord_3745994).sum := by decide
  have hdescent : baseEnd_3745994 < baseStart_3745994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3745994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746005 : List Nat := [1, 3, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3746005 : Nat := 118140960795 + 3746005 * 2 ^ 59
def prefixEnd_3746005 : Nat := 4983230072969 + 3 ^ 40 * 3746005 * 2
def baseEnd_3746005 : Nat := 641167033048573823969981

theorem tailTrace_3746005 : CollatzResearch.WordTrace tailWord_3746005 prefixEnd_3746005 641167033048573823969981 := by
  unfold tailWord_3746005
  simp only [CollatzResearch.WordTrace]
  refine ⟨136628026793871126564679469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91085351195914084376452979 136628026793871126564679469)
  ·
    refine ⟨51235510047701672461754801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136628026793871126564679469 51235510047701672461754801)
    ·
      refine ⟨38426632535776254346316101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51235510047701672461754801 38426632535776254346316101)
      ·
        refine ⟨7204993600458047689934269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38426632535776254346316101 7204993600458047689934269)
        ·
          refine ⟨2701872600171767883725351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7204993600458047689934269 2701872600171767883725351)
          ·
            refine ⟨4052808900257651825588027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701872600171767883725351 4052808900257651825588027)
            ·
              refine ⟨6079213350386477738382041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052808900257651825588027 6079213350386477738382041)
              ·
                refine ⟨4559410012789858303786531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079213350386477738382041 4559410012789858303786531)
                ·
                  refine ⟨6839115019184787455679797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559410012789858303786531 6839115019184787455679797)
                  ·
                    refine ⟨641167033048573823969981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6839115019184787455679797 641167033048573823969981)
                    ·
                      rfl

theorem cell23_3746005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3746005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746005 prefixEnd_3746005 := by exact prefixLift 3746005
  have htrace : WordTrace (prefixWord ++ tailWord_3746005) baseStart_3746005 baseEnd_3746005 := by
    simpa [prefixWord, tailWord_3746005, baseEnd_3746005] using wordTrace_append hprefix tailTrace_3746005
  have hstable : (prefixWord ++ tailWord_3746005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746005).length < 2 ^ (prefixWord ++ tailWord_3746005).sum := by decide
  have hdescent : baseEnd_3746005 < baseStart_3746005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746008 : List Nat := [2, 1, 2, 2, 4, 3, 1, 2, 1, 1, 4]
def baseStart_3746008 : Nat := 118140960795 + 3746008 * 2 ^ 59
def prefixEnd_3746008 : Nat := 4983230072969 + 3 ^ 40 * 3746008 * 2
def baseEnd_3746008 : Nat := 1923502639587684960172429

theorem tailTrace_3746008 : CollatzResearch.WordTrace tailWord_3746008 prefixEnd_3746008 1923502639587684960172429 := by
  unfold tailWord_3746008
  simp only [CollatzResearch.WordTrace]
  refine ⟨68314068106430129038519339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91085424141906838718025785 68314068106430129038519339)
  ·
    refine ⟨102471102159645193557779009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68314068106430129038519339 102471102159645193557779009)
    ·
      refine ⟨76853326619733895168334257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102471102159645193557779009 76853326619733895168334257)
      ·
        refine ⟨57639994964800421376250693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76853326619733895168334257 57639994964800421376250693)
        ·
          refine ⟨10807499055900079008047005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57639994964800421376250693 10807499055900079008047005)
          ·
            refine ⟨4052812145962529628017627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10807499055900079008047005 4052812145962529628017627)
            ·
              refine ⟨6079218218943794442026441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052812145962529628017627 6079218218943794442026441)
              ·
                refine ⟨4559413664207845831519831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079218218943794442026441 4559413664207845831519831)
                ·
                  refine ⟨6839120496311768747279747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559413664207845831519831 6839120496311768747279747)
                  ·
                    refine ⟨10258680744467653120919621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6839120496311768747279747 10258680744467653120919621)
                    ·
                      refine ⟨1923502639587684960172429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10258680744467653120919621 1923502639587684960172429)
                      ·
                        rfl

theorem cell23_3746008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_3746008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746008 prefixEnd_3746008 := by exact prefixLift 3746008
  have htrace : WordTrace (prefixWord ++ tailWord_3746008) baseStart_3746008 baseEnd_3746008 := by
    simpa [prefixWord, tailWord_3746008, baseEnd_3746008] using wordTrace_append hprefix tailTrace_3746008
  have hstable : (prefixWord ++ tailWord_3746008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746008).length < 2 ^ (prefixWord ++ tailWord_3746008).sum := by decide
  have hdescent : baseEnd_3746008 < baseStart_3746008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746012 : List Nat := [2, 2, 5, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_3746012 : Nat := 118140960795 + 3746012 * 2 ^ 59
def prefixEnd_3746012 : Nat := 4983230072969 + 3 ^ 40 * 3746012 * 2
def baseEnd_3746012 : Nat := 1923504693510302944522411

theorem tailTrace_3746012 : CollatzResearch.WordTrace tailWord_3746012 prefixEnd_3746012 1923504693510302944522411 := by
  unfold tailWord_3746012
  simp only [CollatzResearch.WordTrace]
  refine ⟨68314141052422883380092145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91085521403230511173456193 68314141052422883380092145)
  ·
    refine ⟨51235605789317162535069109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68314141052422883380092145 51235605789317162535069109)
    ·
      refine ⟨4803338042748483987662729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51235605789317162535069109 4803338042748483987662729)
      ·
        refine ⟨3602503532061362990747047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4803338042748483987662729 3602503532061362990747047)
        ·
          refine ⟨5403755298092044486120571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602503532061362990747047 5403755298092044486120571)
          ·
            refine ⟨8105632947138066729180857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403755298092044486120571 8105632947138066729180857)
            ·
              refine ⟨6079224710353550046885643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8105632947138066729180857 6079224710353550046885643)
              ·
                refine ⟨9118837065530325070328465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079224710353550046885643 9118837065530325070328465)
                ·
                  refine ⟨6839127799147743802746349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9118837065530325070328465 6839127799147743802746349)
                  ·
                    refine ⟨2564672924680403926029881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6839127799147743802746349 2564672924680403926029881)
                    ·
                      refine ⟨1923504693510302944522411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564672924680403926029881 1923504693510302944522411)
                      ·
                        rfl

theorem cell23_3746012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_3746012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746012 prefixEnd_3746012 := by exact prefixLift 3746012
  have htrace : WordTrace (prefixWord ++ tailWord_3746012) baseStart_3746012 baseEnd_3746012 := by
    simpa [prefixWord, tailWord_3746012, baseEnd_3746012] using wordTrace_append hprefix tailTrace_3746012
  have hstable : (prefixWord ++ tailWord_3746012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746012).length < 2 ^ (prefixWord ++ tailWord_3746012).sum := by decide
  have hdescent : baseEnd_3746012 < baseStart_3746012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746021 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3746021 : Nat := 118140960795 + 3746021 * 2 ^ 59
def prefixEnd_3746021 : Nat := 4983230072969 + 3 ^ 40 * 3746021 * 2
def baseEnd_3746021 : Nat := 1923509314836193409309869

theorem tailTrace_3746021 : CollatzResearch.WordTrace tailWord_3746021 prefixEnd_3746021 1923509314836193409309869 := by
  unfold tailWord_3746021
  simp only [CollatzResearch.WordTrace]
  refine ⟨136628610361813161297261917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91085740241208774198174611 136628610361813161297261917)
  ·
    refine ⟨51235728885679935486473219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136628610361813161297261917 51235728885679935486473219)
    ·
      refine ⟨76853593328519903229709829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51235728885679935486473219 76853593328519903229709829)
      ·
        refine ⟨14410048749097481855570593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76853593328519903229709829 14410048749097481855570593)
        ·
          refine ⟨10807536561823111391677945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14410048749097481855570593 10807536561823111391677945)
          ·
            refine ⟨8105652421367333543758459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10807536561823111391677945 8105652421367333543758459)
            ·
              refine ⟨12158478632051000315637689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105652421367333543758459 12158478632051000315637689)
              ·
                refine ⟨9118858974038250236728267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12158478632051000315637689 9118858974038250236728267)
                ·
                  refine ⟨13678288461057375355092401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9118858974038250236728267 13678288461057375355092401)
                  ·
                    refine ⟨10258716345793031516319301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13678288461057375355092401 10258716345793031516319301)
                    ·
                      refine ⟨1923509314836193409309869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10258716345793031516319301 1923509314836193409309869)
                      ·
                        rfl

theorem cell23_3746021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3746021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746021 prefixEnd_3746021 := by exact prefixLift 3746021
  have htrace : WordTrace (prefixWord ++ tailWord_3746021) baseStart_3746021 baseEnd_3746021 := by
    simpa [prefixWord, tailWord_3746021, baseEnd_3746021] using wordTrace_append hprefix tailTrace_3746021
  have hstable : (prefixWord ++ tailWord_3746021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746021).length < 2 ^ (prefixWord ++ tailWord_3746021).sum := by decide
  have hdescent : baseEnd_3746021 < baseStart_3746021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746028 : List Nat := [2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 3]
def baseStart_3746028 : Nat := 118140960795 + 3746028 * 2 ^ 59
def prefixEnd_3746028 : Nat := 4983230072969 + 3 ^ 40 * 3746028 * 2
def baseEnd_3746028 : Nat := 1923512909200774881922337

theorem tailTrace_3746028 : CollatzResearch.WordTrace tailWord_3746028 prefixEnd_3746028 1923512909200774881922337 := by
  unfold tailWord_3746028
  simp only [CollatzResearch.WordTrace]
  refine ⟨68314432836393900746383369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91085910448525200995177825 68314432836393900746383369)
  ·
    refine ⟨51235824627295425559787527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68314432836393900746383369 51235824627295425559787527)
    ·
      refine ⟨76853736940943138339681291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51235824627295425559787527 76853736940943138339681291)
      ·
        refine ⟨115280605411414707509521937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76853736940943138339681291 115280605411414707509521937)
        ·
          refine ⟨86460454058561030632141453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115280605411414707509521937 86460454058561030632141453)
          ·
            refine ⟨32422670271960386487053045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86460454058561030632141453 32422670271960386487053045)
            ·
              refine ⟨3039625337996286233161223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32422670271960386487053045 3039625337996286233161223)
              ·
                refine ⟨4559438006994429349741835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039625337996286233161223 4559438006994429349741835)
                ·
                  refine ⟨6839157010491644024612753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559438006994429349741835 6839157010491644024612753)
                  ·
                    refine ⟨5129367757868733018459565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839157010491644024612753 5129367757868733018459565)
                    ·
                      refine ⟨1923512909200774881922337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129367757868733018459565 1923512909200774881922337)
                      ·
                        rfl

theorem cell23_3746028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 3].length) (baseStart_3746028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746028 prefixEnd_3746028 := by exact prefixLift 3746028
  have htrace : WordTrace (prefixWord ++ tailWord_3746028) baseStart_3746028 baseEnd_3746028 := by
    simpa [prefixWord, tailWord_3746028, baseEnd_3746028] using wordTrace_append hprefix tailTrace_3746028
  have hstable : (prefixWord ++ tailWord_3746028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746028).length < 2 ^ (prefixWord ++ tailWord_3746028).sum := by decide
  have hdescent : baseEnd_3746028 < baseStart_3746028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746042 : List Nat := [3, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2]
def baseStart_3746042 : Nat := 118140960795 + 3746042 * 2 ^ 59
def prefixEnd_3746042 : Nat := 4983230072969 + 3 ^ 40 * 3746042 * 2
def baseEnd_3746042 : Nat := 1923520097929937827147273

theorem tailTrace_3746042 : CollatzResearch.WordTrace tailWord_3746042 prefixEnd_3746042 1923520097929937827147273 := by
  unfold tailWord_3746042
  simp only [CollatzResearch.WordTrace]
  refine ⟨34157344073684270470944095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91086250863158054589184253 34157344073684270470944095)
  ·
    refine ⟨51236016110526405706416143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34157344073684270470944095 51236016110526405706416143)
    ·
      refine ⟨76854024165789608559624215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51236016110526405706416143 76854024165789608559624215)
      ·
        refine ⟨115281036248684412839436323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76854024165789608559624215 115281036248684412839436323)
        ·
          refine ⟨172921554373026619259154485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115281036248684412839436323 172921554373026619259154485)
          ·
            refine ⟨16211395722471245555545733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 172921554373026619259154485 16211395722471245555545733)
            ·
              refine ⟨3039636697963358541664825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16211395722471245555545733 3039636697963358541664825)
              ·
                refine ⟨2279727523472518906248619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039636697963358541664825 2279727523472518906248619)
                ·
                  refine ⟨3419591285208778359372929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2279727523472518906248619 3419591285208778359372929)
                  ·
                    refine ⟨2564693463906583769529697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3419591285208778359372929 2564693463906583769529697)
                    ·
                      refine ⟨1923520097929937827147273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564693463906583769529697 1923520097929937827147273)
                      ·
                        rfl

theorem cell23_3746042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2].length) (baseStart_3746042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746042 prefixEnd_3746042 := by exact prefixLift 3746042
  have htrace : WordTrace (prefixWord ++ tailWord_3746042) baseStart_3746042 baseEnd_3746042 := by
    simpa [prefixWord, tailWord_3746042, baseEnd_3746042] using wordTrace_append hprefix tailTrace_3746042
  have hstable : (prefixWord ++ tailWord_3746042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746042).length < 2 ^ (prefixWord ++ tailWord_3746042).sum := by decide
  have hdescent : baseEnd_3746042 < baseStart_3746042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746044 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_3746044 : Nat := 118140960795 + 3746044 * 2 ^ 59
def prefixEnd_3746044 : Nat := 4983230072969 + 3 ^ 40 * 3746044 * 2
def baseEnd_3746044 : Nat := 641173708297082273107421

theorem tailTrace_3746044 : CollatzResearch.WordTrace tailWord_3746044 prefixEnd_3746044 641173708297082273107421 := by
  unfold tailWord_3746044
  simp only [CollatzResearch.WordTrace]
  refine ⟨68314724620364918112674593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91086299493819890816899457 68314724620364918112674593)
  ·
    refine ⟨51236043465273688584505945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68314724620364918112674593 51236043465273688584505945)
    ·
      refine ⟨38427032598955266438379459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51236043465273688584505945 38427032598955266438379459)
      ·
        refine ⟨57640548898432899657569189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38427032598955266438379459 57640548898432899657569189)
        ·
          refine ⟨10807602918456168685794223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57640548898432899657569189 10807602918456168685794223)
          ·
            refine ⟨16211404377684253028691335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807602918456168685794223 16211404377684253028691335)
            ·
              refine ⟨24317106566526379543037003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16211404377684253028691335 24317106566526379543037003)
              ·
                refine ⟨36475659849789569314555505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24317106566526379543037003 36475659849789569314555505)
                ·
                  refine ⟨27356744887342176985916629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36475659849789569314555505 27356744887342176985916629)
                  ·
                    refine ⟨641173708297082273107421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27356744887342176985916629 641173708297082273107421)
                    ·
                      rfl

theorem cell23_3746044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_3746044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746044 prefixEnd_3746044 := by exact prefixLift 3746044
  have htrace : WordTrace (prefixWord ++ tailWord_3746044) baseStart_3746044 baseEnd_3746044 := by
    simpa [prefixWord, tailWord_3746044, baseEnd_3746044] using wordTrace_append hprefix tailTrace_3746044
  have hstable : (prefixWord ++ tailWord_3746044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746044).length < 2 ^ (prefixWord ++ tailWord_3746044).sum := by decide
  have hdescent : baseEnd_3746044 < baseStart_3746044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746051 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 5, 3, 2]
def baseStart_3746051 : Nat := 118140960795 + 3746051 * 2 ^ 59
def prefixEnd_3746051 : Nat := 4983230072969 + 3 ^ 40 * 3746051 * 2
def baseEnd_3746051 : Nat := 1923524719255828291934731

theorem tailTrace_3746051 : CollatzResearch.WordTrace tailWord_3746051 prefixEnd_3746051 1923524719255828291934731 := by
  unfold tailWord_3746051
  simp only [CollatzResearch.WordTrace]
  refine ⟨136629704551704476420854007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91086469701136317613902671 136629704551704476420854007)
  ·
    refine ⟨204944556827556714631281011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136629704551704476420854007 204944556827556714631281011)
    ·
      refine ⟨307416835241335071946921517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204944556827556714631281011 307416835241335071946921517)
      ·
        refine ⟨115281313215500651980095569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307416835241335071946921517 115281313215500651980095569)
        ·
          refine ⟨86460984911625488985071677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115281313215500651980095569 86460984911625488985071677)
          ·
            refine ⟨32422869341859558369401879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86460984911625488985071677 32422869341859558369401879)
            ·
              refine ⟨48634304012789337554102819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32422869341859558369401879 48634304012789337554102819)
              ·
                refine ⟨72951456019184006331154229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48634304012789337554102819 72951456019184006331154229)
                ·
                  refine ⟨6839199001798500593545709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72951456019184006331154229 6839199001798500593545709)
                  ·
                    refine ⟨2564699625674437722579641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6839199001798500593545709 2564699625674437722579641)
                    ·
                      refine ⟨1923524719255828291934731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564699625674437722579641 1923524719255828291934731)
                      ·
                        rfl

theorem cell23_3746051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_3746051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746051 prefixEnd_3746051 := by exact prefixLift 3746051
  have htrace : WordTrace (prefixWord ++ tailWord_3746051) baseStart_3746051 baseEnd_3746051 := by
    simpa [prefixWord, tailWord_3746051, baseEnd_3746051] using wordTrace_append hprefix tailTrace_3746051
  have hstable : (prefixWord ++ tailWord_3746051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746051).length < 2 ^ (prefixWord ++ tailWord_3746051).sum := by decide
  have hdescent : baseEnd_3746051 < baseStart_3746051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746058 : List Nat := [3, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_3746058 : Nat := 118140960795 + 3746058 * 2 ^ 59
def prefixEnd_3746058 : Nat := 4983230072969 + 3 ^ 40 * 3746058 * 2
def baseEnd_3746058 : Nat := 1923528313620409764547199

theorem tailTrace_3746058 : CollatzResearch.WordTrace tailWord_3746058 prefixEnd_3746058 1923528313620409764547199 := by
  unfold tailWord_3746058
  simp only [CollatzResearch.WordTrace]
  refine ⟨34157489965669779154089707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91086639908452744410905885 34157489965669779154089707)
  ·
    refine ⟨51236234948504668731134561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34157489965669779154089707 51236234948504668731134561)
    ·
      refine ⟨38427176211378501548350921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51236234948504668731134561 38427176211378501548350921)
      ·
        refine ⟨28820382158533876161263191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38427176211378501548350921 28820382158533876161263191)
        ·
          refine ⟨43230573237800814241894787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28820382158533876161263191 43230573237800814241894787)
          ·
            refine ⟨64845859856701221362842181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43230573237800814241894787 64845859856701221362842181)
            ·
              refine ⟨12158598723131479005532909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64845859856701221362842181 12158598723131479005532909)
              ·
                refine ⟨4559474521174304627074841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12158598723131479005532909 4559474521174304627074841)
                ·
                  refine ⟨3419605890880728470306131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4559474521174304627074841 3419605890880728470306131)
                  ·
                    refine ⟨5129408836321092705459197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3419605890880728470306131 5129408836321092705459197)
                    ·
                      refine ⟨1923528313620409764547199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129408836321092705459197 1923528313620409764547199)
                      ·
                        rfl

theorem cell23_3746058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_3746058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746058 prefixEnd_3746058 := by exact prefixLift 3746058
  have htrace : WordTrace (prefixWord ++ tailWord_3746058) baseStart_3746058 baseEnd_3746058 := by
    simpa [prefixWord, tailWord_3746058, baseEnd_3746058] using wordTrace_append hprefix tailTrace_3746058
  have hstable : (prefixWord ++ tailWord_3746058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746058).length < 2 ^ (prefixWord ++ tailWord_3746058).sum := by decide
  have hdescent : baseEnd_3746058 < baseStart_3746058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746085 : List Nat := [1, 3, 1, 2, 5, 1, 1, 3, 1, 3, 2]
def baseStart_3746085 : Nat := 118140960795 + 3746085 * 2 ^ 59
def prefixEnd_3746085 : Nat := 4983230072969 + 3 ^ 40 * 3746085 * 2
def baseEnd_3746085 : Nat := 1923542177598081158909575

theorem tailTrace_3746085 : CollatzResearch.WordTrace tailWord_3746085 prefixEnd_3746085 1923542177598081158909575 := by
  unfold tailWord_3746085
  simp only [CollatzResearch.WordTrace]
  refine ⟨136630944633581300227591709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91087296422387533485061139 136630944633581300227591709)
  ·
    refine ⟨51236604237592987585346891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136630944633581300227591709 51236604237592987585346891)
    ·
      refine ⟨76854906356389481378020337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51236604237592987585346891 76854906356389481378020337)
      ·
        refine ⟨57641179767292111033515253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76854906356389481378020337 57641179767292111033515253)
        ·
          refine ⟨5403860603183635409392055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57641179767292111033515253 5403860603183635409392055)
          ·
            refine ⟨8105790904775453114088083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5403860603183635409392055 8105790904775453114088083)
            ·
              refine ⟨12158686357163179671132125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8105790904775453114088083 12158686357163179671132125)
              ·
                refine ⟨4559507383936192376674547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12158686357163179671132125 4559507383936192376674547)
                ·
                  refine ⟨6839261075904288565011821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559507383936192376674547 6839261075904288565011821)
                  ·
                    refine ⟨2564722903464108211879433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6839261075904288565011821 2564722903464108211879433)
                    ·
                      refine ⟨1923542177598081158909575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564722903464108211879433 1923542177598081158909575)
                      ·
                        rfl

theorem cell23_3746085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_3746085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746085 prefixEnd_3746085 := by exact prefixLift 3746085
  have htrace : WordTrace (prefixWord ++ tailWord_3746085) baseStart_3746085 baseEnd_3746085 := by
    simpa [prefixWord, tailWord_3746085, baseEnd_3746085] using wordTrace_append hprefix tailTrace_3746085
  have hstable : (prefixWord ++ tailWord_3746085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746085).length < 2 ^ (prefixWord ++ tailWord_3746085).sum := by decide
  have hdescent : baseEnd_3746085 < baseStart_3746085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746104 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 7]
def baseStart_3746104 : Nat := 118140960795 + 3746104 * 2 ^ 59
def prefixEnd_3746104 : Nat := 4983230072969 + 3 ^ 40 * 3746104 * 2
def baseEnd_3746104 : Nat := 213727992636724064952443

theorem tailTrace_3746104 : CollatzResearch.WordTrace tailWord_3746104 prefixEnd_3746104 213727992636724064952443 := by
  unfold tailWord_3746104
  simp only [CollatzResearch.WordTrace]
  refine ⟨68315818810256233236266683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91087758413674977648355577 68315818810256233236266683)
  ·
    refine ⟨102473728215384349854400025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68315818810256233236266683 102473728215384349854400025)
    ·
      refine ⟨76855296161538262390800019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102473728215384349854400025 76855296161538262390800019)
      ·
        refine ⟨115282944242307393586200029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76855296161538262390800019 115282944242307393586200029)
        ·
          refine ⟨43231104090865272594825011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115282944242307393586200029 43231104090865272594825011)
          ·
            refine ⟨64846656136297908892237517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43231104090865272594825011 64846656136297908892237517)
            ·
              refine ⟨24317496051111715834589069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64846656136297908892237517 24317496051111715834589069)
              ·
                refine ⟨9119061019166893437970901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24317496051111715834589069 9119061019166893437970901)
                ·
                  refine ⟨213727992636724064952443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9119061019166893437970901 213727992636724064952443)
                  ·
                    rfl

theorem cell23_3746104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_3746104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746104 prefixEnd_3746104 := by exact prefixLift 3746104
  have htrace : WordTrace (prefixWord ++ tailWord_3746104) baseStart_3746104 baseEnd_3746104 := by
    simpa [prefixWord, tailWord_3746104, baseEnd_3746104] using wordTrace_append hprefix tailTrace_3746104
  have hstable : (prefixWord ++ tailWord_3746104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746104).length < 2 ^ (prefixWord ++ tailWord_3746104).sum := by decide
  have hdescent : baseEnd_3746104 < baseStart_3746104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746151 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 4, 5]
def baseStart_3746151 : Nat := 118140960795 + 3746151 * 2 ^ 59
def prefixEnd_3746151 : Nat := 4983230072969 + 3 ^ 40 * 3746151 * 2
def baseEnd_3746151 : Nat := 641192022440425966894757

theorem tailTrace_3746151 : CollatzResearch.WordTrace tailWord_3746151 prefixEnd_3746151 641192022440425966894757 := by
  unfold tailWord_3746151
  simp only [CollatzResearch.WordTrace]
  refine ⟨136633351851342193499494307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91088901234228128999662871 136633351851342193499494307)
  ·
    refine ⟨204950027777013290249241461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136633351851342193499494307 204950027777013290249241461)
    ·
      refine ⟨19214065104094995960866387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 204950027777013290249241461 19214065104094995960866387)
      ·
        refine ⟨28821097656142493941299581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19214065104094995960866387 28821097656142493941299581)
        ·
          refine ⟨10807911621053435227987343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28821097656142493941299581 10807911621053435227987343)
          ·
            refine ⟨16211867431580152841981015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807911621053435227987343 16211867431580152841981015)
            ·
              refine ⟨24317801147370229262971523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16211867431580152841981015 24317801147370229262971523)
              ·
                refine ⟨36476701721055343894457285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24317801147370229262971523 36476701721055343894457285)
                ·
                  refine ⟨6839381572697876980210741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36476701721055343894457285 6839381572697876980210741)
                  ·
                    refine ⟨641192022440425966894757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6839381572697876980210741 641192022440425966894757)
                    ·
                      rfl

theorem cell23_3746151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_3746151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746151 prefixEnd_3746151 := by exact prefixLift 3746151
  have htrace : WordTrace (prefixWord ++ tailWord_3746151) baseStart_3746151 baseEnd_3746151 := by
    simpa [prefixWord, tailWord_3746151, baseEnd_3746151] using wordTrace_append hprefix tailTrace_3746151
  have hstable : (prefixWord ++ tailWord_3746151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746151).length < 2 ^ (prefixWord ++ tailWord_3746151).sum := by decide
  have hdescent : baseEnd_3746151 < baseStart_3746151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746181 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_3746181 : Nat := 118140960795 + 3746181 * 2 ^ 59
def prefixEnd_3746181 : Nat := 4983230072969 + 3 ^ 40 * 3746181 * 2
def baseEnd_3746181 : Nat := 641197157246970927769711

theorem tailTrace_3746181 : CollatzResearch.WordTrace tailWord_3746181 prefixEnd_3746181 641197157246970927769711 := by
  unfold tailWord_3746181
  simp only [CollatzResearch.WordTrace]
  refine ⟨136634446041233508623086397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91089630694155672415390931 136634446041233508623086397)
  ·
    refine ⟨51237917265462565733657399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136634446041233508623086397 51237917265462565733657399)
    ·
      refine ⟨76856875898193848600486099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51237917265462565733657399 76856875898193848600486099)
      ·
        refine ⟨115285313847290772900729149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76856875898193848600486099 115285313847290772900729149)
        ·
          refine ⟨43231992692734039837773431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115285313847290772900729149 43231992692734039837773431)
          ·
            refine ⟨64847989039101059756660147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43231992692734039837773431 64847989039101059756660147)
            ·
              refine ⟨97271983558651589634990221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64847989039101059756660147 97271983558651589634990221)
              ·
                refine ⟨36476993834494346113121333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97271983558651589634990221 36476993834494346113121333)
                ·
                  refine ⟨3419718171983844948105125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36476993834494346113121333 3419718171983844948105125)
                  ·
                    refine ⟨641197157246970927769711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3419718171983844948105125 641197157246970927769711)
                    ·
                      rfl

theorem cell23_3746181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_3746181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746181 prefixEnd_3746181 := by exact prefixLift 3746181
  have htrace : WordTrace (prefixWord ++ tailWord_3746181) baseStart_3746181 baseEnd_3746181 := by
    simpa [prefixWord, tailWord_3746181, baseEnd_3746181] using wordTrace_append hprefix tailTrace_3746181
  have hstable : (prefixWord ++ tailWord_3746181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746181).length < 2 ^ (prefixWord ++ tailWord_3746181).sum := by decide
  have hdescent : baseEnd_3746181 < baseStart_3746181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746188 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_3746188 : Nat := 118140960795 + 3746188 * 2 ^ 59
def prefixEnd_3746188 : Nat := 4983230072969 + 3 ^ 40 * 3746188 * 2
def baseEnd_3746188 : Nat := 1923595066105494255921601

theorem tailTrace_3746188 : CollatzResearch.WordTrace tailWord_3746188 prefixEnd_3746188 1923595066105494255921601 := by
  unfold tailWord_3746188
  simp only [CollatzResearch.WordTrace]
  refine ⟨68317350676104074409295609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91089800901472099212394145 68317350676104074409295609)
  ·
    refine ⟨51238013007078055806971707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68317350676104074409295609 51238013007078055806971707)
    ·
      refine ⟨76857019510617083710457561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51238013007078055806971707 76857019510617083710457561)
      ·
        refine ⟨57642764632962812782843171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76857019510617083710457561 57642764632962812782843171)
        ·
          refine ⟨86464146949444219174264757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57642764632962812782843171 86464146949444219174264757)
          ·
            refine ⟨8106013776510395547587321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86464146949444219174264757 8106013776510395547587321)
            ·
              refine ⟨6079510332382796660690491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8106013776510395547587321 6079510332382796660690491)
              ·
                refine ⟨9119265498574194991035737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6079510332382796660690491 9119265498574194991035737)
                ·
                  refine ⟨6839449123930646243276803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9119265498574194991035737 6839449123930646243276803)
                  ·
                    refine ⟨10259173685895969364915205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6839449123930646243276803 10259173685895969364915205)
                    ·
                      refine ⟨1923595066105494255921601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10259173685895969364915205 1923595066105494255921601)
                      ·
                        rfl

theorem cell23_3746188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_3746188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746188 prefixEnd_3746188 := by exact prefixLift 3746188
  have htrace : WordTrace (prefixWord ++ tailWord_3746188) baseStart_3746188 baseEnd_3746188 := by
    simpa [prefixWord, tailWord_3746188, baseEnd_3746188] using wordTrace_append hprefix tailTrace_3746188
  have hstable : (prefixWord ++ tailWord_3746188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746188).length < 2 ^ (prefixWord ++ tailWord_3746188).sum := by decide
  have hdescent : baseEnd_3746188 < baseStart_3746188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746208 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3]
def baseStart_3746208 : Nat := 118140960795 + 3746208 * 2 ^ 59
def prefixEnd_3746208 : Nat := 4983230072969 + 3 ^ 40 * 3746208 * 2
def baseEnd_3746208 : Nat := 1923605335718584177671509

theorem tailTrace_3746208 : CollatzResearch.WordTrace tailWord_3746208 prefixEnd_3746208 1923605335718584177671509 := by
  unfold tailWord_3746208
  simp only [CollatzResearch.WordTrace]
  refine ⟨68317715406067846117159639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91090287208090461489546185 68317715406067846117159639)
  ·
    refine ⟨102476573109101769175739459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68317715406067846117159639 102476573109101769175739459)
    ·
      refine ⟨153714859663652653763609189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102476573109101769175739459 153714859663652653763609189)
      ·
        refine ⟨28821536186934872580676723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153714859663652653763609189 28821536186934872580676723)
        ·
          refine ⟨43232304280402308871015085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28821536186934872580676723 43232304280402308871015085)
          ·
            refine ⟨16212114105150865826630657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43232304280402308871015085 16212114105150865826630657)
            ·
              refine ⟨12159085578863149369972993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16212114105150865826630657 12159085578863149369972993)
              ·
                refine ⟨9119314184147362027479745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12159085578863149369972993 9119314184147362027479745)
                ·
                  refine ⟨6839485638110521520609809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9119314184147362027479745 6839485638110521520609809)
                  ·
                    refine ⟨5129614228582891140457357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839485638110521520609809 5129614228582891140457357)
                    ·
                      refine ⟨1923605335718584177671509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129614228582891140457357 1923605335718584177671509)
                      ·
                        rfl

theorem cell23_3746208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_3746208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746208 prefixEnd_3746208 := by exact prefixLift 3746208
  have htrace : WordTrace (prefixWord ++ tailWord_3746208) baseStart_3746208 baseEnd_3746208 := by
    simpa [prefixWord, tailWord_3746208, baseEnd_3746208] using wordTrace_append hprefix tailTrace_3746208
  have hstable : (prefixWord ++ tailWord_3746208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746208).length < 2 ^ (prefixWord ++ tailWord_3746208).sum := by decide
  have hdescent : baseEnd_3746208 < baseStart_3746208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746211 : List Nat := [1, 1, 1, 4, 1, 4, 1, 4, 6]
def baseStart_3746211 : Nat := 118140960795 + 3746211 * 2 ^ 59
def prefixEnd_3746211 : Nat := 4983230072969 + 3 ^ 40 * 3746211 * 2
def baseEnd_3746211 : Nat := 213734097351171962881555

theorem tailTrace_3746211 : CollatzResearch.WordTrace tailWord_3746211 prefixEnd_3746211 213734097351171962881555 := by
  unfold tailWord_3746211
  simp only [CollatzResearch.WordTrace]
  refine ⟨136635540231124823746678487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91090360154083215831118991 136635540231124823746678487)
  ·
    refine ⟨204953310346687235620017731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136635540231124823746678487 204953310346687235620017731)
    ·
      refine ⟨307429965520030853430026597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204953310346687235620017731 307429965520030853430026597)
      ·
        refine ⟨57643118535005785018129987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307429965520030853430026597 57643118535005785018129987)
        ·
          refine ⟨86464677802508677527194981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57643118535005785018129987 86464677802508677527194981)
          ·
            refine ⟨16212127087970377036349059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86464677802508677527194981 16212127087970377036349059)
            ·
              refine ⟨24318190631955565554523589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16212127087970377036349059 24318190631955565554523589)
              ·
                refine ⟨4559660743491668541473173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24318190631955565554523589 4559660743491668541473173)
                ·
                  refine ⟨213734097351171962881555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4559660743491668541473173 213734097351171962881555)
                  ·
                    rfl

theorem cell23_3746211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 4, 6].length) (baseStart_3746211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746211 prefixEnd_3746211 := by exact prefixLift 3746211
  have htrace : WordTrace (prefixWord ++ tailWord_3746211) baseStart_3746211 baseEnd_3746211 := by
    simpa [prefixWord, tailWord_3746211, baseEnd_3746211] using wordTrace_append hprefix tailTrace_3746211
  have hstable : (prefixWord ++ tailWord_3746211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746211).length < 2 ^ (prefixWord ++ tailWord_3746211).sum := by decide
  have hdescent : baseEnd_3746211 < baseStart_3746211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746281 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 3]
def baseStart_3746281 : Nat := 118140960795 + 3746281 * 2 ^ 59
def prefixEnd_3746281 : Nat := 4983230072969 + 3 ^ 40 * 3746281 * 2
def baseEnd_3746281 : Nat := 1923642819806362392058673

theorem tailTrace_3746281 : CollatzResearch.WordTrace tailWord_3746281 prefixEnd_3746281 1923642819806362392058673 := by
  unfold tailWord_3746281
  simp only [CollatzResearch.WordTrace]
  refine ⟨136638093340871225701726697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91092062227247483801151131 136638093340871225701726697)
  ·
    refine ⟨102478570005653419276295023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136638093340871225701726697 102478570005653419276295023)
    ·
      refine ⟨153717855008480128914442535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102478570005653419276295023 153717855008480128914442535)
      ·
        refine ⟨230576782512720193371663803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153717855008480128914442535 230576782512720193371663803)
        ·
          refine ⟨345865173769080290057495705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230576782512720193371663803 345865173769080290057495705)
          ·
            refine ⟨259398880326810217543121779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345865173769080290057495705 259398880326810217543121779)
            ·
              refine ⟨389098320490215326314682669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259398880326810217543121779 389098320490215326314682669)
              ·
                refine ⟨145911870183830747368006001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389098320490215326314682669 145911870183830747368006001)
                ·
                  refine ⟨109433902637873060526004501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145911870183830747368006001 109433902637873060526004501)
                  ·
                    refine ⟨5129714186150299712156461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109433902637873060526004501 5129714186150299712156461)
                    ·
                      refine ⟨1923642819806362392058673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129714186150299712156461 1923642819806362392058673)
                      ·
                        rfl

theorem cell23_3746281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 2, 6, 3].length) (baseStart_3746281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746281 prefixEnd_3746281 := by exact prefixLift 3746281
  have htrace : WordTrace (prefixWord ++ tailWord_3746281) baseStart_3746281 baseEnd_3746281 := by
    simpa [prefixWord, tailWord_3746281, baseEnd_3746281] using wordTrace_append hprefix tailTrace_3746281
  have hstable : (prefixWord ++ tailWord_3746281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746281).length < 2 ^ (prefixWord ++ tailWord_3746281).sum := by decide
  have hdescent : baseEnd_3746281 < baseStart_3746281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746291 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6]
def baseStart_3746291 : Nat := 118140960795 + 3746291 * 2 ^ 59
def prefixEnd_3746291 : Nat := 4983230072969 + 3 ^ 40 * 3746291 * 2
def baseEnd_3746291 : Nat := 1923647954612907352933627

theorem tailTrace_3746291 : CollatzResearch.WordTrace tailWord_3746291 prefixEnd_3746291 1923647954612907352933627 := by
  unfold tailWord_3746291
  simp only [CollatzResearch.WordTrace]
  refine ⟨136638458070834997409590727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91092305380556664939727151 136638458070834997409590727)
  ·
    refine ⟨204957687106252496114386091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136638458070834997409590727 204957687106252496114386091)
    ·
      refine ⟨307436530659378744171579137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204957687106252496114386091 307436530659378744171579137)
      ·
        refine ⟨230577397994534058128684353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307436530659378744171579137 230577397994534058128684353)
        ·
          refine ⟨172933048495900543596513265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230577397994534058128684353 172933048495900543596513265)
          ·
            refine ⟨129699786371925407697384949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172933048495900543596513265 129699786371925407697384949)
            ·
              refine ⟨12159354972368006971629839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129699786371925407697384949 12159354972368006971629839)
              ·
                refine ⟨18239032458552010457444759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12159354972368006971629839 18239032458552010457444759)
                ·
                  refine ⟨27358548687828015686167139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18239032458552010457444759 27358548687828015686167139)
                  ·
                    refine ⟨41037823031742023529250709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27358548687828015686167139 41037823031742023529250709)
                    ·
                      refine ⟨1923647954612907352933627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41037823031742023529250709 1923647954612907352933627)
                      ·
                        rfl

theorem cell23_3746291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_3746291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746291 prefixEnd_3746291 := by exact prefixLift 3746291
  have htrace : WordTrace (prefixWord ++ tailWord_3746291) baseStart_3746291 baseEnd_3746291 := by
    simpa [prefixWord, tailWord_3746291, baseEnd_3746291] using wordTrace_append hprefix tailTrace_3746291
  have hstable : (prefixWord ++ tailWord_3746291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746291).length < 2 ^ (prefixWord ++ tailWord_3746291).sum := by decide
  have hdescent : baseEnd_3746291 < baseStart_3746291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746301 : List Nat := [1, 4, 1, 1, 1, 3, 3, 9]
def baseStart_3746301 : Nat := 118140960795 + 3746301 * 2 ^ 59
def prefixEnd_3746301 : Nat := 4983230072969 + 3 ^ 40 * 3746301 * 2
def baseEnd_3746301 : Nat := 71246410719238974585503

theorem tailTrace_3746301 : CollatzResearch.WordTrace tailWord_3746301 prefixEnd_3746301 71246410719238974585503 := by
  unfold tailWord_3746301
  simp only [CollatzResearch.WordTrace]
  refine ⟨136638822800798769117454757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91092548533865846078303171 136638822800798769117454757)
  ·
    refine ⟨25619779275149769209522767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136638822800798769117454757 25619779275149769209522767)
    ·
      refine ⟨38429668912724653814284151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25619779275149769209522767 38429668912724653814284151)
      ·
        refine ⟨57644503369086980721426227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38429668912724653814284151 57644503369086980721426227)
        ·
          refine ⟨86466755053630471082139341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57644503369086980721426227 86466755053630471082139341)
          ·
            refine ⟨32425033145111426655802253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86466755053630471082139341 32425033145111426655802253)
            ·
              refine ⟨12159387429416784995925845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32425033145111426655802253 12159387429416784995925845)
              ·
                refine ⟨71246410719238974585503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12159387429416784995925845 71246410719238974585503)
                ·
                  rfl

theorem cell23_3746301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 9].length) (baseStart_3746301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746301 prefixEnd_3746301 := by exact prefixLift 3746301
  have htrace : WordTrace (prefixWord ++ tailWord_3746301) baseStart_3746301 baseEnd_3746301 := by
    simpa [prefixWord, tailWord_3746301, baseEnd_3746301] using wordTrace_append hprefix tailTrace_3746301
  have hstable : (prefixWord ++ tailWord_3746301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746301).length < 2 ^ (prefixWord ++ tailWord_3746301).sum := by decide
  have hdescent : baseEnd_3746301 < baseStart_3746301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746315 : List Nat := [1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 3]
def baseStart_3746315 : Nat := 118140960795 + 3746315 * 2 ^ 59
def prefixEnd_3746315 : Nat := 4983230072969 + 3 ^ 40 * 3746315 * 2
def baseEnd_3746315 : Nat := 1923660278148615259033517

theorem tailTrace_3746315 : CollatzResearch.WordTrace tailWord_3746315 prefixEnd_3746315 1923660278148615259033517 := by
  unfold tailWord_3746315
  simp only [CollatzResearch.WordTrace]
  refine ⟨136639333422748049508464399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91092888948498699672309599 136639333422748049508464399)
  ·
    refine ⟨204959000134122074262696599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136639333422748049508464399 204959000134122074262696599)
    ·
      refine ⟨307438500201183111394044899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204959000134122074262696599 307438500201183111394044899)
      ·
        refine ⟨461157750301774667091067349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307438500201183111394044899 461157750301774667091067349)
        ·
          refine ⟨10808384772697843759946891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 461157750301774667091067349 10808384772697843759946891)
          ·
            refine ⟨16212577159046765639920337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10808384772697843759946891 16212577159046765639920337)
            ·
              refine ⟨12159432869285074229940253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16212577159046765639920337 12159432869285074229940253)
              ·
                refine ⟨4559787325981902836227595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12159432869285074229940253 4559787325981902836227595)
                ·
                  refine ⟨6839680988972854254341393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559787325981902836227595 6839680988972854254341393)
                  ·
                    refine ⟨5129760741729640690756045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839680988972854254341393 5129760741729640690756045)
                    ·
                      refine ⟨1923660278148615259033517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129760741729640690756045 1923660278148615259033517)
                      ·
                        rfl

theorem cell23_3746315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 2, 3].length) (baseStart_3746315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746315 prefixEnd_3746315 := by exact prefixLift 3746315
  have htrace : WordTrace (prefixWord ++ tailWord_3746315) baseStart_3746315 baseEnd_3746315 := by
    simpa [prefixWord, tailWord_3746315, baseEnd_3746315] using wordTrace_append hprefix tailTrace_3746315
  have hstable : (prefixWord ++ tailWord_3746315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746315).length < 2 ^ (prefixWord ++ tailWord_3746315).sum := by decide
  have hdescent : baseEnd_3746315 < baseStart_3746315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746318 : List Nat := [4, 1, 1, 2, 3, 3, 9]
def baseStart_3746318 : Nat := 118140960795 + 3746318 * 2 ^ 59
def prefixEnd_3746318 : Nat := 4983230072969 + 3 ^ 40 * 3746318 * 2
def baseEnd_3746318 : Nat := 23748911340624428978963

theorem tailTrace_3746318 : CollatzResearch.WordTrace tailWord_3746318 prefixEnd_3746318 23748911340624428978963 := by
  unfold tailWord_3746318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079930355217147627602951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91092961894491454013882405 17079930355217147627602951)
  ·
    refine ⟨25619895532825721441404427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17079930355217147627602951 25619895532825721441404427)
    ·
      refine ⟨38429843299238582162106641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25619895532825721441404427 38429843299238582162106641)
      ·
        refine ⟨28822382474428936621579981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38429843299238582162106641 28822382474428936621579981)
        ·
          refine ⟨10808393427910851233092493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28822382474428936621579981 10808393427910851233092493)
          ·
            refine ⟨4053147535466569212409685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10808393427910851233092493 4053147535466569212409685)
            ·
              refine ⟨23748911340624428978963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4053147535466569212409685 23748911340624428978963)
              ·
                rfl

theorem cell23_3746318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 9].length) (baseStart_3746318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746318 prefixEnd_3746318 := by exact prefixLift 3746318
  have htrace : WordTrace (prefixWord ++ tailWord_3746318) baseStart_3746318 baseEnd_3746318 := by
    simpa [prefixWord, tailWord_3746318, baseEnd_3746318] using wordTrace_append hprefix tailTrace_3746318
  have hstable : (prefixWord ++ tailWord_3746318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746318).length < 2 ^ (prefixWord ++ tailWord_3746318).sum := by decide
  have hdescent : baseEnd_3746318 < baseStart_3746318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746355 : List Nat := [1, 1, 1, 2, 4, 2, 3, 1, 3, 3, 2]
def baseStart_3746355 : Nat := 118140960795 + 3746355 * 2 ^ 59
def prefixEnd_3746355 : Nat := 4983230072969 + 3 ^ 40 * 3746355 * 2
def baseEnd_3746355 : Nat := 1923680817374795102533333

theorem tailTrace_3746355 : CollatzResearch.WordTrace tailWord_3746355 prefixEnd_3746355 1923680817374795102533333 := by
  unfold tailWord_3746355
  simp only [CollatzResearch.WordTrace]
  refine ⟨136640792342603136339920519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91093861561735424226613679 136640792342603136339920519)
  ·
    refine ⟨204961188513904704509880779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136640792342603136339920519 204961188513904704509880779)
    ·
      refine ⟨307441782770857056764821169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204961188513904704509880779 307441782770857056764821169)
      ·
        refine ⟨230581337078142792573615877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307441782770857056764821169 230581337078142792573615877)
        ·
          refine ⟨43234000702151773607552977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230581337078142792573615877 43234000702151773607552977)
          ·
            refine ⟨32425500526613830205664733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43234000702151773607552977 32425500526613830205664733)
            ·
              refine ⟨12159562697480186327124275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32425500526613830205664733 12159562697480186327124275)
              ·
                refine ⟨18239344046220279490686413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12159562697480186327124275 18239344046220279490686413)
                ·
                  refine ⟨6839754017332604809007405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18239344046220279490686413 6839754017332604809007405)
                  ·
                    refine ⟨2564907756499726803377777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6839754017332604809007405 2564907756499726803377777)
                    ·
                      refine ⟨1923680817374795102533333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564907756499726803377777 1923680817374795102533333)
                      ·
                        rfl

theorem cell23_3746355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 3, 3, 2].length) (baseStart_3746355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746355 prefixEnd_3746355 := by exact prefixLift 3746355
  have htrace : WordTrace (prefixWord ++ tailWord_3746355) baseStart_3746355 baseEnd_3746355 := by
    simpa [prefixWord, tailWord_3746355, baseEnd_3746355] using wordTrace_append hprefix tailTrace_3746355
  have hstable : (prefixWord ++ tailWord_3746355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746355).length < 2 ^ (prefixWord ++ tailWord_3746355).sum := by decide
  have hdescent : baseEnd_3746355 < baseStart_3746355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746366 : List Nat := [4, 2, 1, 4, 1, 1, 3, 1, 1, 2, 3]
def baseStart_3746366 : Nat := 118140960795 + 3746366 * 2 ^ 59
def prefixEnd_3746366 : Nat := 4983230072969 + 3 ^ 40 * 3746366 * 2
def baseEnd_3746366 : Nat := 1923686465661994559495783

theorem tailTrace_3746366 : CollatzResearch.WordTrace tailWord_3746366 prefixEnd_3746366 1923686465661994559495783 := by
  unfold tailWord_3746366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17080149193195410652321369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91094129030375523479047301 17080149193195410652321369)
  ·
    refine ⟨12810111894896557989241027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17080149193195410652321369 12810111894896557989241027)
    ·
      refine ⟨19215167842344836983861541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12810111894896557989241027 19215167842344836983861541)
      ·
        refine ⟨3602843970439656934474039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19215167842344836983861541 3602843970439656934474039)
        ·
          refine ⟨5404265955659485401711059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602843970439656934474039 5404265955659485401711059)
          ·
            refine ⟨8106398933489228102566589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5404265955659485401711059 8106398933489228102566589)
            ·
              refine ⟨3039899600058460538462471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8106398933489228102566589 3039899600058460538462471)
              ·
                refine ⟨4559849400087690807693707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039899600058460538462471 4559849400087690807693707)
                ·
                  refine ⟨6839774100131536211540561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4559849400087690807693707 6839774100131536211540561)
                  ·
                    refine ⟨5129830575098652158655421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6839774100131536211540561 5129830575098652158655421)
                    ·
                      refine ⟨1923686465661994559495783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129830575098652158655421 1923686465661994559495783)
                      ·
                        rfl

theorem cell23_3746366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_3746366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746366 prefixEnd_3746366 := by exact prefixLift 3746366
  have htrace : WordTrace (prefixWord ++ tailWord_3746366) baseStart_3746366 baseEnd_3746366 := by
    simpa [prefixWord, tailWord_3746366, baseEnd_3746366] using wordTrace_append hprefix tailTrace_3746366
  have hstable : (prefixWord ++ tailWord_3746366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746366).length < 2 ^ (prefixWord ++ tailWord_3746366).sum := by decide
  have hdescent : baseEnd_3746366 < baseStart_3746366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746425 : List Nat := [1, 2, 1, 3, 3, 2, 1, 5, 5]
def baseStart_3746425 : Nat := 118140960795 + 3746425 * 2 ^ 59
def prefixEnd_3746425 : Nat := 4983230072969 + 3 ^ 40 * 3746425 * 2
def baseEnd_3746425 : Nat := 213746306780067758739779

theorem tailTrace_3746425 : CollatzResearch.WordTrace tailWord_3746425 prefixEnd_3746425 213746306780067758739779 := by
  unfold tailWord_3746425
  simp only [CollatzResearch.WordTrace]
  refine ⟨136643345452349538294968729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91095563634899692196645819 136643345452349538294968729)
  ·
    refine ⟨102482509089262153721226547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136643345452349538294968729 102482509089262153721226547)
    ·
      refine ⟨153723763633893230581839821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102482509089262153721226547 153723763633893230581839821)
      ·
        refine ⟨57646411362709961468189933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153723763633893230581839821 57646411362709961468189933)
        ·
          refine ⟨21617404261016235550571225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57646411362709961468189933 21617404261016235550571225)
          ·
            refine ⟨16213053195762176662928419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21617404261016235550571225 16213053195762176662928419)
            ·
              refine ⟨24319579793643264994392629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16213053195762176662928419 24319579793643264994392629)
              ·
                refine ⟨2279960605654056093224309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24319579793643264994392629 2279960605654056093224309)
                ·
                  refine ⟨213746306780067758739779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2279960605654056093224309 213746306780067758739779)
                  ·
                    rfl

theorem cell23_3746425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 5].length) (baseStart_3746425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746425 prefixEnd_3746425 := by exact prefixLift 3746425
  have htrace : WordTrace (prefixWord ++ tailWord_3746425) baseStart_3746425 baseEnd_3746425 := by
    simpa [prefixWord, tailWord_3746425, baseEnd_3746425] using wordTrace_append hprefix tailTrace_3746425
  have hstable : (prefixWord ++ tailWord_3746425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746425).length < 2 ^ (prefixWord ++ tailWord_3746425).sum := by decide
  have hdescent : baseEnd_3746425 < baseStart_3746425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746436 : List Nat := [2, 3, 2, 1, 3, 3, 1, 2, 2, 2, 2]
def baseStart_3746436 : Nat := 118140960795 + 3746436 * 2 ^ 59
def prefixEnd_3746436 : Nat := 4983230072969 + 3 ^ 40 * 3746436 * 2
def baseEnd_3746436 : Nat := 1923722409307809285620461

theorem tailTrace_3746436 : CollatzResearch.WordTrace tailWord_3746436 prefixEnd_3746436 1923722409307809285620461 := by
  unfold tailWord_3746436
  simp only [CollatzResearch.WordTrace]
  refine ⟨68321873327654843586809581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91095831103539791449079441 68321873327654843586809581)
  ·
    refine ⟨25620702497870566345053593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68321873327654843586809581 25620702497870566345053593)
    ·
      refine ⟨19215526873402924758790195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25620702497870566345053593 19215526873402924758790195)
      ·
        refine ⟨28823290310104387138185293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19215526873402924758790195 28823290310104387138185293)
        ·
          refine ⟨10808733866289145176819485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28823290310104387138185293 10808733866289145176819485)
          ·
            refine ⟨4053275199858429441307307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10808733866289145176819485 4053275199858429441307307)
            ·
              refine ⟨6079912799787644161960961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053275199858429441307307 6079912799787644161960961)
              ·
                refine ⟨4559934599840733121470721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079912799787644161960961 4559934599840733121470721)
                ·
                  refine ⟨3419950949880549841103041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4559934599840733121470721 3419950949880549841103041)
                  ·
                    refine ⟨2564963212410412380827281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3419950949880549841103041 2564963212410412380827281)
                    ·
                      refine ⟨1923722409307809285620461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2564963212410412380827281 1923722409307809285620461)
                      ·
                        rfl

theorem cell23_3746436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_3746436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746436 prefixEnd_3746436 := by exact prefixLift 3746436
  have htrace : WordTrace (prefixWord ++ tailWord_3746436) baseStart_3746436 baseEnd_3746436 := by
    simpa [prefixWord, tailWord_3746436, baseEnd_3746436] using wordTrace_append hprefix tailTrace_3746436
  have hstable : (prefixWord ++ tailWord_3746436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746436).length < 2 ^ (prefixWord ++ tailWord_3746436).sum := by decide
  have hdescent : baseEnd_3746436 < baseStart_3746436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746452 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_3746452 : Nat := 118140960795 + 3746452 * 2 ^ 59
def prefixEnd_3746452 : Nat := 4983230072969 + 3 ^ 40 * 3746452 * 2
def baseEnd_3746452 : Nat := 1923730624998281223020387

theorem tailTrace_3746452 : CollatzResearch.WordTrace tailWord_3746452 prefixEnd_3746452 1923730624998281223020387 := by
  unfold tailWord_3746452
  simp only [CollatzResearch.WordTrace]
  refine ⟨68322165111625860953100805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91096220148834481270801073 68322165111625860953100805)
  ·
    refine ⟨12810405958429848928706401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68322165111625860953100805 12810405958429848928706401)
    ·
      refine ⟨9607804468822386696529801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12810405958429848928706401 9607804468822386696529801)
      ·
        refine ⟨7205853351616790022397351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9607804468822386696529801 7205853351616790022397351)
        ·
          refine ⟨10808780027425185033596027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205853351616790022397351 10808780027425185033596027)
          ·
            refine ⟨16213170041137777550394041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10808780027425185033596027 16213170041137777550394041)
            ·
              refine ⟨12159877530853333162795531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16213170041137777550394041 12159877530853333162795531)
              ·
                refine ⟨18239816296279999744193297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12159877530853333162795531 18239816296279999744193297)
                ·
                  refine ⟨13679862222209999808144973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18239816296279999744193297 13679862222209999808144973)
                  ·
                    refine ⟨5129948333328749928054365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13679862222209999808144973 5129948333328749928054365)
                    ·
                      refine ⟨1923730624998281223020387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5129948333328749928054365 1923730624998281223020387)
                      ·
                        rfl

theorem cell23_3746452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_3746452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746452 prefixEnd_3746452 := by exact prefixLift 3746452
  have htrace : WordTrace (prefixWord ++ tailWord_3746452) baseStart_3746452 baseEnd_3746452 := by
    simpa [prefixWord, tailWord_3746452, baseEnd_3746452] using wordTrace_append hprefix tailTrace_3746452
  have hstable : (prefixWord ++ tailWord_3746452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746452).length < 2 ^ (prefixWord ++ tailWord_3746452).sum := by decide
  have hdescent : baseEnd_3746452 < baseStart_3746452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746468 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_3746468 : Nat := 118140960795 + 3746468 * 2 ^ 59
def prefixEnd_3746468 : Nat := 4983230072969 + 3 ^ 40 * 3746468 * 2
def baseEnd_3746468 : Nat := 641246280229584386806771

theorem tailTrace_3746468 : CollatzResearch.WordTrace tailWord_3746468 prefixEnd_3746468 641246280229584386806771 := by
  unfold tailWord_3746468
  simp only [CollatzResearch.WordTrace]
  refine ⟨68322456895596878319392029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91096609194129171092522705 68322456895596878319392029)
  ·
    refine ⟨25620921335848829369772011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68322456895596878319392029 25620921335848829369772011)
    ·
      refine ⟨38431382003773244054658017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25620921335848829369772011 38431382003773244054658017)
      ·
        refine ⟨28823536502829933040993513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38431382003773244054658017 28823536502829933040993513)
        ·
          refine ⟨21617652377122449780745135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28823536502829933040993513 21617652377122449780745135)
          ·
            refine ⟨32426478565683674671117703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21617652377122449780745135 32426478565683674671117703)
            ·
              refine ⟨48639717848525512006676555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32426478565683674671117703 48639717848525512006676555)
              ·
                refine ⟨72959576772788268010014833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48639717848525512006676555 72959576772788268010014833)
                ·
                  refine ⟨54719682579591201007511125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72959576772788268010014833 54719682579591201007511125)
                  ·
                    refine ⟨641246280229584386806771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54719682579591201007511125 641246280229584386806771)
                    ·
                      rfl

theorem cell23_3746468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_3746468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746468 prefixEnd_3746468 := by exact prefixLift 3746468
  have htrace : WordTrace (prefixWord ++ tailWord_3746468) baseStart_3746468 baseEnd_3746468 := by
    simpa [prefixWord, tailWord_3746468, baseEnd_3746468] using wordTrace_append hprefix tailTrace_3746468
  have hstable : (prefixWord ++ tailWord_3746468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746468).length < 2 ^ (prefixWord ++ tailWord_3746468).sum := by decide
  have hdescent : baseEnd_3746468 < baseStart_3746468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746495 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 3]
def baseStart_3746495 : Nat := 118140960795 + 3746495 * 2 ^ 59
def prefixEnd_3746495 : Nat := 4983230072969 + 3 ^ 40 * 3746495 * 2
def baseEnd_3746495 : Nat := 1923752704666424554782689

theorem tailTrace_3746495 : CollatzResearch.WordTrace tailWord_3746495 prefixEnd_3746495 1923752704666424554782689 := by
  unfold tailWord_3746495
  simp only [CollatzResearch.WordTrace]
  refine ⟨136645898562095940250016939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91097265708063960166677959 136645898562095940250016939)
  ·
    refine ⟨204968847843143910375025409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136645898562095940250016939 204968847843143910375025409)
    ·
      refine ⟨153726635882357932781269057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204968847843143910375025409 153726635882357932781269057)
      ·
        refine ⟨115294976911768449585951793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153726635882357932781269057 115294976911768449585951793)
        ·
          refine ⟨86471232683826337189463845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115294976911768449585951793 86471232683826337189463845)
          ·
            refine ⟨16213356128217438223024471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86471232683826337189463845 16213356128217438223024471)
            ·
              refine ⟨24320034192326157334536707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16213356128217438223024471 24320034192326157334536707)
              ·
                refine ⟨36480051288489236001805061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24320034192326157334536707 36480051288489236001805061)
                ·
                  refine ⟨6840009616591731750338449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36480051288489236001805061 6840009616591731750338449)
                  ·
                    refine ⟨5130007212443798812753837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6840009616591731750338449 5130007212443798812753837)
                    ·
                      refine ⟨1923752704666424554782689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5130007212443798812753837 1923752704666424554782689)
                      ·
                        rfl

theorem cell23_3746495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_3746495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746495 prefixEnd_3746495 := by exact prefixLift 3746495
  have htrace : WordTrace (prefixWord ++ tailWord_3746495) baseStart_3746495 baseEnd_3746495 := by
    simpa [prefixWord, tailWord_3746495, baseEnd_3746495] using wordTrace_append hprefix tailTrace_3746495
  have hstable : (prefixWord ++ tailWord_3746495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746495).length < 2 ^ (prefixWord ++ tailWord_3746495).sum := by decide
  have hdescent : baseEnd_3746495 < baseStart_3746495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746552 : List Nat := [2, 1, 2, 1, 1, 2, 3, 4, 2, 3, 2]
def baseStart_3746552 : Nat := 118140960795 + 3746552 * 2 ^ 59
def prefixEnd_3746552 : Nat := 4983230072969 + 3 ^ 40 * 3746552 * 2
def baseEnd_3746552 : Nat := 1923781973063730831769927

theorem tailTrace_3746552 : CollatzResearch.WordTrace tailWord_3746552 prefixEnd_3746552 1923781973063730831769927 := by
  unfold tailWord_3746552
  simp only [CollatzResearch.WordTrace]
  refine ⟨68323988761444719492420955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91098651681926292656561273 68323988761444719492420955)
  ·
    refine ⟨102485983142167079238631433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68323988761444719492420955 102485983142167079238631433)
    ·
      refine ⟨76864487356625309428973575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102485983142167079238631433 76864487356625309428973575)
      ·
        refine ⟨115296731034937964143460363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76864487356625309428973575 115296731034937964143460363)
        ·
          refine ⟨172945096552406946215190545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115296731034937964143460363 172945096552406946215190545)
          ·
            refine ⟨129708822414305209661392909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172945096552406946215190545 129708822414305209661392909)
            ·
              refine ⟨48640808405364453623022341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129708822414305209661392909 48640808405364453623022341)
              ·
                refine ⟨9120151576005835054316689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48640808405364453623022341 9120151576005835054316689)
                ·
                  refine ⟨6840113682004376290737517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9120151576005835054316689 6840113682004376290737517)
                  ·
                    refine ⟨2565042630751641109026569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6840113682004376290737517 2565042630751641109026569)
                    ·
                      refine ⟨1923781973063730831769927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565042630751641109026569 1923781973063730831769927)
                      ·
                        rfl

theorem cell23_3746552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 4, 2, 3, 2].length) (baseStart_3746552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746552 prefixEnd_3746552 := by exact prefixLift 3746552
  have htrace : WordTrace (prefixWord ++ tailWord_3746552) baseStart_3746552 baseEnd_3746552 := by
    simpa [prefixWord, tailWord_3746552, baseEnd_3746552] using wordTrace_append hprefix tailTrace_3746552
  have hstable : (prefixWord ++ tailWord_3746552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746552).length < 2 ^ (prefixWord ++ tailWord_3746552).sum := by decide
  have hdescent : baseEnd_3746552 < baseStart_3746552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746562 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3746562 : Nat := 118140960795 + 3746562 * 2 ^ 59
def prefixEnd_3746562 : Nat := 4983230072969 + 3 ^ 40 * 3746562 * 2
def baseEnd_3746562 : Nat := 641262369290091930881627

theorem tailTrace_3746562 : CollatzResearch.WordTrace tailWord_3746562 prefixEnd_3746562 641262369290091930881627 := by
  unfold tailWord_3746562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34162085563213302673176485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91098894835235473795137293 34162085563213302673176485)
  ·
    refine ⟨6405391043102494251220591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34162085563213302673176485 6405391043102494251220591)
    ·
      refine ⟨9608086564653741376830887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6405391043102494251220591 9608086564653741376830887)
      ·
        refine ⟨14412129846980612065246331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9608086564653741376830887 14412129846980612065246331)
        ·
          refine ⟨21618194770470918097869497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14412129846980612065246331 21618194770470918097869497)
          ·
            refine ⟨16213646077853188573402123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21618194770470918097869497 16213646077853188573402123)
            ·
              refine ⟨24320469116779782860103185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16213646077853188573402123 24320469116779782860103185)
              ·
                refine ⟨18240351837584837145077389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24320469116779782860103185 18240351837584837145077389)
                ·
                  refine ⟨6840131939094313929404021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18240351837584837145077389 6840131939094313929404021)
                  ·
                    refine ⟨641262369290091930881627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6840131939094313929404021 641262369290091930881627)
                    ·
                      rfl

theorem cell23_3746562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3746562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746562 prefixEnd_3746562 := by exact prefixLift 3746562
  have htrace : WordTrace (prefixWord ++ tailWord_3746562) baseStart_3746562 baseEnd_3746562 := by
    simpa [prefixWord, tailWord_3746562, baseEnd_3746562] using wordTrace_append hprefix tailTrace_3746562
  have hstable : (prefixWord ++ tailWord_3746562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746562).length < 2 ^ (prefixWord ++ tailWord_3746562).sum := by decide
  have hdescent : baseEnd_3746562 < baseStart_3746562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746575 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 1, 6]
def baseStart_3746575 : Nat := 118140960795 + 3746575 * 2 ^ 59
def prefixEnd_3746575 : Nat := 4983230072969 + 3 ^ 40 * 3746575 * 2
def baseEnd_3746575 : Nat := 641264594372928080594107

theorem tailTrace_3746575 : CollatzResearch.WordTrace tailWord_3746575 prefixEnd_3746575 641264594372928080594107 := by
  unfold tailWord_3746575
  simp only [CollatzResearch.WordTrace]
  refine ⟨136648816401806113912929179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91099210934537409275286119 136648816401806113912929179)
  ·
    refine ⟨204973224602709170869393769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136648816401806113912929179 204973224602709170869393769)
    ·
      refine ⟨153729918452031878152045327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204973224602709170869393769 153729918452031878152045327)
      ·
        refine ⟨230594877678047817228067991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153729918452031878152045327 230594877678047817228067991)
        ·
          refine ⟨345892316517071725842101987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230594877678047817228067991 345892316517071725842101987)
          ·
            refine ⟨518838474775607588763152981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345892316517071725842101987 518838474775607588763152981)
            ·
              refine ⟨6080138376276651430818199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 518838474775607588763152981 6080138376276651430818199)
              ·
                refine ⟨9120207564414977146227299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6080138376276651430818199 9120207564414977146227299)
                ·
                  refine ⟨13680311346622465719340949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9120207564414977146227299 13680311346622465719340949)
                  ·
                    refine ⟨641264594372928080594107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13680311346622465719340949 641264594372928080594107)
                    ·
                      rfl

theorem cell23_3746575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 6].length) (baseStart_3746575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746575 prefixEnd_3746575 := by exact prefixLift 3746575
  have htrace : WordTrace (prefixWord ++ tailWord_3746575) baseStart_3746575 baseEnd_3746575 := by
    simpa [prefixWord, tailWord_3746575, baseEnd_3746575] using wordTrace_append hprefix tailTrace_3746575
  have hstable : (prefixWord ++ tailWord_3746575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746575).length < 2 ^ (prefixWord ++ tailWord_3746575).sum := by decide
  have hdescent : baseEnd_3746575 < baseStart_3746575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746596 : List Nat := [2, 3, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_3746596 : Nat := 118140960795 + 3746596 * 2 ^ 59
def prefixEnd_3746596 : Nat := 4983230072969 + 3 ^ 40 * 3746596 * 2
def baseEnd_3746596 : Nat := 641268188737509553206575

theorem tailTrace_3746596 : CollatzResearch.WordTrace tailWord_3746596 prefixEnd_3746596 641268188737509553206575 := by
  unfold tailWord_3746596
  simp only [CollatzResearch.WordTrace]
  refine ⟨68324791167365017249721821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91099721556486689666295761 68324791167365017249721821)
  ·
    refine ⟨25621796687761881468645683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68324791167365017249721821 25621796687761881468645683)
    ·
      refine ⟨38432695031642822202968525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25621796687761881468645683 38432695031642822202968525)
      ·
        refine ⟨14412260636866058326113197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38432695031642822202968525 14412260636866058326113197)
        ·
          refine ⟨5404597738824771872292449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14412260636866058326113197 5404597738824771872292449)
          ·
            refine ⟨4053448304118578904219337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5404597738824771872292449 4053448304118578904219337)
            ·
              refine ⟨3040086228088934178164503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053448304118578904219337 3040086228088934178164503)
              ·
                refine ⟨4560129342133401267246755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040086228088934178164503 4560129342133401267246755)
                ·
                  refine ⟨6840194013200101900870133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560129342133401267246755 6840194013200101900870133)
                  ·
                    refine ⟨641268188737509553206575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6840194013200101900870133 641268188737509553206575)
                    ·
                      rfl

theorem cell23_3746596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_3746596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746596 prefixEnd_3746596 := by exact prefixLift 3746596
  have htrace : WordTrace (prefixWord ++ tailWord_3746596) baseStart_3746596 baseEnd_3746596 := by
    simpa [prefixWord, tailWord_3746596, baseEnd_3746596] using wordTrace_append hprefix tailTrace_3746596
  have hstable : (prefixWord ++ tailWord_3746596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746596).length < 2 ^ (prefixWord ++ tailWord_3746596).sum := by decide
  have hdescent : baseEnd_3746596 < baseStart_3746596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746616 : List Nat := [2, 1, 2, 1, 3, 2, 1, 6, 1, 2, 2]
def baseStart_3746616 : Nat := 118140960795 + 3746616 * 2 ^ 59
def prefixEnd_3746616 : Nat := 4983230072969 + 3 ^ 40 * 3746616 * 2
def baseEnd_3746616 : Nat := 1923814835825618581369633

theorem tailTrace_3746616 : CollatzResearch.WordTrace tailWord_3746616 prefixEnd_3746616 1923814835825618581369633 := by
  unfold tailWord_3746616
  simp only [CollatzResearch.WordTrace]
  refine ⟨68325155897328788957585851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91100207863105051943447801 68325155897328788957585851)
  ·
    refine ⟨102487733845993183436378777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68325155897328788957585851 102487733845993183436378777)
    ·
      refine ⟨76865800384494887577284083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102487733845993183436378777 76865800384494887577284083)
      ·
        refine ⟨115298700576742331365926125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76865800384494887577284083 115298700576742331365926125)
        ·
          refine ⟨43237012716278374262222297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115298700576742331365926125 43237012716278374262222297)
          ·
            refine ⟨32427759537208780696666723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43237012716278374262222297 32427759537208780696666723)
            ·
              refine ⟨48641639305813171045000085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32427759537208780696666723 48641639305813171045000085)
              ·
                refine ⟨2280076842459992392734379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48641639305813171045000085 2280076842459992392734379)
                ·
                  refine ⟨3420115263689988589101569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280076842459992392734379 3420115263689988589101569)
                  ·
                    refine ⟨2565086447767491441826177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420115263689988589101569 2565086447767491441826177)
                    ·
                      refine ⟨1923814835825618581369633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565086447767491441826177 1923814835825618581369633)
                      ·
                        rfl

theorem cell23_3746616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 6, 1, 2, 2].length) (baseStart_3746616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746616 prefixEnd_3746616 := by exact prefixLift 3746616
  have htrace : WordTrace (prefixWord ++ tailWord_3746616) baseStart_3746616 baseEnd_3746616 := by
    simpa [prefixWord, tailWord_3746616, baseEnd_3746616] using wordTrace_append hprefix tailTrace_3746616
  have hstable : (prefixWord ++ tailWord_3746616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746616).length < 2 ^ (prefixWord ++ tailWord_3746616).sum := by decide
  have hdescent : baseEnd_3746616 < baseStart_3746616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746645 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3746645 : Nat := 118140960795 + 3746645 * 2 ^ 59
def prefixEnd_3746645 : Nat := 4983230072969 + 3 ^ 40 * 3746645 * 2
def baseEnd_3746645 : Nat := 1923829726764598967906999

theorem tailTrace_3746645 : CollatzResearch.WordTrace tailWord_3746645 prefixEnd_3746645 1923829726764598967906999 := by
  unfold tailWord_3746645
  simp only [CollatzResearch.WordTrace]
  refine ⟨136651369511552515867977389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91100913007701677245318259 136651369511552515867977389)
  ·
    refine ⟨51244263566832193450491521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136651369511552515867977389 51244263566832193450491521)
    ·
      refine ⟨38433197675124145087868641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51244263566832193450491521 38433197675124145087868641)
      ·
        refine ⟨28824898256343108815901481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38433197675124145087868641 28824898256343108815901481)
        ·
          refine ⟨21618673692257331611926111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28824898256343108815901481 21618673692257331611926111)
          ·
            refine ⟨32428010538385997417889167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21618673692257331611926111 32428010538385997417889167)
            ·
              refine ⟨48642015807578996126833751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32428010538385997417889167 48642015807578996126833751)
              ·
                refine ⟨72963023711368494190250627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48642015807578996126833751 72963023711368494190250627)
                ·
                  refine ⟨109444535567052741285375941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72963023711368494190250627 109444535567052741285375941)
                  ·
                    refine ⟨20520850418822388991007989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 109444535567052741285375941 20520850418822388991007989)
                    ·
                      refine ⟨1923829726764598967906999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20520850418822388991007989 1923829726764598967906999)
                      ·
                        rfl

theorem cell23_3746645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3746645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746645 prefixEnd_3746645 := by exact prefixLift 3746645
  have htrace : WordTrace (prefixWord ++ tailWord_3746645) baseStart_3746645 baseEnd_3746645 := by
    simpa [prefixWord, tailWord_3746645, baseEnd_3746645] using wordTrace_append hprefix tailTrace_3746645
  have hstable : (prefixWord ++ tailWord_3746645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746645).length < 2 ^ (prefixWord ++ tailWord_3746645).sum := by decide
  have hdescent : baseEnd_3746645 < baseStart_3746645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746725 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_3746725 : Nat := 118140960795 + 3746725 * 2 ^ 59
def prefixEnd_3746725 : Nat := 4983230072969 + 3 ^ 40 * 3746725 * 2
def baseEnd_3746725 : Nat := 641290268405652884968877

theorem tailTrace_3746725 : CollatzResearch.WordTrace tailWord_3746725 prefixEnd_3746725 641290268405652884968877 := by
  unfold tailWord_3746725
  simp only [CollatzResearch.WordTrace]
  refine ⟨136654287351262689530889629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91102858234175126353926419 136654287351262689530889629)
  ·
    refine ⟨51245357756723508574083611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136654287351262689530889629 51245357756723508574083611)
    ·
      refine ⟨76868036635085262861125417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51245357756723508574083611 76868036635085262861125417)
      ·
        refine ⟨57651027476313947145844063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76868036635085262861125417 57651027476313947145844063)
        ·
          refine ⟨86476541214470920718766095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57651027476313947145844063 86476541214470920718766095)
          ·
            refine ⟨129714811821706381078149143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86476541214470920718766095 129714811821706381078149143)
            ·
              refine ⟨194572217732559571617223715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129714811821706381078149143 194572217732559571617223715)
              ·
                refine ⟨291858326598839357425835573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194572217732559571617223715 291858326598839357425835573)
                ·
                  refine ⟨27361718118641189758672085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 291858326598839357425835573 27361718118641189758672085)
                  ·
                    refine ⟨641290268405652884968877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27361718118641189758672085 641290268405652884968877)
                    ·
                      rfl

theorem cell23_3746725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_3746725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746725 prefixEnd_3746725 := by exact prefixLift 3746725
  have htrace : WordTrace (prefixWord ++ tailWord_3746725) baseStart_3746725 baseEnd_3746725 := by
    simpa [prefixWord, tailWord_3746725, baseEnd_3746725] using wordTrace_append hprefix tailTrace_3746725
  have hstable : (prefixWord ++ tailWord_3746725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746725).length < 2 ^ (prefixWord ++ tailWord_3746725).sum := by decide
  have hdescent : baseEnd_3746725 < baseStart_3746725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746735 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 7]
def baseStart_3746735 : Nat := 118140960795 + 3746735 * 2 ^ 59
def prefixEnd_3746735 : Nat := 4983230072969 + 3 ^ 40 * 3746735 * 2
def baseEnd_3746735 : Nat := 1923875940023503615781585

theorem tailTrace_3746735 : CollatzResearch.WordTrace tailWord_3746735 prefixEnd_3746735 1923875940023503615781585 := by
  unfold tailWord_3746735
  simp only [CollatzResearch.WordTrace]
  refine ⟨136654652081226461238753659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91103101387484307492502439 136654652081226461238753659)
  ·
    refine ⟨204981978121839691858130489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136654652081226461238753659 204981978121839691858130489)
    ·
      refine ⟨153736483591379768893597867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 204981978121839691858130489 153736483591379768893597867)
      ·
        refine ⟨230604725387069653340396801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153736483591379768893597867 230604725387069653340396801)
        ·
          refine ⟨172953544040302240005297601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230604725387069653340396801 172953544040302240005297601)
          ·
            refine ⟨129715158030226680003973201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172953544040302240005297601 129715158030226680003973201)
            ·
              refine ⟨97286368522670010002979901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129715158030226680003973201 97286368522670010002979901)
              ·
                refine ⟨36482388196001253751117463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97286368522670010002979901 36482388196001253751117463)
                ·
                  refine ⟨54723582294001880626676195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36482388196001253751117463 54723582294001880626676195)
                  ·
                    refine ⟨82085373441002820940014293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54723582294001880626676195 82085373441002820940014293)
                    ·
                      refine ⟨1923875940023503615781585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 82085373441002820940014293 1923875940023503615781585)
                      ·
                        rfl

theorem cell23_3746735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_3746735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746735 prefixEnd_3746735 := by exact prefixLift 3746735
  have htrace : WordTrace (prefixWord ++ tailWord_3746735) baseStart_3746735 baseEnd_3746735 := by
    simpa [prefixWord, tailWord_3746735, baseEnd_3746735] using wordTrace_append hprefix tailTrace_3746735
  have hstable : (prefixWord ++ tailWord_3746735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746735).length < 2 ^ (prefixWord ++ tailWord_3746735).sum := by decide
  have hdescent : baseEnd_3746735 < baseStart_3746735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746740 : List Nat := [2, 5, 2, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3746740 : Nat := 118140960795 + 3746740 * 2 ^ 59
def prefixEnd_3746740 : Nat := 4983230072969 + 3 ^ 40 * 3746740 * 2
def baseEnd_3746740 : Nat := 1923878507426776096219063

theorem tailTrace_3746740 : CollatzResearch.WordTrace tailWord_3746740 prefixEnd_3746740 1923878507426776096219063 := by
  unfold tailWord_3746740
  simp only [CollatzResearch.WordTrace]
  refine ⟨68327417223104173546342837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91103222964138898061790449 68327417223104173546342837)
  ·
    refine ⟨6405695364666016269969641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68327417223104173546342837 6405695364666016269969641)
    ·
      refine ⟨4804271523499512202477231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6405695364666016269969641 4804271523499512202477231)
      ·
        refine ⟨7206407285249268303715847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804271523499512202477231 7206407285249268303715847)
        ·
          refine ⟨10809610927873902455573771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206407285249268303715847 10809610927873902455573771)
          ·
            refine ⟨16214416391810853683360657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809610927873902455573771 16214416391810853683360657)
            ·
              refine ⟨12160812293858140262520493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16214416391810853683360657 12160812293858140262520493)
              ·
                refine ⟨4560304610196802598445185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12160812293858140262520493 4560304610196802598445185)
                ·
                  refine ⟨3420228457647601948833889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560304610196802598445185 3420228457647601948833889)
                  ·
                    refine ⟨2565171343235701461625417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420228457647601948833889 2565171343235701461625417)
                    ·
                      refine ⟨1923878507426776096219063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565171343235701461625417 1923878507426776096219063)
                      ·
                        rfl

theorem cell23_3746740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3746740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746740 prefixEnd_3746740 := by exact prefixLift 3746740
  have htrace : WordTrace (prefixWord ++ tailWord_3746740) baseStart_3746740 baseEnd_3746740 := by
    simpa [prefixWord, tailWord_3746740, baseEnd_3746740] using wordTrace_append hprefix tailTrace_3746740
  have hstable : (prefixWord ++ tailWord_3746740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746740).length < 2 ^ (prefixWord ++ tailWord_3746740).sum := by decide
  have hdescent : baseEnd_3746740 < baseStart_3746740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746755 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 2, 8]
def baseStart_3746755 : Nat := 118140960795 + 3746755 * 2 ^ 59
def prefixEnd_3746755 : Nat := 4983230072969 + 3 ^ 40 * 3746755 * 2
def baseEnd_3746755 : Nat := 641295403212197845843831

theorem tailTrace_3746755 : CollatzResearch.WordTrace tailWord_3746755 prefixEnd_3746755 641295403212197845843831 := by
  unfold tailWord_3746755
  simp only [CollatzResearch.WordTrace]
  refine ⟨136655381541154004654481719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91103587694102669769654479 136655381541154004654481719)
  ·
    refine ⟨204983072311731006981722579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136655381541154004654481719 204983072311731006981722579)
    ·
      refine ⟨307474608467596510472583869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204983072311731006981722579 307474608467596510472583869)
      ·
        refine ⟨115302978175348691427218951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307474608467596510472583869 115302978175348691427218951)
        ·
          refine ⟨172954467263023037140828427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115302978175348691427218951 172954467263023037140828427)
          ·
            refine ⟨259431700894534555711242641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172954467263023037140828427 259431700894534555711242641)
            ·
              refine ⟨194573775670900916783431981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259431700894534555711242641 194573775670900916783431981)
              ·
                refine ⟨72965165876587843793786993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194573775670900916783431981 72965165876587843793786993)
                ·
                  refine ⟨54723874407440882845340245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72965165876587843793786993 54723874407440882845340245)
                  ·
                    refine ⟨641295403212197845843831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54723874407440882845340245 641295403212197845843831)
                    ·
                      rfl

theorem cell23_3746755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 8].length) (baseStart_3746755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746755 prefixEnd_3746755 := by exact prefixLift 3746755
  have htrace : WordTrace (prefixWord ++ tailWord_3746755) baseStart_3746755 baseEnd_3746755 := by
    simpa [prefixWord, tailWord_3746755, baseEnd_3746755] using wordTrace_append hprefix tailTrace_3746755
  have hstable : (prefixWord ++ tailWord_3746755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746755).length < 2 ^ (prefixWord ++ tailWord_3746755).sum := by decide
  have hdescent : baseEnd_3746755 < baseStart_3746755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746806 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 3, 4]
def baseStart_3746806 : Nat := 118140960795 + 3746806 * 2 ^ 59
def prefixEnd_3746806 : Nat := 4983230072969 + 3 ^ 40 * 3746806 * 2
def baseEnd_3746806 : Nat := 641304132383324279331253

theorem tailTrace_3746806 : CollatzResearch.WordTrace tailWord_3746806 prefixEnd_3746806 641304132383324279331253 := by
  unfold tailWord_3746806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8541077603998077522786767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91104827775979493576392181 8541077603998077522786767)
  ·
    refine ⟨12811616405997116284180151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8541077603998077522786767 12811616405997116284180151)
    ·
      refine ⟨19217424608995674426270227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12811616405997116284180151 19217424608995674426270227)
      ·
        refine ⟨28826136913493511639405341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19217424608995674426270227 28826136913493511639405341)
        ·
          refine ⟨10809801342560066864777003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28826136913493511639405341 10809801342560066864777003)
          ·
            refine ⟨16214702013840100297165505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10809801342560066864777003 16214702013840100297165505)
            ·
              refine ⟨12161026510380075222874129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16214702013840100297165505 12161026510380075222874129)
              ·
                refine ⟨9120769882785056417155597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12161026510380075222874129 9120769882785056417155597)
                ·
                  refine ⟨3420288706044396156433349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9120769882785056417155597 3420288706044396156433349)
                  ·
                    refine ⟨641304132383324279331253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3420288706044396156433349 641304132383324279331253)
                    ·
                      rfl

theorem cell23_3746806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_3746806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746806 prefixEnd_3746806 := by exact prefixLift 3746806
  have htrace : WordTrace (prefixWord ++ tailWord_3746806) baseStart_3746806 baseEnd_3746806 := by
    simpa [prefixWord, tailWord_3746806, baseEnd_3746806] using wordTrace_append hprefix tailTrace_3746806
  have hstable : (prefixWord ++ tailWord_3746806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746806).length < 2 ^ (prefixWord ++ tailWord_3746806).sum := by decide
  have hdescent : baseEnd_3746806 < baseStart_3746806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746873 : List Nat := [1, 2, 1, 5, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3746873 : Nat := 118140960795 + 3746873 * 2 ^ 59
def prefixEnd_3746873 : Nat := 4983230072969 + 3 ^ 40 * 3746873 * 2
def baseEnd_3746873 : Nat := 1923946800353824075855951

theorem tailTrace_3746873 : CollatzResearch.WordTrace tailWord_3746873 prefixEnd_3746873 1923946800353824075855951 := by
  unfold tailWord_3746873
  simp only [CollatzResearch.WordTrace]
  refine ⟨136659685354726510807277273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91106456903151007204851515 136659685354726510807277273)
  ·
    refine ⟨102494764016044883105457955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136659685354726510807277273 102494764016044883105457955)
    ·
      refine ⟨153742146024067324658186933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102494764016044883105457955 153742146024067324658186933)
      ·
        refine ⟨14413326189756311686705025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153742146024067324658186933 14413326189756311686705025)
        ·
          refine ⟨10809994642317233765028769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14413326189756311686705025 10809994642317233765028769)
          ·
            refine ⟨8107495981737925323771577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10809994642317233765028769 8107495981737925323771577)
            ·
              refine ⟨6080621986303443992828683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107495981737925323771577 6080621986303443992828683)
              ·
                refine ⟨9120932979455165989243025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6080621986303443992828683 9120932979455165989243025)
                ·
                  refine ⟨6840699734591374491932269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9120932979455165989243025 6840699734591374491932269)
                  ·
                    refine ⟨2565262400471765434474601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6840699734591374491932269 2565262400471765434474601)
                    ·
                      refine ⟨1923946800353824075855951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565262400471765434474601 1923946800353824075855951)
                      ·
                        rfl

theorem cell23_3746873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3746873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746873 prefixEnd_3746873 := by exact prefixLift 3746873
  have htrace : WordTrace (prefixWord ++ tailWord_3746873) baseStart_3746873 baseEnd_3746873 := by
    simpa [prefixWord, tailWord_3746873, baseEnd_3746873] using wordTrace_append hprefix tailTrace_3746873
  have hstable : (prefixWord ++ tailWord_3746873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746873).length < 2 ^ (prefixWord ++ tailWord_3746873).sum := by decide
  have hdescent : baseEnd_3746873 < baseStart_3746873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746926 : List Nat := [4, 1, 2, 2, 1, 3, 3, 7]
def baseStart_3746926 : Nat := 118140960795 + 3746926 * 2 ^ 59
def prefixEnd_3746926 : Nat := 4983230072969 + 3 ^ 40 * 3746926 * 2
def baseEnd_3746926 : Nat := 71258296845500458092341

theorem tailTrace_3746926 : CollatzResearch.WordTrace tailWord_3746926 prefixEnd_3746926 71258296845500458092341 := by
  unfold tailWord_3746926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17082702302941812607369579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91107745615689667239304421 17082702302941812607369579)
  ·
    refine ⟨25624053454412718911054369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17082702302941812607369579 25624053454412718911054369)
    ·
      refine ⟨19218040090809539183290777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25624053454412718911054369 19218040090809539183290777)
      ·
        refine ⟨14413530068107154387468083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19218040090809539183290777 14413530068107154387468083)
        ·
          refine ⟨21620295102160731581202125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14413530068107154387468083 21620295102160731581202125)
          ·
            refine ⟨8107610663310274342950797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21620295102160731581202125 8107610663310274342950797)
            ·
              refine ⟨3040353998741352878606549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8107610663310274342950797 3040353998741352878606549)
              ·
                refine ⟨71258296845500458092341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3040353998741352878606549 71258296845500458092341)
                ·
                  rfl

theorem cell23_3746926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 7].length) (baseStart_3746926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746926 prefixEnd_3746926 := by exact prefixLift 3746926
  have htrace : WordTrace (prefixWord ++ tailWord_3746926) baseStart_3746926 baseEnd_3746926 := by
    simpa [prefixWord, tailWord_3746926, baseEnd_3746926] using wordTrace_append hprefix tailTrace_3746926
  have hstable : (prefixWord ++ tailWord_3746926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746926).length < 2 ^ (prefixWord ++ tailWord_3746926).sum := by decide
  have hdescent : baseEnd_3746926 < baseStart_3746926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746937 : List Nat := [1, 2, 1, 3, 5, 1, 2, 3, 1, 2, 2]
def baseStart_3746937 : Nat := 118140960795 + 3746937 * 2 ^ 59
def prefixEnd_3746937 : Nat := 4983230072969 + 3 ^ 40 * 3746937 * 2
def baseEnd_3746937 : Nat := 1923979663115711825455657

theorem tailTrace_3746937 : CollatzResearch.WordTrace tailWord_3746937 prefixEnd_3746937 1923979663115711825455657 := by
  unfold tailWord_3746937
  simp only [CollatzResearch.WordTrace]
  refine ⟨136662019626494649737607065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91108013084329766491738043 136662019626494649737607065)
  ·
    refine ⟨102496514719870987303205299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136662019626494649737607065 102496514719870987303205299)
    ·
      refine ⟨153744772079806480954807949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102496514719870987303205299 153744772079806480954807949)
      ·
        refine ⟨57654289529927430358052981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153744772079806480954807949 57654289529927430358052981)
        ·
          refine ⟨5405089643430696596067467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57654289529927430358052981 5405089643430696596067467)
          ·
            refine ⟨8107634465146044894101201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405089643430696596067467 8107634465146044894101201)
            ·
              refine ⟨6080725848859533670575901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107634465146044894101201 6080725848859533670575901)
              ·
                refine ⟨2280272193322325126465963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6080725848859533670575901 2280272193322325126465963)
                ·
                  refine ⟨3420408289983487689698945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280272193322325126465963 3420408289983487689698945)
                  ·
                    refine ⟨2565306217487615767274209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420408289983487689698945 2565306217487615767274209)
                    ·
                      refine ⟨1923979663115711825455657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565306217487615767274209 1923979663115711825455657)
                      ·
                        rfl

theorem cell23_3746937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_3746937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746937 prefixEnd_3746937 := by exact prefixLift 3746937
  have htrace : WordTrace (prefixWord ++ tailWord_3746937) baseStart_3746937 baseEnd_3746937 := by
    simpa [prefixWord, tailWord_3746937, baseEnd_3746937] using wordTrace_append hprefix tailTrace_3746937
  have hstable : (prefixWord ++ tailWord_3746937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746937).length < 2 ^ (prefixWord ++ tailWord_3746937).sum := by decide
  have hdescent : baseEnd_3746937 < baseStart_3746937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746953 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 3]
def baseStart_3746953 : Nat := 118140960795 + 3746953 * 2 ^ 59
def prefixEnd_3746953 : Nat := 4983230072969 + 3 ^ 40 * 3746953 * 2
def baseEnd_3746953 : Nat := 1923987878806183762855583

theorem tailTrace_3746953 : CollatzResearch.WordTrace tailWord_3746953 prefixEnd_3746953 1923987878806183762855583 := by
  unfold tailWord_3746953
  simp only [CollatzResearch.WordTrace]
  refine ⟨136662603194436684470189513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91108402129624456313459675 136662603194436684470189513)
  ·
    refine ⟨102496952395827513352642135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136662603194436684470189513 102496952395827513352642135)
    ·
      refine ⟨153745428593741270028963203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102496952395827513352642135 153745428593741270028963203)
      ·
        refine ⟨230618142890611905043444805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153745428593741270028963203 230618142890611905043444805)
        ·
          refine ⟨43240901791989732195645901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 230618142890611905043444805 43240901791989732195645901)
          ·
            refine ⟨16215338171996149573367213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43240901791989732195645901 16215338171996149573367213)
            ·
              refine ⟨6080751814498556090012705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16215338171996149573367213 6080751814498556090012705)
              ·
                refine ⟨4560563860873917067509529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080751814498556090012705 4560563860873917067509529)
                ·
                  refine ⟨3420422895655437800632147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560563860873917067509529 3420422895655437800632147)
                  ·
                    refine ⟨5130634343483156700948221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3420422895655437800632147 5130634343483156700948221)
                    ·
                      refine ⟨1923987878806183762855583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5130634343483156700948221 1923987878806183762855583)
                      ·
                        rfl

theorem cell23_3746953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 2, 1, 3].length) (baseStart_3746953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746953 prefixEnd_3746953 := by exact prefixLift 3746953
  have htrace : WordTrace (prefixWord ++ tailWord_3746953) baseStart_3746953 baseEnd_3746953 := by
    simpa [prefixWord, tailWord_3746953, baseEnd_3746953] using wordTrace_append hprefix tailTrace_3746953
  have hstable : (prefixWord ++ tailWord_3746953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746953).length < 2 ^ (prefixWord ++ tailWord_3746953).sum := by decide
  have hdescent : baseEnd_3746953 < baseStart_3746953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746979 : List Nat := [1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 3]
def baseStart_3746979 : Nat := 118140960795 + 3746979 * 2 ^ 59
def prefixEnd_3746979 : Nat := 4983230072969 + 3 ^ 40 * 3746979 * 2
def baseEnd_3746979 : Nat := 1924001229303200661130463

theorem tailTrace_3746979 : CollatzResearch.WordTrace tailWord_3746979 prefixEnd_3746979 1924001229303200661130463 := by
  unfold tailWord_3746979
  simp only [CollatzResearch.WordTrace]
  refine ⟨136663551492342490910635991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91109034328228327273757327 136663551492342490910635991)
  ·
    refine ⟨204995327238513736365953987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136663551492342490910635991 204995327238513736365953987)
    ·
      refine ⟨307492990857770604548930981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 204995327238513736365953987 307492990857770604548930981)
      ·
        refine ⟨57654935785831988352924559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307492990857770604548930981 57654935785831988352924559)
        ·
          refine ⟨86482403678747982529386839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57654935785831988352924559 86482403678747982529386839)
          ·
            refine ⟨129723605518121973794080259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86482403678747982529386839 129723605518121973794080259)
            ·
              refine ⟨194585408277182960691120389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129723605518121973794080259 194585408277182960691120389)
              ·
                refine ⟨36484764051971805129585073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194585408277182960691120389 36484764051971805129585073)
                ·
                  refine ⟨27363573038978853847188805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36484764051971805129585073 27363573038978853847188805)
                  ·
                    refine ⟨5130669944808535096347901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27363573038978853847188805 5130669944808535096347901)
                    ·
                      refine ⟨1924001229303200661130463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5130669944808535096347901 1924001229303200661130463)
                      ·
                        rfl

theorem cell23_3746979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_3746979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746979 prefixEnd_3746979 := by exact prefixLift 3746979
  have htrace : WordTrace (prefixWord ++ tailWord_3746979) baseStart_3746979 baseEnd_3746979 := by
    simpa [prefixWord, tailWord_3746979, baseEnd_3746979] using wordTrace_append hprefix tailTrace_3746979
  have hstable : (prefixWord ++ tailWord_3746979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746979).length < 2 ^ (prefixWord ++ tailWord_3746979).sum := by decide
  have hdescent : baseEnd_3746979 < baseStart_3746979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3746980 : List Nat := [2, 3, 1, 2, 3, 2, 2, 2, 1, 3, 2]
def baseStart_3746980 : Nat := 118140960795 + 3746980 * 2 ^ 59
def prefixEnd_3746980 : Nat := 4983230072969 + 3 ^ 40 * 3746980 * 2
def baseEnd_3746980 : Nat := 1924001742783855157217959

theorem tailTrace_3746980 : CollatzResearch.WordTrace tailWord_3746980 prefixEnd_3746980 1924001742783855157217959 := by
  unfold tailWord_3746980
  simp only [CollatzResearch.WordTrace]
  refine ⟨68331793982669434040711197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91109058643559245387614929 68331793982669434040711197)
  ·
    refine ⟨25624422743501037765266699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68331793982669434040711197 25624422743501037765266699)
    ·
      refine ⟨38436634115251556647900049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25624422743501037765266699 38436634115251556647900049)
      ·
        refine ⟨28827475586438667485925037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38436634115251556647900049 28827475586438667485925037)
        ·
          refine ⟨10810303344914500307221889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28827475586438667485925037 10810303344914500307221889)
          ·
            refine ⟨8107727508685875230416417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10810303344914500307221889 8107727508685875230416417)
            ·
              refine ⟨6080795631514406422812313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107727508685875230416417 6080795631514406422812313)
              ·
                refine ⟨4560596723635804817109235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080795631514406422812313 4560596723635804817109235)
                ·
                  refine ⟨6840895085453707225663853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560596723635804817109235 6840895085453707225663853)
                  ·
                    refine ⟨2565335657045140209623945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6840895085453707225663853 2565335657045140209623945)
                    ·
                      refine ⟨1924001742783855157217959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565335657045140209623945 1924001742783855157217959)
                      ·
                        rfl

theorem cell23_3746980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_3746980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3746980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3746980 prefixEnd_3746980 := by exact prefixLift 3746980
  have htrace : WordTrace (prefixWord ++ tailWord_3746980) baseStart_3746980 baseEnd_3746980 := by
    simpa [prefixWord, tailWord_3746980, baseEnd_3746980] using wordTrace_append hprefix tailTrace_3746980
  have hstable : (prefixWord ++ tailWord_3746980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3746980).length < 2 ^ (prefixWord ++ tailWord_3746980).sum := by decide
  have hdescent : baseEnd_3746980 < baseStart_3746980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3746980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747016 : List Nat := [2, 1, 3, 1, 2, 1, 2, 6, 5]
def baseStart_3747016 : Nat := 118140960795 + 3747016 * 2 ^ 59
def prefixEnd_3747016 : Nat := 4983230072969 + 3 ^ 40 * 3747016 * 2
def baseEnd_3747016 : Nat := 213780025343046335151977

theorem tailTrace_3747016 : CollatzResearch.WordTrace tailWord_3747016 prefixEnd_3747016 213780025343046335151977 := by
  unfold tailWord_3747016
  simp only [CollatzResearch.WordTrace]
  refine ⟨68332450496604223114866451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91109933995472297486488601 68332450496604223114866451)
  ·
    refine ⟨102498675744906334672299677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68332450496604223114866451 102498675744906334672299677)
    ·
      refine ⟨38437003404339875502112379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102498675744906334672299677 38437003404339875502112379)
      ·
        refine ⟨57655505106509813253168569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38437003404339875502112379 57655505106509813253168569)
        ·
          refine ⟨43241628829882359939876427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57655505106509813253168569 43241628829882359939876427)
          ·
            refine ⟨64862443244823539909814641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43241628829882359939876427 64862443244823539909814641)
            ·
              refine ⟨48646832433617654932360981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64862443244823539909814641 48646832433617654932360981)
              ·
                refine ⟨2280320270325827574954421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48646832433617654932360981 2280320270325827574954421)
                ·
                  refine ⟨213780025343046335151977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2280320270325827574954421 213780025343046335151977)
                  ·
                    rfl

theorem cell23_3747016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 5].length) (baseStart_3747016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747016 prefixEnd_3747016 := by exact prefixLift 3747016
  have htrace : WordTrace (prefixWord ++ tailWord_3747016) baseStart_3747016 baseEnd_3747016 := by
    simpa [prefixWord, tailWord_3747016, baseEnd_3747016] using wordTrace_append hprefix tailTrace_3747016
  have hstable : (prefixWord ++ tailWord_3747016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747016).length < 2 ^ (prefixWord ++ tailWord_3747016).sum := by decide
  have hdescent : baseEnd_3747016 < baseStart_3747016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747021 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3747021 : Nat := 118140960795 + 3747021 * 2 ^ 59
def prefixEnd_3747021 : Nat := 4983230072969 + 3 ^ 40 * 3747021 * 2
def baseEnd_3747021 : Nat := 1924022795490689496805271

theorem tailTrace_3747021 : CollatzResearch.WordTrace tailWord_3747021 prefixEnd_3747021 1924022795490689496805271 := by
  unfold tailWord_3747021
  simp only [CollatzResearch.WordTrace]
  refine ⟨136665083358190332083664917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91110055572126888055776611 136665083358190332083664917)
  ·
    refine ⟨6406175782415171816421793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 136665083358190332083664917 6406175782415171816421793)
    ·
      refine ⟨4804631836811378862316345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6406175782415171816421793 4804631836811378862316345)
      ·
        refine ⟨3603473877608534146737259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4804631836811378862316345 3603473877608534146737259)
        ·
          refine ⟨5405210816412801220105889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603473877608534146737259 5405210816412801220105889)
          ·
            refine ⟨4053908112309600915079417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5405210816412801220105889 4053908112309600915079417)
            ·
              refine ⟨3040431084232200686309563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053908112309600915079417 3040431084232200686309563)
              ·
                refine ⟨4560646626348301029464345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040431084232200686309563 4560646626348301029464345)
                ·
                  refine ⟨3420484969761225772098259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560646626348301029464345 3420484969761225772098259)
                  ·
                    refine ⟨5130727454641838658147389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3420484969761225772098259 5130727454641838658147389)
                    ·
                      refine ⟨1924022795490689496805271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5130727454641838658147389 1924022795490689496805271)
                      ·
                        rfl

theorem cell23_3747021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3747021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747021 prefixEnd_3747021 := by exact prefixLift 3747021
  have htrace : WordTrace (prefixWord ++ tailWord_3747021) baseStart_3747021 baseEnd_3747021 := by
    simpa [prefixWord, tailWord_3747021, baseEnd_3747021] using wordTrace_append hprefix tailTrace_3747021
  have hstable : (prefixWord ++ tailWord_3747021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747021).length < 2 ^ (prefixWord ++ tailWord_3747021).sum := by decide
  have hdescent : baseEnd_3747021 < baseStart_3747021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747026 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3747026 : Nat := 118140960795 + 3747026 * 2 ^ 59
def prefixEnd_3747026 : Nat := 4983230072969 + 3 ^ 40 * 3747026 * 2
def baseEnd_3747026 : Nat := 1924025362893961977242747

theorem tailTrace_3747026 : CollatzResearch.WordTrace tailWord_3747026 prefixEnd_3747026 1924025362893961977242747 := by
  unfold tailWord_3747026
  simp only [CollatzResearch.WordTrace]
  refine ⟨34166316430793054484399233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91110177148781478625064621 34166316430793054484399233)
  ·
    refine ⟨25624737323094790863299425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34166316430793054484399233 25624737323094790863299425)
    ·
      refine ⟨19218552992321093147474569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25624737323094790863299425 19218552992321093147474569)
      ·
        refine ⟨14413914744240819860605927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19218552992321093147474569 14413914744240819860605927)
        ·
          refine ⟨21620872116361229790908891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14413914744240819860605927 21620872116361229790908891)
          ·
            refine ⟨32431308174541844686363337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21620872116361229790908891 32431308174541844686363337)
            ·
              refine ⟨24323481130906383514772503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32431308174541844686363337 24323481130906383514772503)
              ·
                refine ⟨36485221696359575272158755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24323481130906383514772503 36485221696359575272158755)
                ·
                  refine ⟨54727832544539362908238133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36485221696359575272158755 54727832544539362908238133)
                  ·
                    refine ⟨5130734301050565272647325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54727832544539362908238133 5130734301050565272647325)
                    ·
                      refine ⟨1924025362893961977242747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5130734301050565272647325 1924025362893961977242747)
                      ·
                        rfl

theorem cell23_3747026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3747026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747026 prefixEnd_3747026 := by exact prefixLift 3747026
  have htrace : WordTrace (prefixWord ++ tailWord_3747026) baseStart_3747026 baseEnd_3747026 := by
    simpa [prefixWord, tailWord_3747026, baseEnd_3747026] using wordTrace_append hprefix tailTrace_3747026
  have hstable : (prefixWord ++ tailWord_3747026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747026).length < 2 ^ (prefixWord ++ tailWord_3747026).sum := by decide
  have hdescent : baseEnd_3747026 < baseStart_3747026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747066 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_3747066 : Nat := 118140960795 + 3747066 * 2 ^ 59
def prefixEnd_3747066 : Nat := 4983230072969 + 3 ^ 40 * 3747066 * 2
def baseEnd_3747066 : Nat := 1924045902120141820742563

theorem tailTrace_3747066 : CollatzResearch.WordTrace tailWord_3747066 prefixEnd_3747066 1924045902120141820742563 := by
  unfold tailWord_3747066
  simp only [CollatzResearch.WordTrace]
  refine ⟨34166681160756826192263263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91111149762018203179368701 34166681160756826192263263)
  ·
    refine ⟨51250021741135239288394895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34166681160756826192263263 51250021741135239288394895)
    ·
      refine ⟨76875032611702858932592343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51250021741135239288394895 76875032611702858932592343)
      ·
        refine ⟨115312548917554288398888515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76875032611702858932592343 115312548917554288398888515)
        ·
          refine ⟨172968823376331432598332773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115312548917554288398888515 172968823376331432598332773)
          ·
            refine ⟨32431654383062143612187395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172968823376331432598332773 32431654383062143612187395)
            ·
              refine ⟨48647481574593215418281093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32431654383062143612187395 48647481574593215418281093)
              ·
                refine ⟨9121402795236227890927705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48647481574593215418281093 9121402795236227890927705)
                ·
                  refine ⟨6841052096427170918195779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9121402795236227890927705 6841052096427170918195779)
                  ·
                    refine ⟨10261578144640756377293669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6841052096427170918195779 10261578144640756377293669)
                    ·
                      refine ⟨1924045902120141820742563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10261578144640756377293669 1924045902120141820742563)
                      ·
                        rfl

theorem cell23_3747066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_3747066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747066 prefixEnd_3747066 := by exact prefixLift 3747066
  have htrace : WordTrace (prefixWord ++ tailWord_3747066) baseStart_3747066 baseEnd_3747066 := by
    simpa [prefixWord, tailWord_3747066, baseEnd_3747066] using wordTrace_append hprefix tailTrace_3747066
  have hstable : (prefixWord ++ tailWord_3747066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747066).length < 2 ^ (prefixWord ++ tailWord_3747066).sum := by decide
  have hdescent : baseEnd_3747066 < baseStart_3747066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747083 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 2, 4, 2]
def baseStart_3747083 : Nat := 118140960795 + 3747083 * 2 ^ 59
def prefixEnd_3747083 : Nat := 4983230072969 + 3 ^ 40 * 3747083 * 2
def baseEnd_3747083 : Nat := 1924054631291268254229985

theorem tailTrace_3747083 : CollatzResearch.WordTrace tailWord_3747083 prefixEnd_3747083 1924054631291268254229985 := by
  unfold tailWord_3747083
  simp only [CollatzResearch.WordTrace]
  refine ⟨136667344683965716672421903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91111563122643811114947935 136667344683965716672421903)
  ·
    refine ⟨205001017025948575008632855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136667344683965716672421903 205001017025948575008632855)
    ·
      refine ⟨307501525538922862512949283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205001017025948575008632855 307501525538922862512949283)
      ·
        refine ⟨461252288308384293769423925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307501525538922862512949283 461252288308384293769423925)
        ·
          refine ⟨43242402028911027540883493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 461252288308384293769423925 43242402028911027540883493)
          ·
            refine ⟨8107950380420817663915655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43242402028911027540883493 8107950380420817663915655)
            ·
              refine ⟨12161925570631226495873483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107950380420817663915655 12161925570631226495873483)
              ·
                refine ⟨18242888355946839743810225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12161925570631226495873483 18242888355946839743810225)
                ·
                  refine ⟨13682166266960129807857669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18242888355946839743810225 13682166266960129807857669)
                  ·
                    refine ⟨2565406175055024338973313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13682166266960129807857669 2565406175055024338973313)
                    ·
                      refine ⟨1924054631291268254229985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565406175055024338973313 1924054631291268254229985)
                      ·
                        rfl

theorem cell23_3747083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 2, 4, 2].length) (baseStart_3747083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747083 prefixEnd_3747083 := by exact prefixLift 3747083
  have htrace : WordTrace (prefixWord ++ tailWord_3747083) baseStart_3747083 baseEnd_3747083 := by
    simpa [prefixWord, tailWord_3747083, baseEnd_3747083] using wordTrace_append hprefix tailTrace_3747083
  have hstable : (prefixWord ++ tailWord_3747083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747083).length < 2 ^ (prefixWord ++ tailWord_3747083).sum := by decide
  have hdescent : baseEnd_3747083 < baseStart_3747083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747103 : List Nat := [1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 3]
def baseStart_3747103 : Nat := 118140960795 + 3747103 * 2 ^ 59
def prefixEnd_3747103 : Nat := 4983230072969 + 3 ^ 40 * 3747103 * 2
def baseEnd_3747103 : Nat := 1924064900904358175979893

theorem tailTrace_3747103 : CollatzResearch.WordTrace tailWord_3747103 prefixEnd_3747103 1924064900904358175979893 := by
  unfold tailWord_3747103
  simp only [CollatzResearch.WordTrace]
  refine ⟨136668074143893260088149963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91112049429262173392099975 136668074143893260088149963)
  ·
    refine ⟨205002111215839890132224945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136668074143893260088149963 205002111215839890132224945)
    ·
      refine ⟨153751583411879917599168709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205002111215839890132224945 153751583411879917599168709)
      ·
        refine ⟨28828421889727484549844133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153751583411879917599168709 28828421889727484549844133)
        ·
          refine ⟨5405329104323903353095775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28828421889727484549844133 5405329104323903353095775)
          ·
            refine ⟨8107993656485855029643663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405329104323903353095775 8107993656485855029643663)
            ·
              refine ⟨12161990484728782544465495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107993656485855029643663 12161990484728782544465495)
              ·
                refine ⟨18242985727093173816698243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12161990484728782544465495 18242985727093173816698243)
                ·
                  refine ⟨27364478590639760725047365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18242985727093173816698243 27364478590639760725047365)
                  ·
                    refine ⟨5130839735744955135946381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27364478590639760725047365 5130839735744955135946381)
                    ·
                      refine ⟨1924064900904358175979893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5130839735744955135946381 1924064900904358175979893)
                      ·
                        rfl

theorem cell23_3747103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_3747103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747103 prefixEnd_3747103 := by exact prefixLift 3747103
  have htrace : WordTrace (prefixWord ++ tailWord_3747103) baseStart_3747103 baseEnd_3747103 := by
    simpa [prefixWord, tailWord_3747103, baseEnd_3747103] using wordTrace_append hprefix tailTrace_3747103
  have hstable : (prefixWord ++ tailWord_3747103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747103).length < 2 ^ (prefixWord ++ tailWord_3747103).sum := by decide
  have hdescent : baseEnd_3747103 < baseStart_3747103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747123 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 6]
def baseStart_3747123 : Nat := 118140960795 + 3747123 * 2 ^ 59
def prefixEnd_3747123 : Nat := 4983230072969 + 3 ^ 40 * 3747123 * 2
def baseEnd_3747123 : Nat := 213786130057494233081089

theorem tailTrace_3747123 : CollatzResearch.WordTrace tailWord_3747123 prefixEnd_3747123 213786130057494233081089 := by
  unfold tailWord_3747123
  simp only [CollatzResearch.WordTrace]
  refine ⟨136668803603820803503878023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91112535735880535669252015 136668803603820803503878023)
  ·
    refine ⟨205003205405731205255817035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136668803603820803503878023 205003205405731205255817035)
    ·
      refine ⟨307504808108596807883725553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205003205405731205255817035 307504808108596807883725553)
      ·
        refine ⟨230628606081447605912794165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307504808108596807883725553 230628606081447605912794165)
        ·
          refine ⟨21621431820135713054324453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 230628606081447605912794165 21621431820135713054324453)
          ·
            refine ⟨4054018466275446197685835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21621431820135713054324453 4054018466275446197685835)
            ·
              refine ⟨6081027699413169296528753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054018466275446197685835 6081027699413169296528753)
              ·
                refine ⟨4560770774559876972396565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081027699413169296528753 4560770774559876972396565)
                ·
                  refine ⟨213786130057494233081089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4560770774559876972396565 213786130057494233081089)
                  ·
                    rfl

theorem cell23_3747123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 6].length) (baseStart_3747123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747123 prefixEnd_3747123 := by exact prefixLift 3747123
  have htrace : WordTrace (prefixWord ++ tailWord_3747123) baseStart_3747123 baseEnd_3747123 := by
    simpa [prefixWord, tailWord_3747123, baseEnd_3747123] using wordTrace_append hprefix tailTrace_3747123
  have hstable : (prefixWord ++ tailWord_3747123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747123).length < 2 ^ (prefixWord ++ tailWord_3747123).sum := by decide
  have hdescent : baseEnd_3747123 < baseStart_3747123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747143 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_3747143 : Nat := 118140960795 + 3747143 * 2 ^ 59
def prefixEnd_3747143 : Nat := 4983230072969 + 3 ^ 40 * 3747143 * 2
def baseEnd_3747143 : Nat := 1924085440130538019479709

theorem tailTrace_3747143 : CollatzResearch.WordTrace tailWord_3747143 prefixEnd_3747143 1924085440130538019479709 := by
  unfold tailWord_3747143
  simp only [CollatzResearch.WordTrace]
  refine ⟨136669533063748346919606083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91113022042498897946404055 136669533063748346919606083)
  ·
    refine ⟨205004299595622520379409125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136669533063748346919606083 205004299595622520379409125)
    ·
      refine ⟨38438306174179222571139211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205004299595622520379409125 38438306174179222571139211)
      ·
        refine ⟨57657459261268833856708817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38438306174179222571139211 57657459261268833856708817)
        ·
          refine ⟨43243094445951625392531613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57657459261268833856708817 43243094445951625392531613)
          ·
            refine ⟨16216160417231859522199355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43243094445951625392531613 16216160417231859522199355)
            ·
              refine ⟨24324240625847789283299033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16216160417231859522199355 24324240625847789283299033)
              ·
                refine ⟨18243180469385841962474275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24324240625847789283299033 18243180469385841962474275)
                ·
                  refine ⟨27364770704078762943711413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18243180469385841962474275 27364770704078762943711413)
                  ·
                    refine ⟨2565447253507384025972945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27364770704078762943711413 2565447253507384025972945)
                    ·
                      refine ⟨1924085440130538019479709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565447253507384025972945 1924085440130538019479709)
                      ·
                        rfl

theorem cell23_3747143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_3747143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747143 prefixEnd_3747143 := by exact prefixLift 3747143
  have htrace : WordTrace (prefixWord ++ tailWord_3747143) baseStart_3747143 baseEnd_3747143 := by
    simpa [prefixWord, tailWord_3747143, baseEnd_3747143] using wordTrace_append hprefix tailTrace_3747143
  have hstable : (prefixWord ++ tailWord_3747143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747143).length < 2 ^ (prefixWord ++ tailWord_3747143).sum := by decide
  have hdescent : baseEnd_3747143 < baseStart_3747143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747153 : List Nat := [1, 2, 2, 1, 4, 1, 4, 2, 1, 5]
def baseStart_3747153 : Nat := 118140960795 + 3747153 * 2 ^ 59
def prefixEnd_3747153 : Nat := 4983230072969 + 3 ^ 40 * 3747153 * 2
def baseEnd_3747153 : Nat := 641363524979027660118221

theorem tailTrace_3747153 : CollatzResearch.WordTrace tailWord_3747153 prefixEnd_3747153 641363524979027660118221 := by
  unfold tailWord_3747153
  simp only [CollatzResearch.WordTrace]
  refine ⟨136669897793712118627470113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91113265195808079084980075 136669897793712118627470113)
  ·
    refine ⟨102502423345284088970602585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136669897793712118627470113 102502423345284088970602585)
    ·
      refine ⟨76876817508963066727951939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102502423345284088970602585 76876817508963066727951939)
      ·
        refine ⟨115315226263444600091927909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76876817508963066727951939 115315226263444600091927909)
        ·
          refine ⟨21621604924395862517236483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115315226263444600091927909 21621604924395862517236483)
          ·
            refine ⟨32432407386593793775854725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21621604924395862517236483 32432407386593793775854725)
            ·
              refine ⟨6081076384986336332972761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32432407386593793775854725 6081076384986336332972761)
              ·
                refine ⟨4560807288739752249729571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081076384986336332972761 4560807288739752249729571)
                ·
                  refine ⟨6841210933109628374594357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560807288739752249729571 6841210933109628374594357)
                  ·
                    refine ⟨641363524979027660118221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6841210933109628374594357 641363524979027660118221)
                    ·
                      rfl

theorem cell23_3747153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_3747153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747153 prefixEnd_3747153 := by exact prefixLift 3747153
  have htrace : WordTrace (prefixWord ++ tailWord_3747153) baseStart_3747153 baseEnd_3747153 := by
    simpa [prefixWord, tailWord_3747153, baseEnd_3747153] using wordTrace_append hprefix tailTrace_3747153
  have hstable : (prefixWord ++ tailWord_3747153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747153).length < 2 ^ (prefixWord ++ tailWord_3747153).sum := by decide
  have hdescent : baseEnd_3747153 < baseStart_3747153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747173 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_3747173 : Nat := 118140960795 + 3747173 * 2 ^ 59
def prefixEnd_3747173 : Nat := 4983230072969 + 3 ^ 40 * 3747173 * 2
def baseEnd_3747173 : Nat := 1924100844550172902104571

theorem tailTrace_3747173 : CollatzResearch.WordTrace tailWord_3747173 prefixEnd_3747173 1924100844550172902104571 := by
  unfold tailWord_3747173
  simp only [CollatzResearch.WordTrace]
  refine ⟨136670627253639662043198173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91113751502426441362132115 136670627253639662043198173)
  ·
    refine ⟨51251485220114873266199315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136670627253639662043198173 51251485220114873266199315)
    ·
      refine ⟨76877227830172309899298973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51251485220114873266199315 76877227830172309899298973)
      ·
        refine ⟨28828960436314616212237115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76877227830172309899298973 28828960436314616212237115)
        ·
          refine ⟨43243440654471924318355673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28828960436314616212237115 43243440654471924318355673)
          ·
            refine ⟨32432580490853943238766755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43243440654471924318355673 32432580490853943238766755)
            ·
              refine ⟨48648870736280914858150133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32432580490853943238766755 48648870736280914858150133)
              ·
                refine ⟨4560831631526335767951575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48648870736280914858150133 4560831631526335767951575)
                ·
                  refine ⟨6841247447289503651927363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560831631526335767951575 6841247447289503651927363)
                  ·
                    refine ⟨10261871170934255477891045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6841247447289503651927363 10261871170934255477891045)
                    ·
                      refine ⟨1924100844550172902104571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10261871170934255477891045 1924100844550172902104571)
                      ·
                        rfl

theorem cell23_3747173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_3747173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747173 prefixEnd_3747173 := by exact prefixLift 3747173
  have htrace : WordTrace (prefixWord ++ tailWord_3747173) baseStart_3747173 baseEnd_3747173 := by
    simpa [prefixWord, tailWord_3747173, baseEnd_3747173] using wordTrace_append hprefix tailTrace_3747173
  have hstable : (prefixWord ++ tailWord_3747173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747173).length < 2 ^ (prefixWord ++ tailWord_3747173).sum := by decide
  have hdescent : baseEnd_3747173 < baseStart_3747173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747183 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 2, 4]
def baseStart_3747183 : Nat := 118140960795 + 3747183 * 2 ^ 59
def prefixEnd_3747183 : Nat := 4983230072969 + 3 ^ 40 * 3747183 * 2
def baseEnd_3747183 : Nat := 641368659785572620993175

theorem tailTrace_3747183 : CollatzResearch.WordTrace tailWord_3747183 prefixEnd_3747183 641368659785572620993175 := by
  unfold tailWord_3747183
  simp only [CollatzResearch.WordTrace]
  refine ⟨136670991983603433751062203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91113994655735622500708135 136670991983603433751062203)
  ·
    refine ⟨205006487975405150626593305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136670991983603433751062203 205006487975405150626593305)
    ·
      refine ⟨153754865981553862969944979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205006487975405150626593305 153754865981553862969944979)
      ·
        refine ⟨230632298972330794454917469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153754865981553862969944979 230632298972330794454917469)
        ·
          refine ⟨86487112114624047920594051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230632298972330794454917469 86487112114624047920594051)
          ·
            refine ⟨129730668171936071880891077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86487112114624047920594051 129730668171936071880891077)
            ·
              refine ⟨24324500282238013477667077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129730668171936071880891077 24324500282238013477667077)
              ·
                refine ⟨4560843802919627527062577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24324500282238013477667077 4560843802919627527062577)
                ·
                  refine ⟨3420632852189720645296933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4560843802919627527062577 3420632852189720645296933)
                  ·
                    refine ⟨641368659785572620993175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3420632852189720645296933 641368659785572620993175)
                    ·
                      rfl

theorem cell23_3747183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 2, 4].length) (baseStart_3747183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747183 prefixEnd_3747183 := by exact prefixLift 3747183
  have htrace : WordTrace (prefixWord ++ tailWord_3747183) baseStart_3747183 baseEnd_3747183 := by
    simpa [prefixWord, tailWord_3747183, baseEnd_3747183] using wordTrace_append hprefix tailTrace_3747183
  have hstable : (prefixWord ++ tailWord_3747183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747183).length < 2 ^ (prefixWord ++ tailWord_3747183).sum := by decide
  have hdescent : baseEnd_3747183 < baseStart_3747183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747186 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3747186 : Nat := 118140960795 + 3747186 * 2 ^ 59
def prefixEnd_3747186 : Nat := 4983230072969 + 3 ^ 40 * 3747186 * 2
def baseEnd_3747186 : Nat := 1924107519798681351242011

theorem tailTrace_3747186 : CollatzResearch.WordTrace tailWord_3747186 prefixEnd_3747186 1924107519798681351242011 := by
  unfold tailWord_3747186
  simp only [CollatzResearch.WordTrace]
  refine ⟨34167775350648141315855353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91114067601728376842280941 34167775350648141315855353)
  ·
    refine ⟨25625831512986105986891515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34167775350648141315855353 25625831512986105986891515)
    ·
      refine ⟨38438747269479158980337273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25625831512986105986891515 38438747269479158980337273)
      ·
        refine ⟨28829060452109369235252955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38438747269479158980337273 28829060452109369235252955)
        ·
          refine ⟨43243590678164053852879433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28829060452109369235252955 43243590678164053852879433)
          ·
            refine ⟨32432693008623040389659575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43243590678164053852879433 32432693008623040389659575)
            ·
              refine ⟨48649039512934560584489363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32432693008623040389659575 48649039512934560584489363)
              ·
                refine ⟨72973559269401840876734045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48649039512934560584489363 72973559269401840876734045)
                ·
                  refine ⟨27365084726025690328775267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72973559269401840876734045 27365084726025690328775267)
                  ·
                    refine ⟨41047627089038535493162901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27365084726025690328775267 41047627089038535493162901)
                    ·
                      refine ⟨1924107519798681351242011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41047627089038535493162901 1924107519798681351242011)
                      ·
                        rfl

theorem cell23_3747186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3747186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747186 prefixEnd_3747186 := by exact prefixLift 3747186
  have htrace : WordTrace (prefixWord ++ tailWord_3747186) baseStart_3747186 baseEnd_3747186 := by
    simpa [prefixWord, tailWord_3747186, baseEnd_3747186] using wordTrace_append hprefix tailTrace_3747186
  have hstable : (prefixWord ++ tailWord_3747186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747186).length < 2 ^ (prefixWord ++ tailWord_3747186).sum := by decide
  have hdescent : baseEnd_3747186 < baseStart_3747186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747196 : List Nat := [2, 2, 2, 1, 1, 1, 6, 8]
def baseStart_3747196 : Nat := 118140960795 + 3747196 * 2 ^ 59
def prefixEnd_3747196 : Nat := 4983230072969 + 3 ^ 40 * 3747196 * 2
def baseEnd_3747196 : Nat := 71263431652045418967295

theorem tailTrace_3747196 : CollatzResearch.WordTrace tailWord_3747196 prefixEnd_3747196 71263431652045418967295 := by
  unfold tailWord_3747196
  simp only [CollatzResearch.WordTrace]
  refine ⟨68335733066278168485642721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91114310755037557980856961 68335733066278168485642721)
  ·
    refine ⟨51251799799708626364232041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68335733066278168485642721 51251799799708626364232041)
    ·
      refine ⟨38438849849781469773174031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51251799799708626364232041 38438849849781469773174031)
      ·
        refine ⟨57658274774672204659761047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38438849849781469773174031 57658274774672204659761047)
        ·
          refine ⟨86487412162008306989641571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57658274774672204659761047 86487412162008306989641571)
          ·
            refine ⟨129731118243012460484462357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86487412162008306989641571 129731118243012460484462357)
            ·
              refine ⟨6081146167641209085209173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129731118243012460484462357 6081146167641209085209173)
              ·
                refine ⟨71263431652045418967295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6081146167641209085209173 71263431652045418967295)
                ·
                  rfl

theorem cell23_3747196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 8].length) (baseStart_3747196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747196 prefixEnd_3747196 := by exact prefixLift 3747196
  have htrace : WordTrace (prefixWord ++ tailWord_3747196) baseStart_3747196 baseEnd_3747196 := by
    simpa [prefixWord, tailWord_3747196, baseEnd_3747196] using wordTrace_append hprefix tailTrace_3747196
  have hstable : (prefixWord ++ tailWord_3747196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747196).length < 2 ^ (prefixWord ++ tailWord_3747196).sum := by decide
  have hdescent : baseEnd_3747196 < baseStart_3747196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747220 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_3747220 : Nat := 118140960795 + 3747220 * 2 ^ 59
def prefixEnd_3747220 : Nat := 4983230072969 + 3 ^ 40 * 3747220 * 2
def baseEnd_3747220 : Nat := 1924124978140934218216855

theorem tailTrace_3747220 : CollatzResearch.WordTrace tailWord_3747220 prefixEnd_3747220 1924124978140934218216855 := by
  unfold tailWord_3747220
  simp only [CollatzResearch.WordTrace]
  refine ⟨68336170742234694535079557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91114894322979592713439409 68336170742234694535079557)
  ·
    refine ⟨12813032014169005225327417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68336170742234694535079557 12813032014169005225327417)
    ·
      refine ⟨9609774010626753918995563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12813032014169005225327417 9609774010626753918995563)
      ·
        refine ⟨14414661015940130878493345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9609774010626753918995563 14414661015940130878493345)
        ·
          refine ⟨10810995761955098158870009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14414661015940130878493345 10810995761955098158870009)
          ·
            refine ⟨8108246821466323619152507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10810995761955098158870009 8108246821466323619152507)
            ·
              refine ⟨12162370232199485428728761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108246821466323619152507 12162370232199485428728761)
              ·
                refine ⟨9121777674149614071546571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12162370232199485428728761 9121777674149614071546571)
                ·
                  refine ⟨13682666511224421107319857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9121777674149614071546571 13682666511224421107319857)
                  ·
                    refine ⟨10261999883418315830489893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13682666511224421107319857 10261999883418315830489893)
                    ·
                      refine ⟨1924124978140934218216855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10261999883418315830489893 1924124978140934218216855)
                      ·
                        rfl

theorem cell23_3747220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_3747220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747220 prefixEnd_3747220 := by exact prefixLift 3747220
  have htrace : WordTrace (prefixWord ++ tailWord_3747220) baseStart_3747220 baseEnd_3747220 := by
    simpa [prefixWord, tailWord_3747220, baseEnd_3747220] using wordTrace_append hprefix tailTrace_3747220
  have hstable : (prefixWord ++ tailWord_3747220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747220).length < 2 ^ (prefixWord ++ tailWord_3747220).sum := by decide
  have hdescent : baseEnd_3747220 < baseStart_3747220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747230 : List Nat := [4, 3, 1, 2, 3, 10]
def baseStart_3747230 : Nat := 118140960795 + 3747230 * 2 ^ 59
def prefixEnd_3747230 : Nat := 4983230072969 + 3 ^ 40 * 3747230 * 2
def baseEnd_3747230 : Nat := 7918230917479338185563

theorem tailTrace_3747230 : CollatzResearch.WordTrace tailWord_3747230 prefixEnd_3747230 7918230917479338185563 := by
  unfold tailWord_3747230
  simp only [CollatzResearch.WordTrace]
  refine ⟨17084088276804145097252893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91115137476288773852015429 17084088276804145097252893)
  ·
    refine ⟨6406533103801554411469835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17084088276804145097252893 6406533103801554411469835)
    ·
      refine ⟨9609799655702331617204753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6406533103801554411469835 9609799655702331617204753)
      ·
        refine ⟨7207349741776748712903565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9609799655702331617204753 7207349741776748712903565)
        ·
          refine ⟨2702756153166280767338837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7207349741776748712903565 2702756153166280767338837)
          ·
            refine ⟨7918230917479338185563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2702756153166280767338837 7918230917479338185563)
            ·
              rfl

theorem cell23_3747230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 10].length) (baseStart_3747230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747230 prefixEnd_3747230 := by exact prefixLift 3747230
  have htrace : WordTrace (prefixWord ++ tailWord_3747230) baseStart_3747230 baseEnd_3747230 := by
    simpa [prefixWord, tailWord_3747230, baseEnd_3747230] using wordTrace_append hprefix tailTrace_3747230
  have hstable : (prefixWord ++ tailWord_3747230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747230).length < 2 ^ (prefixWord ++ tailWord_3747230).sum := by decide
  have hdescent : baseEnd_3747230 < baseStart_3747230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747256 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_3747256 : Nat := 118140960795 + 3747256 * 2 ^ 59
def prefixEnd_3747256 : Nat := 4983230072969 + 3 ^ 40 * 3747256 * 2
def baseEnd_3747256 : Nat := 641381154481498692455563

theorem tailTrace_3747256 : CollatzResearch.WordTrace tailWord_3747256 prefixEnd_3747256 641381154481498692455563 := by
  unfold tailWord_3747256
  simp only [CollatzResearch.WordTrace]
  refine ⟨68336827256169483609234811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91115769674892644812313081 68336827256169483609234811)
  ·
    refine ⟨102505240884254225413852217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68336827256169483609234811 102505240884254225413852217)
    ·
      refine ⟨76878930663190669060389163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102505240884254225413852217 76878930663190669060389163)
      ·
        refine ⟨115318395994786003590583745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76878930663190669060389163 115318395994786003590583745)
        ·
          refine ⟨86488796996089502692937809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115318395994786003590583745 86488796996089502692937809)
          ·
            refine ⟨64866597747067127019703357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86488796996089502692937809 64866597747067127019703357)
            ·
              refine ⟨24324974155150172632388759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64866597747067127019703357 24324974155150172632388759)
              ·
                refine ⟨36487461232725258948583139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24324974155150172632388759 36487461232725258948583139)
                ·
                  refine ⟨54731191849087888422874709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36487461232725258948583139 54731191849087888422874709)
                  ·
                    refine ⟨641381154481498692455563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 54731191849087888422874709 641381154481498692455563)
                    ·
                      rfl

theorem cell23_3747256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_3747256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747256 prefixEnd_3747256 := by exact prefixLift 3747256
  have htrace : WordTrace (prefixWord ++ tailWord_3747256) baseStart_3747256 baseEnd_3747256 := by
    simpa [prefixWord, tailWord_3747256, baseEnd_3747256] using wordTrace_append hprefix tailTrace_3747256
  have hstable : (prefixWord ++ tailWord_3747256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747256).length < 2 ^ (prefixWord ++ tailWord_3747256).sum := by decide
  have hdescent : baseEnd_3747256 < baseStart_3747256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747280 : List Nat := [2, 1, 1, 1, 1, 2, 2, 3, 6, 2, 2]
def baseStart_3747280 : Nat := 118140960795 + 3747280 * 2 ^ 59
def prefixEnd_3747280 : Nat := 4983230072969 + 3 ^ 40 * 3747280 * 2
def baseEnd_3747280 : Nat := 1924155786980203983466579

theorem tailTrace_3747280 : CollatzResearch.WordTrace tailWord_3747280 prefixEnd_3747280 1924155786980203983466579 := by
  unfold tailWord_3747280
  simp only [CollatzResearch.WordTrace]
  refine ⟨68337264932126009658671647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91116353242834679544895529 68337264932126009658671647)
  ·
    refine ⟨102505897398189014488007471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68337264932126009658671647 102505897398189014488007471)
    ·
      refine ⟨153758846097283521732011207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102505897398189014488007471 153758846097283521732011207)
      ·
        refine ⟨230638269145925282598016811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153758846097283521732011207 230638269145925282598016811)
        ·
          refine ⟨345957403718887923897025217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230638269145925282598016811 345957403718887923897025217)
          ·
            refine ⟨259468052789165942922768913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 345957403718887923897025217 259468052789165942922768913)
            ·
              refine ⟨194601039591874457192076685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259468052789165942922768913 194601039591874457192076685)
              ·
                refine ⟨72975389846952921447028757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 194601039591874457192076685 72975389846952921447028757)
                ·
                  refine ⟨3420721399075918192829473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 72975389846952921447028757 3420721399075918192829473)
                  ·
                    refine ⟨2565541049306938644622105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420721399075918192829473 2565541049306938644622105)
                    ·
                      refine ⟨1924155786980203983466579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565541049306938644622105 1924155786980203983466579)
                      ·
                        rfl

theorem cell23_3747280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 3, 6, 2, 2].length) (baseStart_3747280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747280 prefixEnd_3747280 := by exact prefixLift 3747280
  have htrace : WordTrace (prefixWord ++ tailWord_3747280) baseStart_3747280 baseEnd_3747280 := by
    simpa [prefixWord, tailWord_3747280, baseEnd_3747280] using wordTrace_append hprefix tailTrace_3747280
  have hstable : (prefixWord ++ tailWord_3747280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747280).length < 2 ^ (prefixWord ++ tailWord_3747280).sum := by decide
  have hdescent : baseEnd_3747280 < baseStart_3747280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747284 : List Nat := [2, 4, 1, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_3747284 : Nat := 118140960795 + 3747284 * 2 ^ 59
def prefixEnd_3747284 : Nat := 4983230072969 + 3 ^ 40 * 3747284 * 2
def baseEnd_3747284 : Nat := 1924157840902821967816561

theorem tailTrace_3747284 : CollatzResearch.WordTrace tailWord_3747284 prefixEnd_3747284 1924157840902821967816561 := by
  unfold tailWord_3747284
  simp only [CollatzResearch.WordTrace]
  refine ⟨68337337878118764000244453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91116450504158352000325937 68337337878118764000244453)
  ·
    refine ⟨12813250852147268250045835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68337337878118764000244453 12813250852147268250045835)
    ·
      refine ⟨19219876278220902375068753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12813250852147268250045835 19219876278220902375068753)
      ·
        refine ⟨14414907208665676781301565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19219876278220902375068753 14414907208665676781301565)
        ·
          refine ⟨5405590203249628792988087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14414907208665676781301565 5405590203249628792988087)
          ·
            refine ⟨8108385304874443189482131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405590203249628792988087 8108385304874443189482131)
            ·
              refine ⟨12162577957311664784223197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108385304874443189482131 12162577957311664784223197)
              ·
                refine ⟨4560966733991874294083699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12162577957311664784223197 4560966733991874294083699)
                ·
                  refine ⟨6841450100987811441125549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4560966733991874294083699 6841450100987811441125549)
                  ·
                    refine ⟨2565543787870429290422081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6841450100987811441125549 2565543787870429290422081)
                    ·
                      refine ⟨1924157840902821967816561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565543787870429290422081 1924157840902821967816561)
                      ·
                        rfl

theorem cell23_3747284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_3747284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747284 prefixEnd_3747284 := by exact prefixLift 3747284
  have htrace : WordTrace (prefixWord ++ tailWord_3747284) baseStart_3747284 baseEnd_3747284 := by
    simpa [prefixWord, tailWord_3747284, baseEnd_3747284] using wordTrace_append hprefix tailTrace_3747284
  have hstable : (prefixWord ++ tailWord_3747284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747284).length < 2 ^ (prefixWord ++ tailWord_3747284).sum := by decide
  have hdescent : baseEnd_3747284 < baseStart_3747284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747296 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_3747296 : Nat := 118140960795 + 3747296 * 2 ^ 59
def prefixEnd_3747296 : Nat := 4983230072969 + 3 ^ 40 * 3747296 * 2
def baseEnd_3747296 : Nat := 1924164002670675920866505

theorem tailTrace_3747296 : CollatzResearch.WordTrace tailWord_3747296 prefixEnd_3747296 1924164002670675920866505 := by
  unfold tailWord_3747296
  simp only [CollatzResearch.WordTrace]
  refine ⟨68337556716097027024962871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91116742288129369366617161 68337556716097027024962871)
  ·
    refine ⟨102506335074145540537444307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68337556716097027024962871 102506335074145540537444307)
    ·
      refine ⟨153759502611218310806166461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102506335074145540537444307 153759502611218310806166461)
      ·
        refine ⟨57659813479206866552312423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153759502611218310806166461 57659813479206866552312423)
        ·
          refine ⟨86489720218810299828468635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57659813479206866552312423 86489720218810299828468635)
          ·
            refine ⟨129734580328215449742702953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86489720218810299828468635 129734580328215449742702953)
            ·
              refine ⟨97300935246161587307027215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129734580328215449742702953 97300935246161587307027215)
              ·
                refine ⟨145951402869242380960540823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97300935246161587307027215 145951402869242380960540823)
                ·
                  refine ⟨218927104303863571440811235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 145951402869242380960540823 218927104303863571440811235)
                  ·
                    refine ⟨328390656455795357161216853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 218927104303863571440811235 328390656455795357161216853)
                    ·
                      refine ⟨1924164002670675920866505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 328390656455795357161216853 1924164002670675920866505)
                      ·
                        rfl

theorem cell23_3747296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_3747296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747296 prefixEnd_3747296 := by exact prefixLift 3747296
  have htrace : WordTrace (prefixWord ++ tailWord_3747296) baseStart_3747296 baseEnd_3747296 := by
    simpa [prefixWord, tailWord_3747296, baseEnd_3747296] using wordTrace_append hprefix tailTrace_3747296
  have hstable : (prefixWord ++ tailWord_3747296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747296).length < 2 ^ (prefixWord ++ tailWord_3747296).sum := by decide
  have hdescent : baseEnd_3747296 < baseStart_3747296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747297 : List Nat := [1, 2, 3, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_3747297 : Nat := 118140960795 + 3747297 * 2 ^ 59
def prefixEnd_3747297 : Nat := 4983230072969 + 3 ^ 40 * 3747297 * 2
def baseEnd_3747297 : Nat := 1924164516151330416954001

theorem tailTrace_3747297 : CollatzResearch.WordTrace tailWord_3747297 prefixEnd_3747297 1924164516151330416954001 := by
  unfold tailWord_3747297
  simp only [CollatzResearch.WordTrace]
  refine ⟨136675149905190431220712145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91116766603460287480474763 136675149905190431220712145)
  ·
    refine ⟨102506362428892823415534109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136675149905190431220712145 102506362428892823415534109)
    ·
      refine ⟨38439885910834808780825291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102506362428892823415534109 38439885910834808780825291)
      ·
        refine ⟨57659828866252213171237937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38439885910834808780825291 57659828866252213171237937)
        ·
          refine ⟨43244871649689159878428453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57659828866252213171237937 43244871649689159878428453)
          ·
            refine ⟨8108413434316717477205335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43244871649689159878428453 8108413434316717477205335)
            ·
              refine ⟨12162620151475076215808003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108413434316717477205335 12162620151475076215808003)
              ·
                refine ⟨18243930227212614323712005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12162620151475076215808003 18243930227212614323712005)
                ·
                  refine ⟨3420736917602365185696001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18243930227212614323712005 3420736917602365185696001)
                  ·
                    refine ⟨2565552688201773889272001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420736917602365185696001 2565552688201773889272001)
                    ·
                      refine ⟨1924164516151330416954001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565552688201773889272001 1924164516151330416954001)
                      ·
                        rfl

theorem cell23_3747297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_3747297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747297 prefixEnd_3747297 := by exact prefixLift 3747297
  have htrace : WordTrace (prefixWord ++ tailWord_3747297) baseStart_3747297 baseEnd_3747297 := by
    simpa [prefixWord, tailWord_3747297, baseEnd_3747297] using wordTrace_append hprefix tailTrace_3747297
  have hstable : (prefixWord ++ tailWord_3747297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747297).length < 2 ^ (prefixWord ++ tailWord_3747297).sum := by decide
  have hdescent : baseEnd_3747297 < baseStart_3747297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747303 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 7]
def baseStart_3747303 : Nat := 118140960795 + 3747303 * 2 ^ 59
def prefixEnd_3747303 : Nat := 4983230072969 + 3 ^ 40 * 3747303 * 2
def baseEnd_3747303 : Nat := 213796399670584154830997

theorem tailTrace_3747303 : CollatzResearch.WordTrace tailWord_3747303 prefixEnd_3747303 213796399670584154830997 := by
  unfold tailWord_3747303
  simp only [CollatzResearch.WordTrace]
  refine ⟨136675368743168694245430563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91116912495445796163620375 136675368743168694245430563)
  ·
    refine ⟨205013053114753041368145845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136675368743168694245430563 205013053114753041368145845)
    ·
      refine ⟨19219973729508097628263673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205013053114753041368145845 19219973729508097628263673)
      ·
        refine ⟨14414980297131073221197755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19219973729508097628263673 14414980297131073221197755)
        ·
          refine ⟨21622470445696609831796633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14414980297131073221197755 21622470445696609831796633)
          ·
            refine ⟨16216852834272457373847475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21622470445696609831796633 16216852834272457373847475)
            ·
              refine ⟨24325279251408686060771213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16216852834272457373847475 24325279251408686060771213)
              ·
                refine ⟨9121979719278257272789205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24325279251408686060771213 9121979719278257272789205)
                ·
                  refine ⟨213796399670584154830997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9121979719278257272789205 213796399670584154830997)
                  ·
                    rfl

theorem cell23_3747303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 7].length) (baseStart_3747303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747303 prefixEnd_3747303 := by exact prefixLift 3747303
  have htrace : WordTrace (prefixWord ++ tailWord_3747303) baseStart_3747303 baseEnd_3747303 := by
    simpa [prefixWord, tailWord_3747303, baseEnd_3747303] using wordTrace_append hprefix tailTrace_3747303
  have hstable : (prefixWord ++ tailWord_3747303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747303).length < 2 ^ (prefixWord ++ tailWord_3747303).sum := by decide
  have hdescent : baseEnd_3747303 < baseStart_3747303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747314 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3747314 : Nat := 118140960795 + 3747314 * 2 ^ 59
def prefixEnd_3747314 : Nat := 4983230072969 + 3 ^ 40 * 3747314 * 2
def baseEnd_3747314 : Nat := 1924173245322456850441423

theorem tailTrace_3747314 : CollatzResearch.WordTrace tailWord_3747314 prefixEnd_3747314 1924173245322456850441423 := by
  unfold tailWord_3747314
  simp only [CollatzResearch.WordTrace]
  refine ⟨34168942486532210781020249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91117179964085895416053997 34168942486532210781020249)
  ·
    refine ⟨25626706864899158085765187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34168942486532210781020249 25626706864899158085765187)
    ·
      refine ⟨38440060297348737128647781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25626706864899158085765187 38440060297348737128647781)
      ·
        refine ⟨7207511305752888211621459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38440060297348737128647781 7207511305752888211621459)
        ·
          refine ⟨10811266958629332317432189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207511305752888211621459 10811266958629332317432189)
          ·
            refine ⟨4054225109485999619037071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10811266958629332317432189 4054225109485999619037071)
            ·
              refine ⟨6081337664228999428555607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054225109485999619037071 6081337664228999428555607)
              ·
                refine ⟨9122006496343499142833411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081337664228999428555607 9122006496343499142833411)
                ·
                  refine ⟨13683009744515248714250117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9122006496343499142833411 13683009744515248714250117)
                  ·
                    refine ⟨2565564327096609133921897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13683009744515248714250117 2565564327096609133921897)
                    ·
                      refine ⟨1924173245322456850441423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565564327096609133921897 1924173245322456850441423)
                      ·
                        rfl

theorem cell23_3747314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3747314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747314 prefixEnd_3747314 := by exact prefixLift 3747314
  have htrace : WordTrace (prefixWord ++ tailWord_3747314) baseStart_3747314 baseEnd_3747314 := by
    simpa [prefixWord, tailWord_3747314, baseEnd_3747314] using wordTrace_append hprefix tailTrace_3747314
  have hstable : (prefixWord ++ tailWord_3747314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747314).length < 2 ^ (prefixWord ++ tailWord_3747314).sum := by decide
  have hdescent : baseEnd_3747314 < baseStart_3747314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747333 : List Nat := [1, 3, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_3747333 : Nat := 118140960795 + 3747333 * 2 ^ 59
def prefixEnd_3747333 : Nat := 4983230072969 + 3 ^ 40 * 3747333 * 2
def baseEnd_3747333 : Nat := 641394333818297425367945

theorem tailTrace_3747333 : CollatzResearch.WordTrace tailWord_3747333 prefixEnd_3747333 641394333818297425367945 := by
  unfold tailWord_3747333
  simp only [CollatzResearch.WordTrace]
  refine ⟨136676462933060009369022653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91117641955373339579348435 136676462933060009369022653)
  ·
    refine ⟨51253673599897503513383495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136676462933060009369022653 51253673599897503513383495)
    ·
      refine ⟨76880510399846255270075243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51253673599897503513383495 76880510399846255270075243)
      ·
        refine ⟨115320765599769382905112865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76880510399846255270075243 115320765599769382905112865)
        ·
          refine ⟨86490574199827037178834649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115320765599769382905112865 86490574199827037178834649)
          ·
            refine ⟨64867930649870277884125987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86490574199827037178834649 64867930649870277884125987)
            ·
              refine ⟨97301895974805416826188981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64867930649870277884125987 97301895974805416826188981)
              ·
                refine ⟨9122052747638007827455217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97301895974805416826188981 9122052747638007827455217)
                ·
                  refine ⟨6841539560728505870591413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9122052747638007827455217 6841539560728505870591413)
                  ·
                    refine ⟨641394333818297425367945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6841539560728505870591413 641394333818297425367945)
                    ·
                      rfl

theorem cell23_3747333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_3747333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747333 prefixEnd_3747333 := by exact prefixLift 3747333
  have htrace : WordTrace (prefixWord ++ tailWord_3747333) baseStart_3747333 baseEnd_3747333 := by
    simpa [prefixWord, tailWord_3747333, baseEnd_3747333] using wordTrace_append hprefix tailTrace_3747333
  have hstable : (prefixWord ++ tailWord_3747333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747333).length < 2 ^ (prefixWord ++ tailWord_3747333).sum := by decide
  have hdescent : baseEnd_3747333 < baseStart_3747333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747360 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3747360 : Nat := 118140960795 + 3747360 * 2 ^ 59
def prefixEnd_3747360 : Nat := 4983230072969 + 3 ^ 40 * 3747360 * 2
def baseEnd_3747360 : Nat := 1924196865432563670466211

theorem tailTrace_3747360 : CollatzResearch.WordTrace tailWord_3747360 prefixEnd_3747360 1924196865432563670466211 := by
  unfold tailWord_3747360
  simp only [CollatzResearch.WordTrace]
  refine ⟨68338723851981096490127767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91118298469308128653503689 68338723851981096490127767)
  ·
    refine ⟨102508085777971644735191651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68338723851981096490127767 102508085777971644735191651)
    ·
      refine ⟨153762128666957467102787477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102508085777971644735191651 153762128666957467102787477)
      ·
        refine ⟨7207599781263631270443163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 153762128666957467102787477 7207599781263631270443163)
        ·
          refine ⟨10811399671895446905664745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7207599781263631270443163 10811399671895446905664745)
          ·
            refine ⟨8108549753921585179248559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10811399671895446905664745 8108549753921585179248559)
            ·
              refine ⟨12162824630882377768872839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108549753921585179248559 12162824630882377768872839)
              ·
                refine ⟨18244236946323566653309259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12162824630882377768872839 18244236946323566653309259)
                ·
                  refine ⟨27366355419485349979963889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18244236946323566653309259 27366355419485349979963889)
                  ·
                    refine ⟨20524766564614012484972917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27366355419485349979963889 20524766564614012484972917)
                    ·
                      refine ⟨1924196865432563670466211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20524766564614012484972917 1924196865432563670466211)
                      ·
                        rfl

theorem cell23_3747360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3747360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747360 prefixEnd_3747360 := by exact prefixLift 3747360
  have htrace : WordTrace (prefixWord ++ tailWord_3747360) baseStart_3747360 baseEnd_3747360 := by
    simpa [prefixWord, tailWord_3747360, baseEnd_3747360] using wordTrace_append hprefix tailTrace_3747360
  have hstable : (prefixWord ++ tailWord_3747360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747360).length < 2 ^ (prefixWord ++ tailWord_3747360).sum := by decide
  have hdescent : baseEnd_3747360 < baseStart_3747360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747370 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3747370 : Nat := 118140960795 + 3747370 * 2 ^ 59
def prefixEnd_3747370 : Nat := 4983230072969 + 3 ^ 40 * 3747370 * 2
def baseEnd_3747370 : Nat := 1924202000239108631341165

theorem tailTrace_3747370 : CollatzResearch.WordTrace tailWord_3747370 prefixEnd_3747370 1924202000239108631341165 := by
  unfold tailWord_3747370
  simp only [CollatzResearch.WordTrace]
  refine ⟨34169453108481491172029891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91118541622617309792079709 34169453108481491172029891)
  ·
    refine ⟨51254179662722236758044837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34169453108481491172029891 51254179662722236758044837)
    ·
      refine ⟨9610158686760419392133407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51254179662722236758044837 9610158686760419392133407)
      ·
        refine ⟨14415238030140629088200111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9610158686760419392133407 14415238030140629088200111)
        ·
          refine ⟨21622857045210943632300167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14415238030140629088200111 21622857045210943632300167)
          ·
            refine ⟨32434285567816415448450251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21622857045210943632300167 32434285567816415448450251)
            ·
              refine ⟨48651428351724623172675377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32434285567816415448450251 48651428351724623172675377)
              ·
                refine ⟨36488571263793467379506533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48651428351724623172675377 36488571263793467379506533)
                ·
                  refine ⟨6841607111961275133657475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36488571263793467379506533 6841607111961275133657475)
                  ·
                    refine ⟨10262410667941912700486213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6841607111961275133657475 10262410667941912700486213)
                    ·
                      refine ⟨1924202000239108631341165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10262410667941912700486213 1924202000239108631341165)
                      ·
                        rfl

theorem cell23_3747370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3747370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747370 prefixEnd_3747370 := by exact prefixLift 3747370
  have htrace : WordTrace (prefixWord ++ tailWord_3747370) baseStart_3747370 baseEnd_3747370 := by
    simpa [prefixWord, tailWord_3747370, baseEnd_3747370] using wordTrace_append hprefix tailTrace_3747370
  have hstable : (prefixWord ++ tailWord_3747370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747370).length < 2 ^ (prefixWord ++ tailWord_3747370).sum := by decide
  have hdescent : baseEnd_3747370 < baseStart_3747370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747397 : List Nat := [1, 3, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_3747397 : Nat := 118140960795 + 3747397 * 2 ^ 59
def prefixEnd_3747397 : Nat := 4983230072969 + 3 ^ 40 * 3747397 * 2
def baseEnd_3747397 : Nat := 641405288072260008567847

theorem tailTrace_3747397 : CollatzResearch.WordTrace tailWord_3747397 prefixEnd_3747397 641405288072260008567847 := by
  unfold tailWord_3747397
  simp only [CollatzResearch.WordTrace]
  refine ⟨136678797204828148299352445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91119198136552098866234963 136678797204828148299352445)
  ·
    refine ⟨51254548951810555612257167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136678797204828148299352445 51254548951810555612257167)
    ·
      refine ⟨76881823427715833418385751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51254548951810555612257167 76881823427715833418385751)
      ·
        refine ⟨115322735141573750127578627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76881823427715833418385751 115322735141573750127578627)
        ·
          refine ⟨172984102712360625191367941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115322735141573750127578627 172984102712360625191367941)
          ·
            refine ⟨32434519258567617223381489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172984102712360625191367941 32434519258567617223381489)
            ·
              refine ⟨24325889443925712917536117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32434519258567617223381489 24325889443925712917536117)
              ·
                refine ⟨2280552135368035586019011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24325889443925712917536117 2280552135368035586019011)
                ·
                  refine ⟨3420828203052053379028517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280552135368035586019011 3420828203052053379028517)
                  ·
                    refine ⟨641405288072260008567847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3420828203052053379028517 641405288072260008567847)
                    ·
                      rfl

theorem cell23_3747397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_3747397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747397 prefixEnd_3747397 := by exact prefixLift 3747397
  have htrace : WordTrace (prefixWord ++ tailWord_3747397) baseStart_3747397 baseEnd_3747397 := by
    simpa [prefixWord, tailWord_3747397, baseEnd_3747397] using wordTrace_append hprefix tailTrace_3747397
  have hstable : (prefixWord ++ tailWord_3747397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747397).length < 2 ^ (prefixWord ++ tailWord_3747397).sum := by decide
  have hdescent : baseEnd_3747397 < baseStart_3747397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747410 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_3747410 : Nat := 118140960795 + 3747410 * 2 ^ 59
def prefixEnd_3747410 : Nat := 4983230072969 + 3 ^ 40 * 3747410 * 2
def baseEnd_3747410 : Nat := 213802504385032052760109

theorem tailTrace_3747410 : CollatzResearch.WordTrace tailWord_3747410 prefixEnd_3747410 213802504385032052760109 := by
  unfold tailWord_3747410
  simp only [CollatzResearch.WordTrace]
  refine ⟨34169817838445262879893921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91119514235854034346383789 34169817838445262879893921)
  ·
    refine ⟨25627363378833947159920441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34169817838445262879893921 25627363378833947159920441)
    ·
      refine ⟨19220522534125460369940331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25627363378833947159920441 19220522534125460369940331)
      ·
        refine ⟨28830783801188190554910497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19220522534125460369940331 28830783801188190554910497)
        ·
          refine ⟨21623087850891142916182873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28830783801188190554910497 21623087850891142916182873)
          ·
            refine ⟨16217315888168357187137155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21623087850891142916182873 16217315888168357187137155)
            ·
              refine ⟨24325973832252535780705733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16217315888168357187137155 24325973832252535780705733)
              ·
                refine ⟨4561120093547350458882325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24325973832252535780705733 4561120093547350458882325)
                ·
                  refine ⟨213802504385032052760109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4561120093547350458882325 213802504385032052760109)
                  ·
                    rfl

theorem cell23_3747410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_3747410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747410 prefixEnd_3747410 := by exact prefixLift 3747410
  have htrace : WordTrace (prefixWord ++ tailWord_3747410) baseStart_3747410 baseEnd_3747410 := by
    simpa [prefixWord, tailWord_3747410, baseEnd_3747410] using wordTrace_append hprefix tailTrace_3747410
  have hstable : (prefixWord ++ tailWord_3747410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747410).length < 2 ^ (prefixWord ++ tailWord_3747410).sum := by decide
  have hdescent : baseEnd_3747410 < baseStart_3747410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747413 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3747413 : Nat := 118140960795 + 3747413 * 2 ^ 59
def prefixEnd_3747413 : Nat := 4983230072969 + 3 ^ 40 * 3747413 * 2
def baseEnd_3747413 : Nat := 1924224079907251963103467

theorem tailTrace_3747413 : CollatzResearch.WordTrace tailWord_3747413 prefixEnd_3747413 1924224079907251963103467 := by
  unfold tailWord_3747413
  simp only [CollatzResearch.WordTrace]
  refine ⟨136679380772770183031934893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91119587181846788687956595 136679380772770183031934893)
  ·
    refine ⟨51254767789788818636975585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136679380772770183031934893 51254767789788818636975585)
    ·
      refine ⟨38441075842341613977731689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51254767789788818636975585 38441075842341613977731689)
      ·
        refine ⟨28830806881756210483298767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38441075842341613977731689 28830806881756210483298767)
        ·
          refine ⟨43246210322634315724948151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28830806881756210483298767 43246210322634315724948151)
          ·
            refine ⟨64869315483951473587422227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43246210322634315724948151 64869315483951473587422227)
            ·
              refine ⟨97303973225927210381133341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64869315483951473587422227 97303973225927210381133341)
              ·
                refine ⟨36488989959722703892925003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97303973225927210381133341 36488989959722703892925003)
                ·
                  refine ⟨54733484939584055839387505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36488989959722703892925003 54733484939584055839387505)
                  ·
                    refine ⟨41050113704688041879540629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54733484939584055839387505 41050113704688041879540629)
                    ·
                      refine ⟨1924224079907251963103467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41050113704688041879540629 1924224079907251963103467)
                      ·
                        rfl

theorem cell23_3747413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3747413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747413 prefixEnd_3747413 := by exact prefixLift 3747413
  have htrace : WordTrace (prefixWord ++ tailWord_3747413) baseStart_3747413 baseEnd_3747413 := by
    simpa [prefixWord, tailWord_3747413, baseEnd_3747413] using wordTrace_append hprefix tailTrace_3747413
  have hstable : (prefixWord ++ tailWord_3747413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747413).length < 2 ^ (prefixWord ++ tailWord_3747413).sum := by decide
  have hdescent : baseEnd_3747413 < baseStart_3747413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747421 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_3747421 : Nat := 118140960795 + 3747421 * 2 ^ 59
def prefixEnd_3747421 : Nat := 4983230072969 + 3 ^ 40 * 3747421 * 2
def baseEnd_3747421 : Nat := 1924228187752487931803431

theorem tailTrace_3747421 : CollatzResearch.WordTrace tailWord_3747421 prefixEnd_3747421 1924228187752487931803431 := by
  unfold tailWord_3747421
  simp only [CollatzResearch.WordTrace]
  refine ⟨136679672556741200398226117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91119781704494133598817411 136679672556741200398226117)
  ·
    refine ⟨25627438604388975074667397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136679672556741200398226117 25627438604388975074667397)
    ·
      refine ⟨4805144738322932826500137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25627438604388975074667397 4805144738322932826500137)
      ·
        refine ⟨3603858553742199619875103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4805144738322932826500137 3603858553742199619875103)
        ·
          refine ⟨5405787830613299429812655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603858553742199619875103 5405787830613299429812655)
          ·
            refine ⟨8108681745919949144718983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405787830613299429812655 8108681745919949144718983)
            ·
              refine ⟨12163022618879923717078475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108681745919949144718983 12163022618879923717078475)
              ·
                refine ⟨18244533928319885575617713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12163022618879923717078475 18244533928319885575617713)
                ·
                  refine ⟨13683400446239914181713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18244533928319885575617713 13683400446239914181713285)
                  ·
                    refine ⟨2565637583669983909071241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13683400446239914181713285 2565637583669983909071241)
                    ·
                      refine ⟨1924228187752487931803431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565637583669983909071241 1924228187752487931803431)
                      ·
                        rfl

theorem cell23_3747421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_3747421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747421 prefixEnd_3747421 := by exact prefixLift 3747421
  have htrace : WordTrace (prefixWord ++ tailWord_3747421) baseStart_3747421 baseEnd_3747421 := by
    simpa [prefixWord, tailWord_3747421, baseEnd_3747421] using wordTrace_append hprefix tailTrace_3747421
  have hstable : (prefixWord ++ tailWord_3747421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747421).length < 2 ^ (prefixWord ++ tailWord_3747421).sum := by decide
  have hdescent : baseEnd_3747421 < baseStart_3747421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747440 : List Nat := [2, 1, 1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_3747440 : Nat := 118140960795 + 3747440 * 2 ^ 59
def prefixEnd_3747440 : Nat := 4983230072969 + 3 ^ 40 * 3747440 * 2
def baseEnd_3747440 : Nat := 641412647961641119155281

theorem tailTrace_3747440 : CollatzResearch.WordTrace tailWord_3747440 prefixEnd_3747440 641412647961641119155281 := by
  unfold tailWord_3747440
  simp only [CollatzResearch.WordTrace]
  refine ⟨68340182771836183321583887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91120243695781577762111849 68340182771836183321583887)
  ·
    refine ⟨102510274157754274982375831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68340182771836183321583887 102510274157754274982375831)
    ·
      refine ⟨153765411236631412473563747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102510274157754274982375831 153765411236631412473563747)
      ·
        refine ⟨230648116854947118710345621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153765411236631412473563747 230648116854947118710345621)
        ·
          refine ⟨10811630477575646189547451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230648116854947118710345621 10811630477575646189547451)
          ·
            refine ⟨16217445716363469284321177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10811630477575646189547451 16217445716363469284321177)
            ·
              refine ⟨12163084287272601963240883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16217445716363469284321177 12163084287272601963240883)
              ·
                refine ⟨18244626430908902944861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12163084287272601963240883 18244626430908902944861325)
                ·
                  refine ⟨6841734911590838604322997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18244626430908902944861325 6841734911590838604322997)
                  ·
                    refine ⟨641412647961641119155281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6841734911590838604322997 641412647961641119155281)
                    ·
                      rfl

theorem cell23_3747440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_3747440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747440 prefixEnd_3747440 := by exact prefixLift 3747440
  have htrace : WordTrace (prefixWord ++ tailWord_3747440) baseStart_3747440 baseEnd_3747440 := by
    simpa [prefixWord, tailWord_3747440, baseEnd_3747440] using wordTrace_append hprefix tailTrace_3747440
  have hstable : (prefixWord ++ tailWord_3747440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747440).length < 2 ^ (prefixWord ++ tailWord_3747440).sum := by decide
  have hdescent : baseEnd_3747440 < baseStart_3747440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747457 : List Nat := [1, 2, 4, 2, 1, 3, 1, 3, 1, 5]
def baseStart_3747457 : Nat := 118140960795 + 3747457 * 2 ^ 59
def prefixEnd_3747457 : Nat := 4983230072969 + 3 ^ 40 * 3747457 * 2
def baseEnd_3747457 : Nat := 641415557685349930317755

theorem tailTrace_3747457 : CollatzResearch.WordTrace tailWord_3747457 prefixEnd_3747457 641415557685349930317755 := by
  unfold tailWord_3747457
  simp only [CollatzResearch.WordTrace]
  refine ⟨136680985584610778546536625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91120657056407185697691083 136680985584610778546536625)
  ·
    refine ⟨102510739188458083909902469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136680985584610778546536625 102510739188458083909902469)
    ·
      refine ⟨19220763597835890733106713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102510739188458083909902469 19220763597835890733106713)
      ·
        refine ⟨14415572698376918049830035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19220763597835890733106713 14415572698376918049830035)
        ·
          refine ⟨21623359047565377074745053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14415572698376918049830035 21623359047565377074745053)
          ·
            refine ⟨8108759642837016403029395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21623359047565377074745053 8108759642837016403029395)
            ·
              refine ⟨12163139464255524604544093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8108759642837016403029395 12163139464255524604544093)
              ·
                refine ⟨4561177299095821726704035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12163139464255524604544093 4561177299095821726704035)
                ·
                  refine ⟨6841765948643732590056053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561177299095821726704035 6841765948643732590056053)
                  ·
                    refine ⟨641415557685349930317755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6841765948643732590056053 641415557685349930317755)
                    ·
                      rfl

theorem cell23_3747457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_3747457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747457 prefixEnd_3747457 := by exact prefixLift 3747457
  have htrace : WordTrace (prefixWord ++ tailWord_3747457) baseStart_3747457 baseEnd_3747457 := by
    simpa [prefixWord, tailWord_3747457, baseEnd_3747457] using wordTrace_append hprefix tailTrace_3747457
  have hstable : (prefixWord ++ tailWord_3747457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747457).length < 2 ^ (prefixWord ++ tailWord_3747457).sum := by decide
  have hdescent : baseEnd_3747457 < baseStart_3747457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747480 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3747480 : Nat := 118140960795 + 3747480 * 2 ^ 59
def prefixEnd_3747480 : Nat := 4983230072969 + 3 ^ 40 * 3747480 * 2
def baseEnd_3747480 : Nat := 1924258483111103200965659

theorem tailTrace_3747480 : CollatzResearch.WordTrace tailWord_3747480 prefixEnd_3747480 1924258483111103200965659 := by
  unfold tailWord_3747480
  simp only [CollatzResearch.WordTrace]
  refine ⟨68340912231763726737311947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91121216309018302316415929 68340912231763726737311947)
  ·
    refine ⟨102511368347645590105967921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68340912231763726737311947 102511368347645590105967921)
    ·
      refine ⟨76883526260734192579475941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102511368347645590105967921 76883526260734192579475941)
      ·
        refine ⟨14415661173887661108651739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76883526260734192579475941 14415661173887661108651739)
        ·
          refine ⟨21623491760831491662977609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14415661173887661108651739 21623491760831491662977609)
          ·
            refine ⟨16217618820623618747233207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21623491760831491662977609 16217618820623618747233207)
            ·
              refine ⟨24326428230935428120849811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16217618820623618747233207 24326428230935428120849811)
              ·
                refine ⟨36489642346403142181274717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24326428230935428120849811 36489642346403142181274717)
                ·
                  refine ⟨13683615879901178317978019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36489642346403142181274717 13683615879901178317978019)
                  ·
                    refine ⟨20525423819851767476967029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13683615879901178317978019 20525423819851767476967029)
                    ·
                      refine ⟨1924258483111103200965659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20525423819851767476967029 1924258483111103200965659)
                      ·
                        rfl

theorem cell23_3747480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3747480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747480 prefixEnd_3747480 := by exact prefixLift 3747480
  have htrace : WordTrace (prefixWord ++ tailWord_3747480) baseStart_3747480 baseEnd_3747480 := by
    simpa [prefixWord, tailWord_3747480, baseEnd_3747480] using wordTrace_append hprefix tailTrace_3747480
  have hstable : (prefixWord ++ tailWord_3747480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747480).length < 2 ^ (prefixWord ++ tailWord_3747480).sum := by decide
  have hdescent : baseEnd_3747480 < baseStart_3747480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747522 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_3747522 : Nat := 118140960795 + 3747522 * 2 ^ 59
def prefixEnd_3747522 : Nat := 4983230072969 + 3 ^ 40 * 3747522 * 2
def baseEnd_3747522 : Nat := 1924280049298592036640467

theorem tailTrace_3747522 : CollatzResearch.WordTrace tailWord_3747522 prefixEnd_3747522 1924280049298592036640467 := by
  unfold tailWord_3747522
  simp only [CollatzResearch.WordTrace]
  refine ⟨34170839082343823661913205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91122237552916863098435213 34170839082343823661913205)
  ·
    refine ⟨3203516163969733468304363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34170839082343823661913205 3203516163969733468304363)
    ·
      refine ⟨4805274245954600202456545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3203516163969733468304363 4805274245954600202456545)
      ·
        refine ⟨3603955684465950151842409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4805274245954600202456545 3603955684465950151842409)
        ·
          refine ⟨2702966763349462613881807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3603955684465950151842409 2702966763349462613881807)
          ·
            refine ⟨4054450145024193920822711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702966763349462613881807 4054450145024193920822711)
            ·
              refine ⟨6081675217536290881234067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054450145024193920822711 6081675217536290881234067)
              ·
                refine ⟨9122512826304436321851101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6081675217536290881234067 9122512826304436321851101)
                ·
                  refine ⟨3420942309864163620694163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9122512826304436321851101 3420942309864163620694163)
                  ·
                    refine ⟨5131413464796245431041245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3420942309864163620694163 5131413464796245431041245)
                    ·
                      refine ⟨1924280049298592036640467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5131413464796245431041245 1924280049298592036640467)
                      ·
                        rfl

theorem cell23_3747522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_3747522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747522 prefixEnd_3747522 := by exact prefixLift 3747522
  have htrace : WordTrace (prefixWord ++ tailWord_3747522) baseStart_3747522 baseEnd_3747522 := by
    simpa [prefixWord, tailWord_3747522, baseEnd_3747522] using wordTrace_append hprefix tailTrace_3747522
  have hstable : (prefixWord ++ tailWord_3747522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747522).length < 2 ^ (prefixWord ++ tailWord_3747522).sum := by decide
  have hdescent : baseEnd_3747522 < baseStart_3747522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747527 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_3747527 : Nat := 118140960795 + 3747527 * 2 ^ 59
def prefixEnd_3747527 : Nat := 4983230072969 + 3 ^ 40 * 3747527 * 2
def baseEnd_3747527 : Nat := 1924282616701864517077943

theorem tailTrace_3747527 : CollatzResearch.WordTrace tailWord_3747527 prefixEnd_3747527 1924282616701864517077943 := by
  unfold tailWord_3747527
  simp only [CollatzResearch.WordTrace]
  refine ⟨136683538694357180501584835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91122359129571453667723223 136683538694357180501584835)
  ·
    refine ⟨205025308041535770752377253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136683538694357180501584835 205025308041535770752377253)
    ·
      refine ⟨38442245257787957016070735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205025308041535770752377253 38442245257787957016070735)
      ·
        refine ⟨57663367886681935524106103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38442245257787957016070735 57663367886681935524106103)
        ·
          refine ⟨86495051830022903286159155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57663367886681935524106103 86495051830022903286159155)
          ·
            refine ⟨129742577745034354929238733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86495051830022903286159155 129742577745034354929238733)
            ·
              refine ⟨48653466654387883098464525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129742577745034354929238733 48653466654387883098464525)
              ·
                refine ⟨18245049995395456161924197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48653466654387883098464525 18245049995395456161924197)
                ·
                  refine ⟨3420946874136648030360787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18245049995395456161924197 3420946874136648030360787)
                  ·
                    refine ⟨5131420311204972045541181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3420946874136648030360787 5131420311204972045541181)
                    ·
                      refine ⟨1924282616701864517077943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5131420311204972045541181 1924282616701864517077943)
                      ·
                        rfl

theorem cell23_3747527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_3747527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747527 prefixEnd_3747527 := by exact prefixLift 3747527
  have htrace : WordTrace (prefixWord ++ tailWord_3747527) baseStart_3747527 baseEnd_3747527 := by
    simpa [prefixWord, tailWord_3747527, baseEnd_3747527] using wordTrace_append hprefix tailTrace_3747527
  have hstable : (prefixWord ++ tailWord_3747527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747527).length < 2 ^ (prefixWord ++ tailWord_3747527).sum := by decide
  have hdescent : baseEnd_3747527 < baseStart_3747527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747528 : List Nat := [2, 1, 3, 1, 2, 2, 5, 2, 1, 2, 2]
def baseStart_3747528 : Nat := 118140960795 + 3747528 * 2 ^ 59
def prefixEnd_3747528 : Nat := 4983230072969 + 3 ^ 40 * 3747528 * 2
def baseEnd_3747528 : Nat := 1924283130182519013165439

theorem tailTrace_3747528 : CollatzResearch.WordTrace tailWord_3747528 prefixEnd_3747528 1924283130182519013165439 := by
  unfold tailWord_3747528
  simp only [CollatzResearch.WordTrace]
  refine ⟨68341787583676778836185619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91122383444902371781580825 68341787583676778836185619)
  ·
    refine ⟨102512681375515168254278429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68341787583676778836185619 102512681375515168254278429)
    ·
      refine ⟨38442255515818188095354411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102512681375515168254278429 38442255515818188095354411)
      ·
        refine ⟨57663383273727282143031617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38442255515818188095354411 57663383273727282143031617)
        ·
          refine ⟨43247537455295461607273713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57663383273727282143031617 43247537455295461607273713)
          ·
            refine ⟨32435653091471596205455285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43247537455295461607273713 32435653091471596205455285)
            ·
              refine ⟨3040842477325462144261433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32435653091471596205455285 3040842477325462144261433)
              ·
                refine ⟨2280631857994096608196075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040842477325462144261433 2280631857994096608196075)
                ·
                  refine ⟨3420947786991144912294113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2280631857994096608196075 3420947786991144912294113)
                  ·
                    refine ⟨2565710840243358684220585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3420947786991144912294113 2565710840243358684220585)
                    ·
                      refine ⟨1924283130182519013165439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565710840243358684220585 1924283130182519013165439)
                      ·
                        rfl

theorem cell23_3747528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_3747528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747528 prefixEnd_3747528 := by exact prefixLift 3747528
  have htrace : WordTrace (prefixWord ++ tailWord_3747528) baseStart_3747528 baseEnd_3747528 := by
    simpa [prefixWord, tailWord_3747528, baseEnd_3747528] using wordTrace_append hprefix tailTrace_3747528
  have hstable : (prefixWord ++ tailWord_3747528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747528).length < 2 ^ (prefixWord ++ tailWord_3747528).sum := by decide
  have hdescent : baseEnd_3747528 < baseStart_3747528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747544 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 2, 1, 3]
def baseStart_3747544 : Nat := 118140960795 + 3747544 * 2 ^ 59
def prefixEnd_3747544 : Nat := 4983230072969 + 3 ^ 40 * 3747544 * 2
def baseEnd_3747544 : Nat := 1924291345872990950565365

theorem tailTrace_3747544 : CollatzResearch.WordTrace tailWord_3747544 prefixEnd_3747544 1924291345872990950565365 := by
  unfold tailWord_3747544
  simp only [CollatzResearch.WordTrace]
  refine ⟨68342079367647796202476843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91122772490197061603302457 68342079367647796202476843)
  ·
    refine ⟨102513119051471694303715265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68342079367647796202476843 102513119051471694303715265)
    ·
      refine ⟨76884839288603770727786449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102513119051471694303715265 76884839288603770727786449)
      ·
        refine ⟨57663629466452828045839837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76884839288603770727786449 57663629466452828045839837)
        ·
          refine ⟨21623861049919810517189939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57663629466452828045839837 21623861049919810517189939)
          ·
            refine ⟨32435791574879715775784909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21623861049919810517189939 32435791574879715775784909)
            ·
              refine ⟨12163421840579893415919341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32435791574879715775784909 12163421840579893415919341)
              ·
                refine ⟨4561283190217460030969753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12163421840579893415919341 4561283190217460030969753)
                ·
                  refine ⟨3420962392663095023227315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561283190217460030969753 3420962392663095023227315)
                  ·
                    refine ⟨5131443588994642534840973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3420962392663095023227315 5131443588994642534840973)
                    ·
                      refine ⟨1924291345872990950565365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5131443588994642534840973 1924291345872990950565365)
                      ·
                        rfl

theorem cell23_3747544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_3747544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747544 prefixEnd_3747544 := by exact prefixLift 3747544
  have htrace : WordTrace (prefixWord ++ tailWord_3747544) baseStart_3747544 baseEnd_3747544 := by
    simpa [prefixWord, tailWord_3747544, baseEnd_3747544] using wordTrace_append hprefix tailTrace_3747544
  have hstable : (prefixWord ++ tailWord_3747544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747544).length < 2 ^ (prefixWord ++ tailWord_3747544).sum := by decide
  have hdescent : baseEnd_3747544 < baseStart_3747544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747548 : List Nat := [2, 2, 5, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_3747548 : Nat := 118140960795 + 3747548 * 2 ^ 59
def prefixEnd_3747548 : Nat := 4983230072969 + 3 ^ 40 * 3747548 * 2
def baseEnd_3747548 : Nat := 1924293399795608934915347

theorem tailTrace_3747548 : CollatzResearch.WordTrace tailWord_3747548 prefixEnd_3747548 1924293399795608934915347 := by
  unfold tailWord_3747548
  simp only [CollatzResearch.WordTrace]
  refine ⟨68342152313640550544049649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91122869751520734058732865 68342152313640550544049649)
  ·
    refine ⟨51256614235230412908037237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68342152313640550544049649 51256614235230412908037237)
    ·
      refine ⟨4805307584552851210128491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51256614235230412908037237 4805307584552851210128491)
      ·
        refine ⟨7207961376829276815192737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4805307584552851210128491 7207961376829276815192737)
        ·
          refine ⟨5405971032621957611394553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207961376829276815192737 5405971032621957611394553)
          ·
            refine ⟨4054478274466468208545915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5405971032621957611394553 4054478274466468208545915)
            ·
              refine ⟨6081717411699702312818873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054478274466468208545915 6081717411699702312818873)
              ·
                refine ⟨4561288058774776734614155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081717411699702312818873 4561288058774776734614155)
                ·
                  refine ⟨6841932088162165101921233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561288058774776734614155 6841932088162165101921233)
                  ·
                    refine ⟨5131449066121623826440925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6841932088162165101921233 5131449066121623826440925)
                    ·
                      refine ⟨1924293399795608934915347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5131449066121623826440925 1924293399795608934915347)
                      ·
                        rfl

theorem cell23_3747548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_3747548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747548 prefixEnd_3747548 := by exact prefixLift 3747548
  have htrace : WordTrace (prefixWord ++ tailWord_3747548) baseStart_3747548 baseEnd_3747548 := by
    simpa [prefixWord, tailWord_3747548, baseEnd_3747548] using wordTrace_append hprefix tailTrace_3747548
  have hstable : (prefixWord ++ tailWord_3747548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747548).length < 2 ^ (prefixWord ++ tailWord_3747548).sum := by decide
  have hdescent : baseEnd_3747548 < baseStart_3747548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747607 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 7]
def baseStart_3747607 : Nat := 118140960795 + 3747607 * 2 ^ 59
def prefixEnd_3747607 : Nat := 4983230072969 + 3 ^ 40 * 3747607 * 2
def baseEnd_3747607 : Nat := 213813743906024911564175

theorem tailTrace_3747607 : CollatzResearch.WordTrace tailWord_3747607 prefixEnd_3747607 213813743906024911564175 := by
  unfold tailWord_3747607
  simp only [CollatzResearch.WordTrace]
  refine ⟨136686456534067354164497075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91124304356044902776331383 136686456534067354164497075)
  ·
    refine ⟨205029684801101031246745613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136686456534067354164497075 205029684801101031246745613)
    ·
      refine ⟨76886131800412886717529605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205029684801101031246745613 76886131800412886717529605)
      ·
        refine ⟨14416149712577416259536801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76886131800412886717529605 14416149712577416259536801)
        ·
          refine ⟨10812112284433062194652601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14416149712577416259536801 10812112284433062194652601)
          ·
            refine ⟨8109084213324796645989451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10812112284433062194652601 8109084213324796645989451)
            ·
              refine ⟨12163626319987194968984177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8109084213324796645989451 12163626319987194968984177)
              ·
                refine ⟨9122719739990396226738133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12163626319987194968984177 9122719739990396226738133)
                ·
                  refine ⟨213813743906024911564175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9122719739990396226738133 213813743906024911564175)
                  ·
                    rfl

theorem cell23_3747607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 7].length) (baseStart_3747607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747607 prefixEnd_3747607 := by exact prefixLift 3747607
  have htrace : WordTrace (prefixWord ++ tailWord_3747607) baseStart_3747607 baseEnd_3747607 := by
    simpa [prefixWord, tailWord_3747607, baseEnd_3747607] using wordTrace_append hprefix tailTrace_3747607
  have hstable : (prefixWord ++ tailWord_3747607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747607).length < 2 ^ (prefixWord ++ tailWord_3747607).sum := by decide
  have hdescent : baseEnd_3747607 < baseStart_3747607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747624 : List Nat := [2, 1, 5, 1, 1, 2, 1, 5, 5]
def baseStart_3747624 : Nat := 118140960795 + 3747624 * 2 ^ 59
def prefixEnd_3747624 : Nat := 4983230072969 + 3 ^ 40 * 3747624 * 2
def baseEnd_3747624 : Nat := 213814713813927848618333

theorem tailTrace_3747624 : CollatzResearch.WordTrace tailWord_3747624 prefixEnd_3747624 213814713813927848618333 := by
  unfold tailWord_3747624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68343538287502883033932963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91124717716670510711910617 68343538287502883033932963)
  ·
    refine ⟨102515307431254324550899445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68343538287502883033932963 102515307431254324550899445)
    ·
      refine ⟨9610810071680092926646823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102515307431254324550899445 9610810071680092926646823)
      ·
        refine ⟨14416215107520139389970235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9610810071680092926646823 14416215107520139389970235)
        ·
          refine ⟨21624322661280209084955353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14416215107520139389970235 21624322661280209084955353)
          ·
            refine ⟨16218241995960156813716515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21624322661280209084955353 16218241995960156813716515)
            ·
              refine ⟨24327362993940235220574773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16218241995960156813716515 24327362993940235220574773)
              ·
                refine ⟨2280690280681897051928885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24327362993940235220574773 2280690280681897051928885)
                ·
                  refine ⟨213814713813927848618333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2280690280681897051928885 213814713813927848618333)
                  ·
                    rfl

theorem cell23_3747624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5, 5].length) (baseStart_3747624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747624 prefixEnd_3747624 := by exact prefixLift 3747624
  have htrace : WordTrace (prefixWord ++ tailWord_3747624) baseStart_3747624 baseEnd_3747624 := by
    simpa [prefixWord, tailWord_3747624, baseEnd_3747624] using wordTrace_append hprefix tailTrace_3747624
  have hstable : (prefixWord ++ tailWord_3747624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747624).length < 2 ^ (prefixWord ++ tailWord_3747624).sum := by decide
  have hdescent : baseEnd_3747624 < baseStart_3747624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747635 : List Nat := [1, 1, 1, 2, 8, 1, 1, 2, 2, 2, 2]
def baseStart_3747635 : Nat := 118140960795 + 3747635 * 2 ^ 59
def prefixEnd_3747635 : Nat := 4983230072969 + 3 ^ 40 * 3747635 * 2
def baseEnd_3747635 : Nat := 1924338072612550094527447

theorem tailTrace_3747635 : CollatzResearch.WordTrace tailWord_3747635 prefixEnd_3747635 1924338072612550094527447 := by
  unfold tailWord_3747635
  simp only [CollatzResearch.WordTrace]
  refine ⟨136687477777965914946516359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91124985185310609964344239 136687477777965914946516359)
  ·
    refine ⟨205031216666948872419774539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136687477777965914946516359 205031216666948872419774539)
    ·
      refine ⟨307546825000423308629661809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205031216666948872419774539 307546825000423308629661809)
      ·
        refine ⟨230660118750317481472246357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307546825000423308629661809 230660118750317481472246357)
        ·
          refine ⟨2703048266605282986002887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 230660118750317481472246357 2703048266605282986002887)
          ·
            refine ⟨4054572399907924479004331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703048266605282986002887 4054572399907924479004331)
            ·
              refine ⟨6081858599861886718506497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4054572399907924479004331 6081858599861886718506497)
              ·
                refine ⟨4561393949896415038879873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6081858599861886718506497 4561393949896415038879873)
                ·
                  refine ⟨3421045462422311279159905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561393949896415038879873 3421045462422311279159905)
                  ·
                    refine ⟨2565784096816733459369929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421045462422311279159905 2565784096816733459369929)
                    ·
                      refine ⟨1924338072612550094527447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565784096816733459369929 1924338072612550094527447)
                      ·
                        rfl

theorem cell23_3747635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 2, 2, 2, 2].length) (baseStart_3747635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747635 prefixEnd_3747635 := by exact prefixLift 3747635
  have htrace : WordTrace (prefixWord ++ tailWord_3747635) baseStart_3747635 baseEnd_3747635 := by
    simpa [prefixWord, tailWord_3747635, baseEnd_3747635] using wordTrace_append hprefix tailTrace_3747635
  have hstable : (prefixWord ++ tailWord_3747635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747635).length < 2 ^ (prefixWord ++ tailWord_3747635).sum := by decide
  have hdescent : baseEnd_3747635 < baseStart_3747635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747697 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 6]
def baseStart_3747697 : Nat := 118140960795 + 3747697 * 2 ^ 59
def prefixEnd_3747697 : Nat := 4983230072969 + 3 ^ 40 * 3747697 * 2
def baseEnd_3747697 : Nat := 213818878712569872439129

theorem tailTrace_3747697 : CollatzResearch.WordTrace tailWord_3747697 prefixEnd_3747697 213818878712569872439129 := by
  unfold tailWord_3747697
  simp only [CollatzResearch.WordTrace]
  refine ⟨136689739103741299535273345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91126492735827533023515563 136689739103741299535273345)
  ·
    refine ⟨102517304327805974651455009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136689739103741299535273345 102517304327805974651455009)
    ·
      refine ⟨76887978245854480988591257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102517304327805974651455009 76887978245854480988591257)
      ·
        refine ⟨57665983684390860741443443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76887978245854480988591257 57665983684390860741443443)
        ·
          refine ⟨86498975526586291112165165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57665983684390860741443443 86498975526586291112165165)
          ·
            refine ⟨32437115822469859167061937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86498975526586291112165165 32437115822469859167061937)
            ·
              refine ⟨24327836866852394375296453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32437115822469859167061937 24327836866852394375296453)
              ·
                refine ⟨4561469412534823945368085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24327836866852394375296453 4561469412534823945368085)
                ·
                  refine ⟨213818878712569872439129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4561469412534823945368085 213818878712569872439129)
                  ·
                    rfl

theorem cell23_3747697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 6].length) (baseStart_3747697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747697 prefixEnd_3747697 := by exact prefixLift 3747697
  have htrace : WordTrace (prefixWord ++ tailWord_3747697) baseStart_3747697 baseEnd_3747697 := by
    simpa [prefixWord, tailWord_3747697, baseEnd_3747697] using wordTrace_append hprefix tailTrace_3747697
  have hstable : (prefixWord ++ tailWord_3747697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747697).length < 2 ^ (prefixWord ++ tailWord_3747697).sum := by decide
  have hdescent : baseEnd_3747697 < baseStart_3747697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747724 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 5, 1, 3]
def baseStart_3747724 : Nat := 118140960795 + 3747724 * 2 ^ 59
def prefixEnd_3747724 : Nat := 4983230072969 + 3 ^ 40 * 3747724 * 2
def baseEnd_3747724 : Nat := 1924383772390800246314537

theorem tailTrace_3747724 : CollatzResearch.WordTrace tailWord_3747724 prefixEnd_3747724 1924383772390800246314537 := by
  unfold tailWord_3747724
  simp only [CollatzResearch.WordTrace]
  refine ⟨68345361937321741573253113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91127149249762322097670817 68345361937321741573253113)
  ·
    refine ⟨51259021452991306179939835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68345361937321741573253113 51259021452991306179939835)
    ·
      refine ⟨76888532179486959269909753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51259021452991306179939835 76888532179486959269909753)
      ·
        refine ⟨57666399134615219452432315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76888532179486959269909753 57666399134615219452432315)
        ·
          refine ⟨86499598701922829178648473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57666399134615219452432315 86499598701922829178648473)
          ·
            refine ⟨64874699026442121883986355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86499598701922829178648473 64874699026442121883986355)
            ·
              refine ⟨97312048539663182825979533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64874699026442121883986355 97312048539663182825979533)
              ·
                refine ⟨36492018202373693559742325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97312048539663182825979533 36492018202373693559742325)
                ·
                  refine ⟨3421126706472533771225843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36492018202373693559742325 3421126706472533771225843)
                  ·
                    refine ⟨5131690059708800656838765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421126706472533771225843 5131690059708800656838765)
                    ·
                      refine ⟨1924383772390800246314537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5131690059708800656838765 1924383772390800246314537)
                      ·
                        rfl

theorem cell23_3747724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_3747724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747724 prefixEnd_3747724 := by exact prefixLift 3747724
  have htrace : WordTrace (prefixWord ++ tailWord_3747724) baseStart_3747724 baseEnd_3747724 := by
    simpa [prefixWord, tailWord_3747724, baseEnd_3747724] using wordTrace_append hprefix tailTrace_3747724
  have hstable : (prefixWord ++ tailWord_3747724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747724).length < 2 ^ (prefixWord ++ tailWord_3747724).sum := by decide
  have hdescent : baseEnd_3747724 < baseStart_3747724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747767 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_3747767 : Nat := 118140960795 + 3747767 * 2 ^ 59
def prefixEnd_3747767 : Nat := 4983230072969 + 3 ^ 40 * 3747767 * 2
def baseEnd_3747767 : Nat := 1924405852058943578076839

theorem tailTrace_3747767 : CollatzResearch.WordTrace tailWord_3747767 prefixEnd_3747767 1924405852058943578076839 := by
  unfold tailWord_3747767
  simp only [CollatzResearch.WordTrace]
  refine ⟨136692292213487701490321555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91128194808991800993547703 136692292213487701490321555)
  ·
    refine ⟨205038438320231552235482333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136692292213487701490321555 205038438320231552235482333)
    ·
      refine ⟨76889414370086832088305875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205038438320231552235482333 76889414370086832088305875)
      ·
        refine ⟨115334121555130248132458813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76889414370086832088305875 115334121555130248132458813)
        ·
          refine ⟨43250295583173843049672055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115334121555130248132458813 43250295583173843049672055)
          ·
            refine ⟨64875443374760764574508083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43250295583173843049672055 64875443374760764574508083)
            ·
              refine ⟨97313165062141146861762125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64875443374760764574508083 97313165062141146861762125)
              ·
                refine ⟨36492436898302930073160797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97313165062141146861762125 36492436898302930073160797)
                ·
                  refine ⟨13684663836863598777435299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36492436898302930073160797 13684663836863598777435299)
                  ·
                    refine ⟨20526995755295398166152949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13684663836863598777435299 20526995755295398166152949)
                    ·
                      refine ⟨1924405852058943578076839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20526995755295398166152949 1924405852058943578076839)
                      ·
                        rfl

theorem cell23_3747767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_3747767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747767 prefixEnd_3747767 := by exact prefixLift 3747767
  have htrace : WordTrace (prefixWord ++ tailWord_3747767) baseStart_3747767 baseEnd_3747767 := by
    simpa [prefixWord, tailWord_3747767, baseEnd_3747767] using wordTrace_append hprefix tailTrace_3747767
  have hstable : (prefixWord ++ tailWord_3747767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747767).length < 2 ^ (prefixWord ++ tailWord_3747767).sum := by decide
  have hdescent : baseEnd_3747767 < baseStart_3747767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747774 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_3747774 : Nat := 118140960795 + 3747774 * 2 ^ 59
def prefixEnd_3747774 : Nat := 4983230072969 + 3 ^ 40 * 3747774 * 2
def baseEnd_3747774 : Nat := 641469815474508350229769

theorem tailTrace_3747774 : CollatzResearch.WordTrace tailWord_3747774 prefixEnd_3747774 641469815474508350229769 := by
  unfold tailWord_3747774
  simp only [CollatzResearch.WordTrace]
  refine ⟨17086568440557792710728297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91128365016308227790550917 17086568440557792710728297)
  ·
    refine ⟨12814926330418344533046223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17086568440557792710728297 12814926330418344533046223)
    ·
      refine ⟨19222389495627516799569335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12814926330418344533046223 19222389495627516799569335)
      ·
        refine ⟨28833584243441275199354003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19222389495627516799569335 28833584243441275199354003)
        ·
          refine ⟨43250376365161912799031005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28833584243441275199354003 43250376365161912799031005)
          ·
            refine ⟨16218891136935717299636627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43250376365161912799031005 16218891136935717299636627)
            ·
              refine ⟨24328336705403575949454941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16218891136935717299636627 24328336705403575949454941)
              ·
                refine ⟨9123126264526340981045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24328336705403575949454941 9123126264526340981045603)
                ·
                  refine ⟨13684689396789511471568405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9123126264526340981045603 13684689396789511471568405)
                  ·
                    refine ⟨641469815474508350229769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13684689396789511471568405 641469815474508350229769)
                    ·
                      rfl

theorem cell23_3747774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_3747774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747774 prefixEnd_3747774 := by exact prefixLift 3747774
  have htrace : WordTrace (prefixWord ++ tailWord_3747774) baseStart_3747774 baseEnd_3747774 := by
    simpa [prefixWord, tailWord_3747774, baseEnd_3747774] using wordTrace_append hprefix tailTrace_3747774
  have hstable : (prefixWord ++ tailWord_3747774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747774).length < 2 ^ (prefixWord ++ tailWord_3747774).sum := by decide
  have hdescent : baseEnd_3747774 < baseStart_3747774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747815 : List Nat := [1, 1, 5, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_3747815 : Nat := 118140960795 + 3747815 * 2 ^ 59
def prefixEnd_3747815 : Nat := 4983230072969 + 3 ^ 40 * 3747815 * 2
def baseEnd_3747815 : Nat := 1924430499130359390276619

theorem tailTrace_3747815 : CollatzResearch.WordTrace tailWord_3747815 prefixEnd_3747815 1924430499130359390276619 := by
  unfold tailWord_3747815
  simp only [CollatzResearch.WordTrace]
  refine ⟨136694042917313805688068899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91129361944875870458712599 136694042917313805688068899)
  ·
    refine ⟨205041064375970708532103349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136694042917313805688068899 205041064375970708532103349)
    ·
      refine ⟨19222599785247253924884689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205041064375970708532103349 19222599785247253924884689)
      ·
        refine ⟨14416949838935440443663517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19222599785247253924884689 14416949838935440443663517)
        ·
          refine ⟨5406356189600790166373819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14416949838935440443663517 5406356189600790166373819)
          ·
            refine ⟨8109534284401185249560729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406356189600790166373819 8109534284401185249560729)
            ·
              refine ⟨6082150713300888937170547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8109534284401185249560729 6082150713300888937170547)
              ·
                refine ⟨9123226069951333405755821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082150713300888937170547 9123226069951333405755821)
                ·
                  refine ⟨3421209776231750027158433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9123226069951333405755821 3421209776231750027158433)
                  ·
                    refine ⟨2565907332173812520368825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421209776231750027158433 2565907332173812520368825)
                    ·
                      refine ⟨1924430499130359390276619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565907332173812520368825 1924430499130359390276619)
                      ·
                        rfl

theorem cell23_3747815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_3747815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747815 prefixEnd_3747815 := by exact prefixLift 3747815
  have htrace : WordTrace (prefixWord ++ tailWord_3747815) baseStart_3747815 baseEnd_3747815 := by
    simpa [prefixWord, tailWord_3747815, baseEnd_3747815] using wordTrace_append hprefix tailTrace_3747815
  have hstable : (prefixWord ++ tailWord_3747815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747815).length < 2 ^ (prefixWord ++ tailWord_3747815).sum := by decide
  have hdescent : baseEnd_3747815 < baseStart_3747815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747827 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5]
def baseStart_3747827 : Nat := 118140960795 + 3747827 * 2 ^ 59
def prefixEnd_3747827 : Nat := 4983230072969 + 3 ^ 40 * 3747827 * 2
def baseEnd_3747827 : Nat := 1924436660898213343326563

theorem tailTrace_3747827 : CollatzResearch.WordTrace tailWord_3747827 prefixEnd_3747827 1924436660898213343326563 := by
  unfold tailWord_3747827
  simp only [CollatzResearch.WordTrace]
  refine ⟨136694480593270331737505735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91129653728846887825003823 136694480593270331737505735)
  ·
    refine ⟨205041720889905497606258603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136694480593270331737505735 205041720889905497606258603)
    ·
      refine ⟨307562581334858246409387905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205041720889905497606258603 307562581334858246409387905)
      ·
        refine ⟨230671936001143684807040929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307562581334858246409387905 230671936001143684807040929)
        ·
          refine ⟨173003952000857763605280697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230671936001143684807040929 173003952000857763605280697)
          ·
            refine ⟨129752964000643322703960523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173003952000857763605280697 129752964000643322703960523)
            ·
              refine ⟨194629446000964984055940785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129752964000643322703960523 194629446000964984055940785)
              ·
                refine ⟨145972084500723738041955589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 194629446000964984055940785 145972084500723738041955589)
                ·
                  refine ⟨27369765843885700882866673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 145972084500723738041955589 27369765843885700882866673)
                  ·
                    refine ⟨20527324382914275662150005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27369765843885700882866673 20527324382914275662150005)
                    ·
                      refine ⟨1924436660898213343326563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20527324382914275662150005 1924436660898213343326563)
                      ·
                        rfl

theorem cell23_3747827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 5].length) (baseStart_3747827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747827 prefixEnd_3747827 := by exact prefixLift 3747827
  have htrace : WordTrace (prefixWord ++ tailWord_3747827) baseStart_3747827 baseEnd_3747827 := by
    simpa [prefixWord, tailWord_3747827, baseEnd_3747827] using wordTrace_append hprefix tailTrace_3747827
  have hstable : (prefixWord ++ tailWord_3747827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747827).length < 2 ^ (prefixWord ++ tailWord_3747827).sum := by decide
  have hdescent : baseEnd_3747827 < baseStart_3747827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747838 : List Nat := [4, 2, 2, 2, 1, 3, 2, 7]
def baseStart_3747838 : Nat := 118140960795 + 3747838 * 2 ^ 59
def prefixEnd_3747838 : Nat := 4983230072969 + 3 ^ 40 * 3747838 * 2
def baseEnd_3747838 : Nat := 71275641080941214825519

theorem tailTrace_3747838 : CollatzResearch.WordTrace tailWord_3747838 prefixEnd_3747838 71275641080941214825519 := by
  unfold tailWord_3747838
  simp only [CollatzResearch.WordTrace]
  refine ⟨17086860224528810077019521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91129921197486987077437445 17086860224528810077019521)
  ·
    refine ⟨12815145168396607557764641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17086860224528810077019521 12815145168396607557764641)
    ·
      refine ⟨9611358876297455668323481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12815145168396607557764641 9611358876297455668323481)
      ·
        refine ⟨7208519157223091751242611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9611358876297455668323481 7208519157223091751242611)
        ·
          refine ⟨10812778735834637626863917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7208519157223091751242611 10812778735834637626863917)
          ·
            refine ⟨4054792025937989110073969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10812778735834637626863917 4054792025937989110073969)
            ·
              refine ⟨3041094019453491832555477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4054792025937989110073969 3041094019453491832555477)
              ·
                refine ⟨71275641080941214825519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3041094019453491832555477 71275641080941214825519)
                ·
                  rfl

theorem cell23_3747838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 7].length) (baseStart_3747838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747838 prefixEnd_3747838 := by exact prefixLift 3747838
  have htrace : WordTrace (prefixWord ++ tailWord_3747838) baseStart_3747838 baseEnd_3747838 := by
    simpa [prefixWord, tailWord_3747838, baseEnd_3747838] using wordTrace_append hprefix tailTrace_3747838
  have hstable : (prefixWord ++ tailWord_3747838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747838).length < 2 ^ (prefixWord ++ tailWord_3747838).sum := by decide
  have hdescent : baseEnd_3747838 < baseStart_3747838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747867 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6]
def baseStart_3747867 : Nat := 118140960795 + 3747867 * 2 ^ 59
def prefixEnd_3747867 : Nat := 4983230072969 + 3 ^ 40 * 3747867 * 2
def baseEnd_3747867 : Nat := 1924457200124393186826379

theorem tailTrace_3747867 : CollatzResearch.WordTrace tailWord_3747867 prefixEnd_3747867 1924457200124393186826379 := by
  unfold tailWord_3747867
  simp only [CollatzResearch.WordTrace]
  refine ⟨136695939513125418568961855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91130626342083612379307903 136695939513125418568961855)
  ·
    refine ⟨205043909269688127853442783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136695939513125418568961855 205043909269688127853442783)
    ·
      refine ⟨307565863904532191780164175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205043909269688127853442783 307565863904532191780164175)
      ·
        refine ⟨461348795856798287670246263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307565863904532191780164175 461348795856798287670246263)
        ·
          refine ⟨692023193785197431505369395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 461348795856798287670246263 692023193785197431505369395)
          ·
            refine ⟨1038034790677796147258054093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 692023193785197431505369395 1038034790677796147258054093)
            ·
              refine ⟨389263046504173555221770285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1038034790677796147258054093 389263046504173555221770285)
              ·
                refine ⟨145973642439065083208163857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 389263046504173555221770285 145973642439065083208163857)
                ·
                  refine ⟨109480231829298812406122893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 145973642439065083208163857 109480231829298812406122893)
                  ·
                    refine ⟨41055086935987054652296085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 109480231829298812406122893 41055086935987054652296085)
                    ·
                      refine ⟨1924457200124393186826379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41055086935987054652296085 1924457200124393186826379)
                      ·
                        rfl

theorem cell23_3747867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 6].length) (baseStart_3747867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747867 prefixEnd_3747867 := by exact prefixLift 3747867
  have htrace : WordTrace (prefixWord ++ tailWord_3747867) baseStart_3747867 baseEnd_3747867 := by
    simpa [prefixWord, tailWord_3747867, baseEnd_3747867] using wordTrace_append hprefix tailTrace_3747867
  have hstable : (prefixWord ++ tailWord_3747867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747867).length < 2 ^ (prefixWord ++ tailWord_3747867).sum := by decide
  have hdescent : baseEnd_3747867 < baseStart_3747867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747874 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 1, 3, 5]
def baseStart_3747874 : Nat := 118140960795 + 3747874 * 2 ^ 59
def prefixEnd_3747874 : Nat := 4983230072969 + 3 ^ 40 * 3747874 * 2
def baseEnd_3747874 : Nat := 1924460794488974659438847

theorem tailTrace_3747874 : CollatzResearch.WordTrace tailWord_3747874 prefixEnd_3747874 1924460794488974659438847 := by
  unfold tailWord_3747874
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174048706025014691116669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91130796549400039176311117 34174048706025014691116669)
  ·
    refine ⟨12815268264759380509168751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34174048706025014691116669 12815268264759380509168751)
    ·
      refine ⟨19222902397139070763753127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12815268264759380509168751 19222902397139070763753127)
      ·
        refine ⟨28834353595708606145629691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19222902397139070763753127 28834353595708606145629691)
        ·
          refine ⟨43251530393562909218444537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28834353595708606145629691 43251530393562909218444537)
          ·
            refine ⟨32438647795172181913833403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43251530393562909218444537 32438647795172181913833403)
            ·
              refine ⟨48657971692758272870750105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32438647795172181913833403 48657971692758272870750105)
              ·
                refine ⟨36493478769568704653062579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48657971692758272870750105 36493478769568704653062579)
                ·
                  refine ⟨54740218154353056979593869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36493478769568704653062579 54740218154353056979593869)
                  ·
                    refine ⟨20527581807882396367347701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54740218154353056979593869 20527581807882396367347701)
                    ·
                      refine ⟨1924460794488974659438847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20527581807882396367347701 1924460794488974659438847)
                      ·
                        rfl

theorem cell23_3747874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_3747874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747874 prefixEnd_3747874 := by exact prefixLift 3747874
  have htrace : WordTrace (prefixWord ++ tailWord_3747874) baseStart_3747874 baseEnd_3747874 := by
    simpa [prefixWord, tailWord_3747874, baseEnd_3747874] using wordTrace_append hprefix tailTrace_3747874
  have hstable : (prefixWord ++ tailWord_3747874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747874).length < 2 ^ (prefixWord ++ tailWord_3747874).sum := by decide
  have hdescent : baseEnd_3747874 < baseStart_3747874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747882 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_3747882 : Nat := 118140960795 + 3747882 * 2 ^ 59
def prefixEnd_3747882 : Nat := 4983230072969 + 3 ^ 40 * 3747882 * 2
def baseEnd_3747882 : Nat := 1924464902334210628138811

theorem tailTrace_3747882 : CollatzResearch.WordTrace tailWord_3747882 prefixEnd_3747882 1924464902334210628138811 := by
  unfold tailWord_3747882
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174121652017769032689475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91130991072047384087171933 34174121652017769032689475)
  ·
    refine ⟨51261182478026653549034213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34174121652017769032689475 51261182478026653549034213)
    ·
      refine ⟨9611471714629997540443915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51261182478026653549034213 9611471714629997540443915)
      ·
        refine ⟨14417207571944996310665873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9611471714629997540443915 14417207571944996310665873)
        ·
          refine ⟨10812905678958747232999405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14417207571944996310665873 10812905678958747232999405)
          ·
            refine ⟨4054839629609530212374777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10812905678958747232999405 4054839629609530212374777)
            ·
              refine ⟨3041129722207147659281083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4054839629609530212374777 3041129722207147659281083)
              ·
                refine ⟨4561694583310721488921625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041129722207147659281083 4561694583310721488921625)
                ·
                  refine ⟨3421270937483041116691219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561694583310721488921625 3421270937483041116691219)
                  ·
                    refine ⟨5131906406224561675036829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421270937483041116691219 5131906406224561675036829)
                    ·
                      refine ⟨1924464902334210628138811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5131906406224561675036829 1924464902334210628138811)
                      ·
                        rfl

theorem cell23_3747882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_3747882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747882 prefixEnd_3747882 := by exact prefixLift 3747882
  have htrace : WordTrace (prefixWord ++ tailWord_3747882) baseStart_3747882 baseEnd_3747882 := by
    simpa [prefixWord, tailWord_3747882, baseEnd_3747882] using wordTrace_append hprefix tailTrace_3747882
  have hstable : (prefixWord ++ tailWord_3747882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747882).length < 2 ^ (prefixWord ++ tailWord_3747882).sum := by decide
  have hdescent : baseEnd_3747882 < baseStart_3747882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747911 : List Nat := [1, 1, 4, 1, 3, 1, 2, 5, 5]
def baseStart_3747911 : Nat := 118140960795 + 3747911 * 2 ^ 59
def prefixEnd_3747911 : Nat := 4983230072969 + 3 ^ 40 * 3747911 * 2
def baseEnd_3747911 : Nat := 213831088141465668297353

theorem tailTrace_3747911 : CollatzResearch.WordTrace tailWord_3747911 prefixEnd_3747911 213831088141465668297353 := by
  unfold tailWord_3747911
  simp only [CollatzResearch.WordTrace]
  refine ⟨136697544324966014083563587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91131696216644009389042391 136697544324966014083563587)
  ·
    refine ⟨205046316487449021125345381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136697544324966014083563587 205046316487449021125345381)
    ·
      refine ⟨38446184341396691461002259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205046316487449021125345381 38446184341396691461002259)
      ·
        refine ⟨57669276512095037191503389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38446184341396691461002259 57669276512095037191503389)
        ·
          refine ⟨21625978692035638946813771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57669276512095037191503389 21625978692035638946813771)
          ·
            refine ⟨32438968038053458420220657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21625978692035638946813771 32438968038053458420220657)
            ·
              refine ⟨24329226028540093815165493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32438968038053458420220657 24329226028540093815165493)
              ·
                refine ⟨2280864940175633795171765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24329226028540093815165493 2280864940175633795171765)
                ·
                  refine ⟨213831088141465668297353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2280864940175633795171765 213831088141465668297353)
                  ·
                    rfl

theorem cell23_3747911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 5, 5].length) (baseStart_3747911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747911 prefixEnd_3747911 := by exact prefixLift 3747911
  have htrace : WordTrace (prefixWord ++ tailWord_3747911) baseStart_3747911 baseEnd_3747911 := by
    simpa [prefixWord, tailWord_3747911, baseEnd_3747911] using wordTrace_append hprefix tailTrace_3747911
  have hstable : (prefixWord ++ tailWord_3747911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747911).length < 2 ^ (prefixWord ++ tailWord_3747911).sum := by decide
  have hdescent : baseEnd_3747911 < baseStart_3747911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747922 : List Nat := [3, 2, 2, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_3747922 : Nat := 118140960795 + 3747922 * 2 ^ 59
def prefixEnd_3747922 : Nat := 4983230072969 + 3 ^ 40 * 3747922 * 2
def baseEnd_3747922 : Nat := 1924485441560390471638627

theorem tailTrace_3747922 : CollatzResearch.WordTrace tailWord_3747922 prefixEnd_3747922 1924485441560390471638627 := by
  unfold tailWord_3747922
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174486381981540740553505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91131963685284108641476013 34174486381981540740553505)
  ·
    refine ⟨25630864786486155555415129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34174486381981540740553505 25630864786486155555415129)
    ·
      refine ⟨19223148589864616666561347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25630864786486155555415129 19223148589864616666561347)
      ·
        refine ⟨28834722884796924999842021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19223148589864616666561347 28834722884796924999842021)
        ·
          refine ⟨5406510540899423437470379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28834722884796924999842021 5406510540899423437470379)
          ·
            refine ⟨8109765811349135156205569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406510540899423437470379 8109765811349135156205569)
            ·
              refine ⟨6082324358511851367154177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8109765811349135156205569 6082324358511851367154177)
              ·
                refine ⟨4561743268883888525365633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6082324358511851367154177 4561743268883888525365633)
                ·
                  refine ⟨3421307451662916394024225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561743268883888525365633 3421307451662916394024225)
                  ·
                    refine ⟨2565980588747187295518169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421307451662916394024225 2565980588747187295518169)
                    ·
                      refine ⟨1924485441560390471638627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2565980588747187295518169 1924485441560390471638627)
                      ·
                        rfl

theorem cell23_3747922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_3747922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747922 prefixEnd_3747922 := by exact prefixLift 3747922
  have htrace : WordTrace (prefixWord ++ tailWord_3747922) baseStart_3747922 baseEnd_3747922 := by
    simpa [prefixWord, tailWord_3747922, baseEnd_3747922] using wordTrace_append hprefix tailTrace_3747922
  have hstable : (prefixWord ++ tailWord_3747922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747922).length < 2 ^ (prefixWord ++ tailWord_3747922).sum := by decide
  have hdescent : baseEnd_3747922 < baseStart_3747922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747924 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_3747924 : Nat := 118140960795 + 3747924 * 2 ^ 59
def prefixEnd_3747924 : Nat := 4983230072969 + 3 ^ 40 * 3747924 * 2
def baseEnd_3747924 : Nat := 641495489507233154604539

theorem tailTrace_3747924 : CollatzResearch.WordTrace tailWord_3747924 prefixEnd_3747924 641495489507233154604539 := by
  unfold tailWord_3747924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68349009236959458651893413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91132012315945944869191217 68349009236959458651893413)
  ·
    refine ⟨12815439231929898497230015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68349009236959458651893413 12815439231929898497230015)
    ·
      refine ⟨19223158847894847745845023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12815439231929898497230015 19223158847894847745845023)
      ·
        refine ⟨28834738271842271618767535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19223158847894847745845023 28834738271842271618767535)
        ·
          refine ⟨43252107407763407428151303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28834738271842271618767535 43252107407763407428151303)
          ·
            refine ⟨64878161111645111142226955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43252107407763407428151303 64878161111645111142226955)
            ·
              refine ⟨97317241667467666713340433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64878161111645111142226955 97317241667467666713340433)
              ·
                refine ⟨72987931250600750035005325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97317241667467666713340433 72987931250600750035005325)
                ·
                  refine ⟨27370474218975281263126997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72987931250600750035005325 27370474218975281263126997)
                  ·
                    refine ⟨641495489507233154604539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 27370474218975281263126997 641495489507233154604539)
                    ·
                      rfl

theorem cell23_3747924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_3747924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747924 prefixEnd_3747924 := by exact prefixLift 3747924
  have htrace : WordTrace (prefixWord ++ tailWord_3747924) baseStart_3747924 baseEnd_3747924 := by
    simpa [prefixWord, tailWord_3747924, baseEnd_3747924] using wordTrace_append hprefix tailTrace_3747924
  have hstable : (prefixWord ++ tailWord_3747924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747924).length < 2 ^ (prefixWord ++ tailWord_3747924).sum := by decide
  have hdescent : baseEnd_3747924 < baseStart_3747924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747928 : List Nat := [2, 1, 2, 2, 1, 4, 4, 2, 5]
def baseStart_3747928 : Nat := 118140960795 + 3747928 * 2 ^ 59
def prefixEnd_3747928 : Nat := 4983230072969 + 3 ^ 40 * 3747928 * 2
def baseEnd_3747928 : Nat := 213832058049368605351511

theorem tailTrace_3747928 : CollatzResearch.WordTrace tailWord_3747928 prefixEnd_3747928 213832058049368605351511 := by
  unfold tailWord_3747928
  simp only [CollatzResearch.WordTrace]
  refine ⟨68349082182952212993466219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91132109577269617324621625 68349082182952212993466219)
  ·
    refine ⟨102523623274428319490199329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68349082182952212993466219 102523623274428319490199329)
    ·
      refine ⟨76892717455821239617649497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102523623274428319490199329 76892717455821239617649497)
      ·
        refine ⟨57669538091865929713237123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76892717455821239617649497 57669538091865929713237123)
        ·
          refine ⟨86504307137798894569855685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57669538091865929713237123 86504307137798894569855685)
          ·
            refine ⟨16219557588337292731847941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86504307137798894569855685 16219557588337292731847941)
            ·
              refine ⟨3041167047813242387221489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16219557588337292731847941 3041167047813242387221489)
              ·
                refine ⟨2280875285859931790416117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041167047813242387221489 2280875285859931790416117)
                ·
                  refine ⟨213832058049368605351511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2280875285859931790416117 213832058049368605351511)
                  ·
                    rfl

theorem cell23_3747928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 5].length) (baseStart_3747928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747928 prefixEnd_3747928 := by exact prefixLift 3747928
  have htrace : WordTrace (prefixWord ++ tailWord_3747928) baseStart_3747928 baseEnd_3747928 := by
    simpa [prefixWord, tailWord_3747928, baseEnd_3747928] using wordTrace_append hprefix tailTrace_3747928
  have hstable : (prefixWord ++ tailWord_3747928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747928).length < 2 ^ (prefixWord ++ tailWord_3747928).sum := by decide
  have hdescent : baseEnd_3747928 < baseStart_3747928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747958 : List Nat := [5, 1, 1, 2, 1, 2, 3, 1, 2, 5]
def baseStart_3747958 : Nat := 118140960795 + 3747958 * 2 ^ 59
def prefixEnd_3747958 : Nat := 4983230072969 + 3 ^ 40 * 3747958 * 2
def baseEnd_3747958 : Nat := 641501308954650776929487

theorem tailTrace_3747958 : CollatzResearch.WordTrace tailWord_3747958 prefixEnd_3747958 641501308954650776929487 := by
  unfold tailWord_3747958
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543703659737233819407783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91132839037197160740349685 8543703659737233819407783)
  ·
    refine ⟨12815555489605850729111675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8543703659737233819407783 12815555489605850729111675)
    ·
      refine ⟨19223333234408776093667513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12815555489605850729111675 19223333234408776093667513)
      ·
        refine ⟨14417499925806582070250635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19223333234408776093667513 14417499925806582070250635)
        ·
          refine ⟨21626249888709873105375953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14417499925806582070250635 21626249888709873105375953)
          ·
            refine ⟨16219687416532404829031965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21626249888709873105375953 16219687416532404829031965)
            ·
              refine ⟨6082382781199651810886987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16219687416532404829031965 6082382781199651810886987)
              ·
                refine ⟨9123574171799477716330481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082382781199651810886987 9123574171799477716330481)
                ·
                  refine ⟨6842680628849608287247861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9123574171799477716330481 6842680628849608287247861)
                  ·
                    refine ⟨641501308954650776929487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6842680628849608287247861 641501308954650776929487)
                    ·
                      rfl

theorem cell23_3747958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_3747958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747958 prefixEnd_3747958 := by exact prefixLift 3747958
  have htrace : WordTrace (prefixWord ++ tailWord_3747958) baseStart_3747958 baseEnd_3747958 := by
    simpa [prefixWord, tailWord_3747958, baseEnd_3747958] using wordTrace_append hprefix tailTrace_3747958
  have hstable : (prefixWord ++ tailWord_3747958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747958).length < 2 ^ (prefixWord ++ tailWord_3747958).sum := by decide
  have hdescent : baseEnd_3747958 < baseStart_3747958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747961 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3747961 : Nat := 118140960795 + 3747961 * 2 ^ 59
def prefixEnd_3747961 : Nat := 4983230072969 + 3 ^ 40 * 3747961 * 2
def baseEnd_3747961 : Nat := 1924505467305915819050947

theorem tailTrace_3747961 : CollatzResearch.WordTrace tailWord_3747961 prefixEnd_3747961 1924505467305915819050947 := by
  unfold tailWord_3747961
  simp only [CollatzResearch.WordTrace]
  refine ⟨136699367974784872622883737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91132911983189915081922491 136699367974784872622883737)
  ·
    refine ⟨102524525981088654467162803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136699367974784872622883737 102524525981088654467162803)
    ·
      refine ⟨153786788971632981700744205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102524525981088654467162803 153786788971632981700744205)
      ·
        refine ⟨57670045864362368137779077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153786788971632981700744205 57670045864362368137779077)
        ·
          refine ⟨10813133599567944025833577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57670045864362368137779077 10813133599567944025833577)
          ·
            refine ⟨8109850199675958019375183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10813133599567944025833577 8109850199675958019375183)
            ·
              refine ⟨12164775299513937029062775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8109850199675958019375183 12164775299513937029062775)
              ·
                refine ⟨18247162949270905543594163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12164775299513937029062775 18247162949270905543594163)
                ·
                  refine ⟨27370744423906358315391245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18247162949270905543594163 27370744423906358315391245)
                  ·
                    refine ⟨10264029158964884368271717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27370744423906358315391245 10264029158964884368271717)
                    ·
                      refine ⟨1924505467305915819050947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10264029158964884368271717 1924505467305915819050947)
                      ·
                        rfl

theorem cell23_3747961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3747961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747961 prefixEnd_3747961 := by exact prefixLift 3747961
  have htrace : WordTrace (prefixWord ++ tailWord_3747961) baseStart_3747961 baseEnd_3747961 := by
    simpa [prefixWord, tailWord_3747961, baseEnd_3747961] using wordTrace_append hprefix tailTrace_3747961
  have hstable : (prefixWord ++ tailWord_3747961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747961).length < 2 ^ (prefixWord ++ tailWord_3747961).sum := by decide
  have hdescent : baseEnd_3747961 < baseStart_3747961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747978 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2]
def baseStart_3747978 : Nat := 118140960795 + 3747978 * 2 ^ 59
def prefixEnd_3747978 : Nat := 4983230072969 + 3 ^ 40 * 3747978 * 2
def baseEnd_3747978 : Nat := 1924514196477042252538369

theorem tailTrace_3747978 : CollatzResearch.WordTrace tailWord_3747978 prefixEnd_3747978 1924514196477042252538369 := by
  unfold tailWord_3747978
  simp only [CollatzResearch.WordTrace]
  refine ⟨34174997003930821131563147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91133325343815523017501725 34174997003930821131563147)
  ·
    refine ⟨51262495505896231697344721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34174997003930821131563147 51262495505896231697344721)
    ·
      refine ⟨38446871629422173773008541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51262495505896231697344721 38446871629422173773008541)
      ·
        refine ⟨14417576861033315164878203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38446871629422173773008541 14417576861033315164878203)
        ·
          refine ⟨21626365291549972747317305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14417576861033315164878203 21626365291549972747317305)
          ·
            refine ⟨16219773968662479560487979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21626365291549972747317305 16219773968662479560487979)
            ·
              refine ⟨24329660952993719340731969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16219773968662479560487979 24329660952993719340731969)
              ·
                refine ⟨18247245714745289505548977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24329660952993719340731969 18247245714745289505548977)
                ·
                  refine ⟨13685434286058967129161733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18247245714745289505548977 13685434286058967129161733)
                  ·
                    refine ⟨2566018928636056336717825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13685434286058967129161733 2566018928636056336717825)
                    ·
                      refine ⟨1924514196477042252538369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566018928636056336717825 1924514196477042252538369)
                      ·
                        rfl

theorem cell23_3747978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_3747978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747978 prefixEnd_3747978 := by exact prefixLift 3747978
  have htrace : WordTrace (prefixWord ++ tailWord_3747978) baseStart_3747978 baseEnd_3747978 := by
    simpa [prefixWord, tailWord_3747978, baseEnd_3747978] using wordTrace_append hprefix tailTrace_3747978
  have hstable : (prefixWord ++ tailWord_3747978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747978).length < 2 ^ (prefixWord ++ tailWord_3747978).sum := by decide
  have hdescent : baseEnd_3747978 < baseStart_3747978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747984 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 8]
def baseStart_3747984 : Nat := 118140960795 + 3747984 * 2 ^ 59
def prefixEnd_3747984 : Nat := 4983230072969 + 3 ^ 40 * 3747984 * 2
def baseEnd_3747984 : Nat := 213835253040107692118149

theorem tailTrace_3747984 : CollatzResearch.WordTrace tailWord_3747984 prefixEnd_3747984 213835253040107692118149 := by
  unfold tailWord_3747984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68350103426850773775485503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91133471235801031700647337 68350103426850773775485503)
  ·
    refine ⟨102525155140276160663228255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68350103426850773775485503 102525155140276160663228255)
    ·
      refine ⟨153787732710414240994842383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102525155140276160663228255 153787732710414240994842383)
      ·
        refine ⟨230681599065621361492263575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153787732710414240994842383 230681599065621361492263575)
        ·
          refine ⟨346022398598432042238395363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230681599065621361492263575 346022398598432042238395363)
          ·
            refine ⟨519033597897648063357593045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346022398598432042238395363 519033597897648063357593045)
            ·
              refine ⟨12164849950726126484943587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 519033597897648063357593045 12164849950726126484943587)
              ·
                refine ⟨18247274926089189727415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12164849950726126484943587 18247274926089189727415381)
                ·
                  refine ⟨213835253040107692118149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18247274926089189727415381 213835253040107692118149)
                  ·
                    rfl

theorem cell23_3747984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 8].length) (baseStart_3747984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747984 prefixEnd_3747984 := by exact prefixLift 3747984
  have htrace : WordTrace (prefixWord ++ tailWord_3747984) baseStart_3747984 baseEnd_3747984 := by
    simpa [prefixWord, tailWord_3747984, baseEnd_3747984] using wordTrace_append hprefix tailTrace_3747984
  have hstable : (prefixWord ++ tailWord_3747984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747984).length < 2 ^ (prefixWord ++ tailWord_3747984).sum := by decide
  have hdescent : baseEnd_3747984 < baseStart_3747984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3747990 : List Nat := [5, 3, 2, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3747990 : Nat := 118140960795 + 3747990 * 2 ^ 59
def prefixEnd_3747990 : Nat := 4983230072969 + 3 ^ 40 * 3747990 * 2
def baseEnd_3747990 : Nat := 1924520358244896205588315

theorem tailTrace_3747990 : CollatzResearch.WordTrace tailWord_3747990 prefixEnd_3747990 1924520358244896205588315 := by
  unfold tailWord_3747990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8543776605729988160980589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91133617127786540383792949 8543776605729988160980589)
  ·
    refine ⟨3203916227148745560367721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8543776605729988160980589 3203916227148745560367721)
    ·
      refine ⟨2402937170361559170275791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3203916227148745560367721 2402937170361559170275791)
      ·
        refine ⟨3604405755542338755413687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402937170361559170275791 3604405755542338755413687)
        ·
          refine ⟨5406608633313508133120531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604405755542338755413687 5406608633313508133120531)
          ·
            refine ⟨8109912949970262199680797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406608633313508133120531 8109912949970262199680797)
            ·
              refine ⟨3041217356238848324880299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8109912949970262199680797 3041217356238848324880299)
              ·
                refine ⟨4561826034358272487320449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041217356238848324880299 4561826034358272487320449)
                ·
                  refine ⟨3421369525768704365490337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4561826034358272487320449 3421369525768704365490337)
                  ·
                    refine ⟨2566027144326528274117753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421369525768704365490337 2566027144326528274117753)
                    ·
                      refine ⟨1924520358244896205588315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566027144326528274117753 1924520358244896205588315)
                      ·
                        rfl

theorem cell23_3747990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3747990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3747990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3747990 prefixEnd_3747990 := by exact prefixLift 3747990
  have htrace : WordTrace (prefixWord ++ tailWord_3747990) baseStart_3747990 baseEnd_3747990 := by
    simpa [prefixWord, tailWord_3747990, baseEnd_3747990] using wordTrace_append hprefix tailTrace_3747990
  have hstable : (prefixWord ++ tailWord_3747990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3747990).length < 2 ^ (prefixWord ++ tailWord_3747990).sum := by decide
  have hdescent : baseEnd_3747990 < baseStart_3747990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3747990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748081 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 4]
def baseStart_3748081 : Nat := 118140960795 + 3748081 * 2 ^ 59
def prefixEnd_3748081 : Nat := 4983230072969 + 3 ^ 40 * 3748081 * 2
def baseEnd_3748081 : Nat := 1924567084984455349550395

theorem tailTrace_3748081 : CollatzResearch.WordTrace tailWord_3748081 prefixEnd_3748081 1924567084984455349550395 := by
  unfold tailWord_3748081
  simp only [CollatzResearch.WordTrace]
  refine ⟨136703744734350133117252097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91135829822900088744834731 136703744734350133117252097)
  ·
    refine ⟨102527808550762599837939073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136703744734350133117252097 102527808550762599837939073)
    ·
      refine ⟨76895856413071949878454305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102527808550762599837939073 76895856413071949878454305)
      ·
        refine ⟨57671892309803962408840729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76895856413071949878454305 57671892309803962408840729)
        ·
          refine ⟨43253919232352971806630547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57671892309803962408840729 43253919232352971806630547)
          ·
            refine ⟨64880878848529457709945821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43253919232352971806630547 64880878848529457709945821)
            ·
              refine ⟨24330329568198546641229683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64880878848529457709945821 24330329568198546641229683)
              ·
                refine ⟨36495494352297819961844525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24330329568198546641229683 36495494352297819961844525)
                ·
                  refine ⟨13685810382111682485691697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36495494352297819961844525 13685810382111682485691697)
                  ·
                    refine ⟨10264357786583761864268773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13685810382111682485691697 10264357786583761864268773)
                    ·
                      refine ⟨1924567084984455349550395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10264357786583761864268773 1924567084984455349550395)
                      ·
                        rfl

theorem cell23_3748081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_3748081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748081 prefixEnd_3748081 := by exact prefixLift 3748081
  have htrace : WordTrace (prefixWord ++ tailWord_3748081) baseStart_3748081 baseEnd_3748081 := by
    simpa [prefixWord, tailWord_3748081, baseEnd_3748081] using wordTrace_append hprefix tailTrace_3748081
  have hstable : (prefixWord ++ tailWord_3748081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748081).length < 2 ^ (prefixWord ++ tailWord_3748081).sum := by decide
  have hdescent : baseEnd_3748081 < baseStart_3748081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748088 : List Nat := [2, 1, 2, 1, 1, 2, 1, 7, 1, 2, 3]
def baseStart_3748088 : Nat := 118140960795 + 3748088 * 2 ^ 59
def prefixEnd_3748088 : Nat := 4983230072969 + 3 ^ 40 * 3748088 * 2
def baseEnd_3748088 : Nat := 1924570679349036822162863

theorem tailTrace_3748088 : CollatzResearch.WordTrace tailWord_3748088 prefixEnd_3748088 1924570679349036822162863 := by
  unfold tailWord_3748088
  simp only [CollatzResearch.WordTrace]
  refine ⟨68352000022662386656378459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91136000030216515541837945 68352000022662386656378459)
  ·
    refine ⟨102528000033993579984567689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68352000022662386656378459 102528000033993579984567689)
    ·
      refine ⟨76896000025495184988425767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102528000033993579984567689 76896000025495184988425767)
      ·
        refine ⟨115344000038242777482638651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76896000025495184988425767 115344000038242777482638651)
        ·
          refine ⟨173016000057364166223957977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115344000038242777482638651 173016000057364166223957977)
          ·
            refine ⟨129762000043023124667968483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173016000057364166223957977 129762000043023124667968483)
            ·
              refine ⟨194643000064534687001952725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129762000043023124667968483 194643000064534687001952725)
              ·
                refine ⟨4561945314012531726608267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 194643000064534687001952725 4561945314012531726608267)
                ·
                  refine ⟨6842917971018797589912401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4561945314012531726608267 6842917971018797589912401)
                  ·
                    refine ⟨5132188478264098192434301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6842917971018797589912401 5132188478264098192434301)
                    ·
                      refine ⟨1924570679349036822162863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132188478264098192434301 1924570679349036822162863)
                      ·
                        rfl

theorem cell23_3748088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 2, 3].length) (baseStart_3748088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748088 prefixEnd_3748088 := by exact prefixLift 3748088
  have htrace : WordTrace (prefixWord ++ tailWord_3748088) baseStart_3748088 baseEnd_3748088 := by
    simpa [prefixWord, tailWord_3748088, baseEnd_3748088] using wordTrace_append hprefix tailTrace_3748088
  have hstable : (prefixWord ++ tailWord_3748088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748088).length < 2 ^ (prefixWord ++ tailWord_3748088).sum := by decide
  have hdescent : baseEnd_3748088 < baseStart_3748088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748125 : List Nat := [1, 4, 2, 3, 2, 1, 3, 7]
def baseStart_3748125 : Nat := 118140960795 + 3748125 * 2 ^ 59
def prefixEnd_3748125 : Nat := 4983230072969 + 3 ^ 40 * 3748125 * 2
def baseEnd_3748125 : Nat := 71281099190120488051859

theorem tailTrace_3748125 : CollatzResearch.WordTrace tailWord_3748125 prefixEnd_3748125 71281099190120488051859 := by
  unfold tailWord_3748125
  simp only [CollatzResearch.WordTrace]
  refine ⟨136705349546190728631853829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91136899697460485754569219 136705349546190728631853829)
  ·
    refine ⟨25632253039910761618472593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 136705349546190728631853829 25632253039910761618472593)
    ·
      refine ⟨19224189779933071213854445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25632253039910761618472593 19224189779933071213854445)
      ·
        refine ⟨7209071167474901705195417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19224189779933071213854445 7209071167474901705195417)
        ·
          refine ⟨5406803375606176278896563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7209071167474901705195417 5406803375606176278896563)
          ·
            refine ⟨8110205063409264418344845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406803375606176278896563 8110205063409264418344845)
            ·
              refine ⟨3041326898778474156879317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8110205063409264418344845 3041326898778474156879317)
              ·
                refine ⟨71281099190120488051859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3041326898778474156879317 71281099190120488051859)
                ·
                  rfl

theorem cell23_3748125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 7].length) (baseStart_3748125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748125 prefixEnd_3748125 := by exact prefixLift 3748125
  have htrace : WordTrace (prefixWord ++ tailWord_3748125) baseStart_3748125 baseEnd_3748125 := by
    simpa [prefixWord, tailWord_3748125, baseEnd_3748125] using wordTrace_append hprefix tailTrace_3748125
  have hstable : (prefixWord ++ tailWord_3748125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748125).length < 2 ^ (prefixWord ++ tailWord_3748125).sum := by decide
  have hdescent : baseEnd_3748125 < baseStart_3748125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748131 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3748131 : Nat := 118140960795 + 3748131 * 2 ^ 59
def prefixEnd_3748131 : Nat := 4983230072969 + 3 ^ 40 * 3748131 * 2
def baseEnd_3748131 : Nat := 1924592759017180153925165

theorem tailTrace_3748131 : CollatzResearch.WordTrace tailWord_3748131 prefixEnd_3748131 1924592759017180153925165 := by
  unfold tailWord_3748131
  simp only [CollatzResearch.WordTrace]
  refine ⟨136705568384168991656572247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91137045589445994437714831 136705568384168991656572247)
  ·
    refine ⟨205058352576253487484858371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136705568384168991656572247 205058352576253487484858371)
    ·
      refine ⟨307587528864380231227287557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205058352576253487484858371 307587528864380231227287557)
      ·
        refine ⟨57672661662071293355116417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307587528864380231227287557 57672661662071293355116417)
        ·
          refine ⟨43254496246553470016337313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57672661662071293355116417 43254496246553470016337313)
          ·
            refine ⟨32440872184915102512252985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43254496246553470016337313 32440872184915102512252985)
            ·
              refine ⟨24330654138686326884189739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32440872184915102512252985 24330654138686326884189739)
              ·
                refine ⟨36495981208029490326284609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24330654138686326884189739 36495981208029490326284609)
                ·
                  refine ⟨27371985906022117744713457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36495981208029490326284609 27371985906022117744713457)
                  ·
                    refine ⟨20528989429516588308535093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27371985906022117744713457 20528989429516588308535093)
                    ·
                      refine ⟨1924592759017180153925165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20528989429516588308535093 1924592759017180153925165)
                      ·
                        rfl

theorem cell23_3748131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3748131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748131 prefixEnd_3748131 := by exact prefixLift 3748131
  have htrace : WordTrace (prefixWord ++ tailWord_3748131) baseStart_3748131 baseEnd_3748131 := by
    simpa [prefixWord, tailWord_3748131, baseEnd_3748131] using wordTrace_append hprefix tailTrace_3748131
  have hstable : (prefixWord ++ tailWord_3748131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748131).length < 2 ^ (prefixWord ++ tailWord_3748131).sum := by decide
  have hdescent : baseEnd_3748131 < baseStart_3748131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748136 : List Nat := [2, 1, 5, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3748136 : Nat := 118140960795 + 3748136 * 2 ^ 59
def prefixEnd_3748136 : Nat := 4983230072969 + 3 ^ 40 * 3748136 * 2
def baseEnd_3748136 : Nat := 1924595326420452634362643

theorem tailTrace_3748136 : CollatzResearch.WordTrace tailWord_3748136 prefixEnd_3748136 1924595326420452634362643 := by
  unfold tailWord_3748136
  simp only [CollatzResearch.WordTrace]
  refine ⟨68352875374575438755252131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91137167166100585007002841 68352875374575438755252131)
  ·
    refine ⟨102529313061863158132878197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68352875374575438755252131 102529313061863158132878197)
    ·
      refine ⟨9612123099549671074957331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102529313061863158132878197 9612123099549671074957331)
      ·
        refine ⟨14418184649324506612435997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612123099549671074957331 14418184649324506612435997)
        ·
          refine ⟨5406819243496689979663499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14418184649324506612435997 5406819243496689979663499)
          ·
            refine ⟨8110228865245034969495249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5406819243496689979663499 8110228865245034969495249)
            ·
              refine ⟨6082671648933776227121437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8110228865245034969495249 6082671648933776227121437)
              ·
                refine ⟨2281001868350166085170539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6082671648933776227121437 2281001868350166085170539)
                ·
                  refine ⟨3421502802525249127755809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281001868350166085170539 3421502802525249127755809)
                  ·
                    refine ⟨2566127101893936845816857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421502802525249127755809 2566127101893936845816857)
                    ·
                      refine ⟨1924595326420452634362643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566127101893936845816857 1924595326420452634362643)
                      ·
                        rfl

theorem cell23_3748136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3748136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748136 prefixEnd_3748136 := by exact prefixLift 3748136
  have htrace : WordTrace (prefixWord ++ tailWord_3748136) baseStart_3748136 baseEnd_3748136 := by
    simpa [prefixWord, tailWord_3748136, baseEnd_3748136] using wordTrace_append hprefix tailTrace_3748136
  have hstable : (prefixWord ++ tailWord_3748136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748136).length < 2 ^ (prefixWord ++ tailWord_3748136).sum := by decide
  have hdescent : baseEnd_3748136 < baseStart_3748136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748171 : List Nat := [1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4]
def baseStart_3748171 : Nat := 118140960795 + 3748171 * 2 ^ 59
def prefixEnd_3748171 : Nat := 4983230072969 + 3 ^ 40 * 3748171 * 2
def baseEnd_3748171 : Nat := 1924613298243359997424981

theorem tailTrace_3748171 : CollatzResearch.WordTrace tailWord_3748171 prefixEnd_3748171 1924613298243359997424981 := by
  unfold tailWord_3748171
  simp only [CollatzResearch.WordTrace]
  refine ⟨136707027304024078488028367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91138018202682718992018911 136707027304024078488028367)
  ·
    refine ⟨205060540956036117732042551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136707027304024078488028367 205060540956036117732042551)
    ·
      refine ⟨307590811434054176598063827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205060540956036117732042551 307590811434054176598063827)
      ·
        refine ⟨461386217151081264897095741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307590811434054176598063827 461386217151081264897095741)
        ·
          refine ⟨173019831431655474336410903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461386217151081264897095741 173019831431655474336410903)
          ·
            refine ⟨259529747147483211504616355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173019831431655474336410903 259529747147483211504616355)
            ·
              refine ⟨389294620721224817256924533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259529747147483211504616355 389294620721224817256924533)
              ·
                refine ⟨36496370692614826617836675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389294620721224817256924533 36496370692614826617836675)
                ·
                  refine ⟨54744556038922239926755013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36496370692614826617836675 54744556038922239926755013)
                  ·
                    refine ⟨10264604257297919986266565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54744556038922239926755013 10264604257297919986266565)
                    ·
                      refine ⟨1924613298243359997424981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10264604257297919986266565 1924613298243359997424981)
                      ·
                        rfl

theorem cell23_3748171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 5, 1, 4, 4].length) (baseStart_3748171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748171 prefixEnd_3748171 := by exact prefixLift 3748171
  have htrace : WordTrace (prefixWord ++ tailWord_3748171) baseStart_3748171 baseEnd_3748171 := by
    simpa [prefixWord, tailWord_3748171, baseEnd_3748171] using wordTrace_append hprefix tailTrace_3748171
  have hstable : (prefixWord ++ tailWord_3748171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748171).length < 2 ^ (prefixWord ++ tailWord_3748171).sum := by decide
  have hdescent : baseEnd_3748171 < baseStart_3748171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748178 : List Nat := [3, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_3748178 : Nat := 118140960795 + 3748178 * 2 ^ 59
def prefixEnd_3748178 : Nat := 4983230072969 + 3 ^ 40 * 3748178 * 2
def baseEnd_3748178 : Nat := 1924616892607941470037449

theorem tailTrace_3748178 : CollatzResearch.WordTrace tailWord_3748178 prefixEnd_3748178 1924616892607941470037449 := by
  unfold tailWord_3748178
  simp only [CollatzResearch.WordTrace]
  refine ⟨34176820653749679670883297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91138188409999145789022125 34176820653749679670883297)
  ·
    refine ⟨25632615490312259753162473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34176820653749679670883297 25632615490312259753162473)
    ·
      refine ⟨19224461617734194814871855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25632615490312259753162473 19224461617734194814871855)
      ·
        refine ⟨28836692426601292222307783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19224461617734194814871855 28836692426601292222307783)
        ·
          refine ⟨43255038639901938333461675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28836692426601292222307783 43255038639901938333461675)
          ·
            refine ⟨64882557959852907500192513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43255038639901938333461675 64882557959852907500192513)
            ·
              refine ⟨48661918469889680625144385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64882557959852907500192513 48661918469889680625144385)
              ·
                refine ⟨36496438852417260468858289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48661918469889680625144385 36496438852417260468858289)
                ·
                  refine ⟨27372329139312945351643717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36496438852417260468858289 27372329139312945351643717)
                  ·
                    refine ⟨5132311713621177253433197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27372329139312945351643717 5132311713621177253433197)
                    ·
                      refine ⟨1924616892607941470037449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132311713621177253433197 1924616892607941470037449)
                      ·
                        rfl

theorem cell23_3748178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_3748178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748178 prefixEnd_3748178 := by exact prefixLift 3748178
  have htrace : WordTrace (prefixWord ++ tailWord_3748178) baseStart_3748178 baseEnd_3748178 := by
    simpa [prefixWord, tailWord_3748178, baseEnd_3748178] using wordTrace_append hprefix tailTrace_3748178
  have hstable : (prefixWord ++ tailWord_3748178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748178).length < 2 ^ (prefixWord ++ tailWord_3748178).sum := by decide
  have hdescent : baseEnd_3748178 < baseStart_3748178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748228 : List Nat := [2, 3, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3748228 : Nat := 118140960795 + 3748228 * 2 ^ 59
def prefixEnd_3748228 : Nat := 4983230072969 + 3 ^ 40 * 3748228 * 2
def baseEnd_3748228 : Nat := 641547522213555424804073

theorem tailTrace_3748228 : CollatzResearch.WordTrace tailWord_3748228 prefixEnd_3748228 641547522213555424804073 := by
  unfold tailWord_3748228
  simp only [CollatzResearch.WordTrace]
  refine ⟨68354553132408788611426669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91139404176545051481902225 68354553132408788611426669)
  ·
    refine ⟨25632957424653295729285001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68354553132408788611426669 25632957424653295729285001)
    ·
      refine ⟨19224718068489971796963751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25632957424653295729285001 19224718068489971796963751)
      ·
        refine ⟨28837077102734957695445627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19224718068489971796963751 28837077102734957695445627)
        ·
          refine ⟨43255615654102436543168441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28837077102734957695445627 43255615654102436543168441)
          ·
            refine ⟨32441711740576827407376331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43255615654102436543168441 32441711740576827407376331)
            ·
              refine ⟨48662567610865241111064497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32441711740576827407376331 48662567610865241111064497)
              ·
                refine ⟨36496925708148930833298373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48662567610865241111064497 36496925708148930833298373)
                ·
                  refine ⟨6843173570277924531243445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36496925708148930833298373 6843173570277924531243445)
                  ·
                    refine ⟨641547522213555424804073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6843173570277924531243445 641547522213555424804073)
                    ·
                      rfl

theorem cell23_3748228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3748228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748228 prefixEnd_3748228 := by exact prefixLift 3748228
  have htrace : WordTrace (prefixWord ++ tailWord_3748228) baseStart_3748228 baseEnd_3748228 := by
    simpa [prefixWord, tailWord_3748228, baseEnd_3748228] using wordTrace_append hprefix tailTrace_3748228
  have hstable : (prefixWord ++ tailWord_3748228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748228).length < 2 ^ (prefixWord ++ tailWord_3748228).sum := by decide
  have hdescent : baseEnd_3748228 < baseStart_3748228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748266 : List Nat := [3, 1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_3748266 : Nat := 118140960795 + 3748266 * 2 ^ 59
def prefixEnd_3748266 : Nat := 4983230072969 + 3 ^ 40 * 3748266 * 2
def baseEnd_3748266 : Nat := 213851342100615236193005

theorem tailTrace_3748266 : CollatzResearch.WordTrace tailWord_3748266 prefixEnd_3748266 213851342100615236193005 := by
  unfold tailWord_3748266
  simp only [CollatzResearch.WordTrace]
  refine ⟨34177623059669977428184163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91140328159119939808491101 34177623059669977428184163)
  ·
    refine ⟨51266434589504966142276245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34177623059669977428184163 51266434589504966142276245)
    ·
      refine ⟨2403114121383045287919199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51266434589504966142276245 2403114121383045287919199)
      ·
        refine ⟨3604671182074567931878799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2403114121383045287919199 3604671182074567931878799)
        ·
          refine ⟨5407006773111851897818199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3604671182074567931878799 5407006773111851897818199)
          ·
            refine ⟨8110510159667777846727299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407006773111851897818199 8110510159667777846727299)
            ·
              refine ⟨12165765239501666770090949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8110510159667777846727299 12165765239501666770090949)
              ·
                refine ⟨2281080982406562519392053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12165765239501666770090949 2281080982406562519392053)
                ·
                  refine ⟨213851342100615236193005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2281080982406562519392053 213851342100615236193005)
                  ·
                    rfl

theorem cell23_3748266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_3748266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748266 prefixEnd_3748266 := by exact prefixLift 3748266
  have htrace : WordTrace (prefixWord ++ tailWord_3748266) baseStart_3748266 baseEnd_3748266 := by
    simpa [prefixWord, tailWord_3748266, baseEnd_3748266] using wordTrace_append hprefix tailTrace_3748266
  have hstable : (prefixWord ++ tailWord_3748266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748266).length < 2 ^ (prefixWord ++ tailWord_3748266).sum := by decide
  have hdescent : baseEnd_3748266 < baseStart_3748266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748268 : List Nat := [2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 3]
def baseStart_3748268 : Nat := 118140960795 + 3748268 * 2 ^ 59
def prefixEnd_3748268 : Nat := 4983230072969 + 3 ^ 40 * 3748268 * 2
def baseEnd_3748268 : Nat := 1924663105866846117912035

theorem tailTrace_3748268 : CollatzResearch.WordTrace tailWord_3748268 prefixEnd_3748268 1924663105866846117912035 := by
  unfold tailWord_3748268
  simp only [CollatzResearch.WordTrace]
  refine ⟨68355282592336332027154729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91140376789781776036206305 68355282592336332027154729)
  ·
    refine ⟨51266461944252249020366047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68355282592336332027154729 51266461944252249020366047)
    ·
      refine ⟨76899692916378373530549071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51266461944252249020366047 76899692916378373530549071)
      ·
        refine ⟨115349539374567560295823607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76899692916378373530549071 115349539374567560295823607)
        ·
          refine ⟨173024309061851340443735411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115349539374567560295823607 173024309061851340443735411)
          ·
            refine ⟨259536463592777010665603117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173024309061851340443735411 259536463592777010665603117)
            ·
              refine ⟨97326173847291378999601169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259536463592777010665603117 97326173847291378999601169)
              ·
                refine ⟨72994630385468534249700877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97326173847291378999601169 72994630385468534249700877)
                ·
                  refine ⟨27372986394550700343637829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72994630385468534249700877 27372986394550700343637829)
                  ·
                    refine ⟨5132434948978256314432093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27372986394550700343637829 5132434948978256314432093)
                    ·
                      refine ⟨1924663105866846117912035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132434948978256314432093 1924663105866846117912035)
                      ·
                        rfl

theorem cell23_3748268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 3].length) (baseStart_3748268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748268 prefixEnd_3748268 := by exact prefixLift 3748268
  have htrace : WordTrace (prefixWord ++ tailWord_3748268) baseStart_3748268 baseEnd_3748268 := by
    simpa [prefixWord, tailWord_3748268, baseEnd_3748268] using wordTrace_append hprefix tailTrace_3748268
  have hstable : (prefixWord ++ tailWord_3748268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748268).length < 2 ^ (prefixWord ++ tailWord_3748268).sum := by decide
  have hdescent : baseEnd_3748268 < baseStart_3748268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748309 : List Nat := [1, 3, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3748309 : Nat := 118140960795 + 3748309 * 2 ^ 59
def prefixEnd_3748309 : Nat := 4983230072969 + 3 ^ 40 * 3748309 * 2
def baseEnd_3748309 : Nat := 641561386191226819166449

theorem tailTrace_3748309 : CollatzResearch.WordTrace tailWord_3748309 prefixEnd_3748309 641561386191226819166449 := by
  unfold tailWord_3748309
  simp only [CollatzResearch.WordTrace]
  refine ⟨136712060577524128056551981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91141373718349418704367987 136712060577524128056551981)
  ·
    refine ⟨51267022716571548021206993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136712060577524128056551981 51267022716571548021206993)
    ·
      refine ⟨38450267037428661015905245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51267022716571548021206993 38450267037428661015905245)
      ·
        refine ⟨14418850139035747880964467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38450267037428661015905245 14418850139035747880964467)
        ·
          refine ⟨21628275208553621821446701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14418850139035747880964467 21628275208553621821446701)
          ·
            refine ⟨8110603203207608183042513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21628275208553621821446701 8110603203207608183042513)
            ·
              refine ⟨6082952402405706137281885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8110603203207608183042513 6082952402405706137281885)
              ·
                refine ⟨2281107150902139801480707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6082952402405706137281885 2281107150902139801480707)
                ·
                  refine ⟨3421660726353209702221061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281107150902139801480707 3421660726353209702221061)
                  ·
                    refine ⟨641561386191226819166449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3421660726353209702221061 641561386191226819166449)
                    ·
                      rfl

theorem cell23_3748309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3748309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748309 prefixEnd_3748309 := by exact prefixLift 3748309
  have htrace : WordTrace (prefixWord ++ tailWord_3748309) baseStart_3748309 baseEnd_3748309 := by
    simpa [prefixWord, tailWord_3748309, baseEnd_3748309] using wordTrace_append hprefix tailTrace_3748309
  have hstable : (prefixWord ++ tailWord_3748309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748309).length < 2 ^ (prefixWord ++ tailWord_3748309).sum := by decide
  have hdescent : baseEnd_3748309 < baseStart_3748309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748332 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 3]
def baseStart_3748332 : Nat := 118140960795 + 3748332 * 2 ^ 59
def prefixEnd_3748332 : Nat := 4983230072969 + 3 ^ 40 * 3748332 * 2
def baseEnd_3748332 : Nat := 1924695968628733867511741

theorem tailTrace_3748332 : CollatzResearch.WordTrace tailWord_3748332 prefixEnd_3748332 1924695968628733867511741 := by
  unfold tailWord_3748332
  simp only [CollatzResearch.WordTrace]
  refine ⟨68356449728220401492319625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91141932970960535323092833 68356449728220401492319625)
  ·
    refine ⟨51267337296165301119239719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68356449728220401492319625 51267337296165301119239719)
    ·
      refine ⟨76901005944247951678859579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51267337296165301119239719 76901005944247951678859579)
      ·
        refine ⟨115351508916371927518289369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76901005944247951678859579 115351508916371927518289369)
        ·
          refine ⟨86513631687278945638717027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115351508916371927518289369 86513631687278945638717027)
          ·
            refine ⟨129770447530918418458075541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86513631687278945638717027 129770447530918418458075541)
            ·
              refine ⟨6082989728011800865222291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 129770447530918418458075541 6082989728011800865222291)
              ·
                refine ⟨9124484592017701297833437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6082989728011800865222291 9124484592017701297833437)
                ·
                  refine ⟨3421681722006637986687539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9124484592017701297833437 3421681722006637986687539)
                  ·
                    refine ⟨5132522583009956980031309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421681722006637986687539 5132522583009956980031309)
                    ·
                      refine ⟨1924695968628733867511741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132522583009956980031309 1924695968628733867511741)
                      ·
                        rfl

theorem cell23_3748332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 3].length) (baseStart_3748332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748332 prefixEnd_3748332 := by exact prefixLift 3748332
  have htrace : WordTrace (prefixWord ++ tailWord_3748332) baseStart_3748332 baseEnd_3748332 := by
    simpa [prefixWord, tailWord_3748332, baseEnd_3748332] using wordTrace_append hprefix tailTrace_3748332
  have hstable : (prefixWord ++ tailWord_3748332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748332).length < 2 ^ (prefixWord ++ tailWord_3748332).sum := by decide
  have hdescent : baseEnd_3748332 < baseStart_3748332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748342 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_3748342 : Nat := 118140960795 + 3748342 * 2 ^ 59
def prefixEnd_3748342 : Nat := 4983230072969 + 3 ^ 40 * 3748342 * 2
def baseEnd_3748342 : Nat := 1924701103435278828386695

theorem tailTrace_3748342 : CollatzResearch.WordTrace tailWord_3748342 prefixEnd_3748342 1924701103435278828386695 := by
  unfold tailWord_3748342
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544579011650285918281455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91142176124269716461668853 8544579011650285918281455)
  ·
    refine ⟨12816868517475428877422183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544579011650285918281455 12816868517475428877422183)
    ·
      refine ⟨19225302776213143316133275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12816868517475428877422183 19225302776213143316133275)
      ·
        refine ⟨28837954164319714974199913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19225302776213143316133275 28837954164319714974199913)
        ·
          refine ⟨21628465623239786230649935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28837954164319714974199913 21628465623239786230649935)
          ·
            refine ⟨32442698434859679345974903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21628465623239786230649935 32442698434859679345974903)
            ·
              refine ⟨48664047652289519018962355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32442698434859679345974903 48664047652289519018962355)
              ·
                refine ⟨72996071478434278528443533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48664047652289519018962355 72996071478434278528443533)
                ·
                  refine ⟨27373526804412854448166325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72996071478434278528443533 27373526804412854448166325)
                  ·
                    refine ⟨2566268137913705104515593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27373526804412854448166325 2566268137913705104515593)
                    ·
                      refine ⟨1924701103435278828386695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566268137913705104515593 1924701103435278828386695)
                      ·
                        rfl

theorem cell23_3748342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_3748342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748342 prefixEnd_3748342 := by exact prefixLift 3748342
  have htrace : WordTrace (prefixWord ++ tailWord_3748342) baseStart_3748342 baseEnd_3748342 := by
    simpa [prefixWord, tailWord_3748342, baseEnd_3748342] using wordTrace_append hprefix tailTrace_3748342
  have hstable : (prefixWord ++ tailWord_3748342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748342).length < 2 ^ (prefixWord ++ tailWord_3748342).sum := by decide
  have hdescent : baseEnd_3748342 < baseStart_3748342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748355 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 2, 6, 2]
def baseStart_3748355 : Nat := 118140960795 + 3748355 * 2 ^ 59
def prefixEnd_3748355 : Nat := 4983230072969 + 3 ^ 40 * 3748355 * 2
def baseEnd_3748355 : Nat := 1924707778683787277524135

theorem tailTrace_3748355 : CollatzResearch.WordTrace tailWord_3748355 prefixEnd_3748355 1924707778683787277524135 := by
  unfold tailWord_3748355
  simp only [CollatzResearch.WordTrace]
  refine ⟨136713738335357477912726519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91142492223571651941817679 136713738335357477912726519)
  ·
    refine ⟨205070607503036216869089779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136713738335357477912726519 205070607503036216869089779)
    ·
      refine ⟨307605911254554325303634669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205070607503036216869089779 307605911254554325303634669)
      ·
        refine ⟨115352216720457871988863001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 307605911254554325303634669 115352216720457871988863001)
        ·
          refine ⟨86514162540343403991647251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115352216720457871988863001 86514162540343403991647251)
          ·
            refine ⟨129771243810515105987470877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86514162540343403991647251 129771243810515105987470877)
            ·
              refine ⟨48664216428943164745301579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129771243810515105987470877 48664216428943164745301579)
              ·
                refine ⟨72996324643414747117952369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48664216428943164745301579 72996324643414747117952369)
                ·
                  refine ⟨54747243482561060338464277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72996324643414747117952369 54747243482561060338464277)
                  ·
                    refine ⟨2566277038245049703365513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54747243482561060338464277 2566277038245049703365513)
                    ·
                      refine ⟨1924707778683787277524135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566277038245049703365513 1924707778683787277524135)
                      ·
                        rfl

theorem cell23_3748355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 6, 2].length) (baseStart_3748355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748355 prefixEnd_3748355 := by exact prefixLift 3748355
  have htrace : WordTrace (prefixWord ++ tailWord_3748355) baseStart_3748355 baseEnd_3748355 := by
    simpa [prefixWord, tailWord_3748355, baseEnd_3748355] using wordTrace_append hprefix tailTrace_3748355
  have hstable : (prefixWord ++ tailWord_3748355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748355).length < 2 ^ (prefixWord ++ tailWord_3748355).sum := by decide
  have hdescent : baseEnd_3748355 < baseStart_3748355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748366 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3]
def baseStart_3748366 : Nat := 118140960795 + 3748366 * 2 ^ 59
def prefixEnd_3748366 : Nat := 4983230072969 + 3 ^ 40 * 3748366 * 2
def baseEnd_3748366 : Nat := 1924713426970986734486585

theorem tailTrace_3748366 : CollatzResearch.WordTrace tailWord_3748366 prefixEnd_3748366 1924713426970986734486585 := by
  unfold tailWord_3748366
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089267442289703348922119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91142759692211751194251301 17089267442289703348922119)
  ·
    refine ⟨25633901163434555023383179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17089267442289703348922119 25633901163434555023383179)
    ·
      refine ⟨38450851745151832535074769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25633901163434555023383179 38450851745151832535074769)
      ·
        refine ⟨28838138808863874401306077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38450851745151832535074769 28838138808863874401306077)
        ·
          refine ⟨10814302053323952900489779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28838138808863874401306077 10814302053323952900489779)
          ·
            refine ⟨16221453079985929350734669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814302053323952900489779 16221453079985929350734669)
            ·
              refine ⟨6083044904994723506525501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16221453079985929350734669 6083044904994723506525501)
              ·
                refine ⟨2281141839373021314947063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6083044904994723506525501 2281141839373021314947063)
                ·
                  refine ⟨3421712759059531972420595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2281141839373021314947063 3421712759059531972420595)
                  ·
                    refine ⟨5132569138589297958630893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421712759059531972420595 5132569138589297958630893)
                    ·
                      refine ⟨1924713426970986734486585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132569138589297958630893 1924713426970986734486585)
                      ·
                        rfl

theorem cell23_3748366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_3748366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748366 prefixEnd_3748366 := by exact prefixLift 3748366
  have htrace : WordTrace (prefixWord ++ tailWord_3748366) baseStart_3748366 baseEnd_3748366 := by
    simpa [prefixWord, tailWord_3748366, baseEnd_3748366] using wordTrace_append hprefix tailTrace_3748366
  have hstable : (prefixWord ++ tailWord_3748366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748366).length < 2 ^ (prefixWord ++ tailWord_3748366).sum := by decide
  have hdescent : baseEnd_3748366 < baseStart_3748366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748378 : List Nat := [3, 1, 1, 3, 1, 1, 13]
def baseStart_3748378 : Nat := 118140960795 + 3748378 * 2 ^ 59
def prefixEnd_3748378 : Nat := 4983230072969 + 3 ^ 40 * 3748378 * 2
def baseEnd_3748378 : Nat := 23761970231343712191809

theorem tailTrace_3748378 : CollatzResearch.WordTrace tailWord_3748378 prefixEnd_3748378 23761970231343712191809 := by
  unfold tailWord_3748378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34178644303568538210203447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91143051476182768560542525 34178644303568538210203447)
  ·
    refine ⟨51267966455352807315305171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34178644303568538210203447 51267966455352807315305171)
    ·
      refine ⟨76901949683029210972957757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51267966455352807315305171 76901949683029210972957757)
      ·
        refine ⟨28838231131135954114859159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76901949683029210972957757 28838231131135954114859159)
        ·
          refine ⟨43257346696703931172288739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28838231131135954114859159 43257346696703931172288739)
          ·
            refine ⟨64886020045055896758433109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43257346696703931172288739 64886020045055896758433109)
            ·
              refine ⟨23761970231343712191809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 64886020045055896758433109 23761970231343712191809)
              ·
                rfl

theorem cell23_3748378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 13].length) (baseStart_3748378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748378 prefixEnd_3748378 := by exact prefixLift 3748378
  have htrace : WordTrace (prefixWord ++ tailWord_3748378) baseStart_3748378 baseEnd_3748378 := by
    simpa [prefixWord, tailWord_3748378, baseEnd_3748378] using wordTrace_append hprefix tailTrace_3748378
  have hstable : (prefixWord ++ tailWord_3748378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748378).length < 2 ^ (prefixWord ++ tailWord_3748378).sum := by decide
  have hdescent : baseEnd_3748378 < baseStart_3748378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748389 : List Nat := [1, 3, 1, 2, 2, 1, 5, 1, 3, 2, 2]
def baseStart_3748389 : Nat := 118140960795 + 3748389 * 2 ^ 59
def prefixEnd_3748389 : Nat := 4983230072969 + 3 ^ 40 * 3748389 * 2
def baseEnd_3748389 : Nat := 1924725237026040144498979

theorem tailTrace_3748389 : CollatzResearch.WordTrace tailWord_3748389 prefixEnd_3748389 1924725237026040144498979 := by
  unfold tailWord_3748389
  simp only [CollatzResearch.WordTrace]
  refine ⟨136714978417234301719464221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91143318944822867812976147 136714978417234301719464221)
  ·
    refine ⟨51268116906462863144799083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136714978417234301719464221 51268116906462863144799083)
    ·
      refine ⟨76902175359694294717198625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51268116906462863144799083 76902175359694294717198625)
      ·
        refine ⟨57676631519770721037898969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76902175359694294717198625 57676631519770721037898969)
        ·
          refine ⟨43257473639828040778424227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57676631519770721037898969 43257473639828040778424227)
          ·
            refine ⟨64886210459742061167636341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43257473639828040778424227 64886210459742061167636341)
            ·
              refine ⟨6083082230600818234465907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64886210459742061167636341 6083082230600818234465907)
              ·
                refine ⟨9124623345901227351698861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083082230600818234465907 9124623345901227351698861)
                ·
                  refine ⟨3421733754712960256887073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9124623345901227351698861 3421733754712960256887073)
                  ·
                    refine ⟨2566300316034720192665305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3421733754712960256887073 2566300316034720192665305)
                    ·
                      refine ⟨1924725237026040144498979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566300316034720192665305 1924725237026040144498979)
                      ·
                        rfl

theorem cell23_3748389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_3748389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748389 prefixEnd_3748389 := by exact prefixLift 3748389
  have htrace : WordTrace (prefixWord ++ tailWord_3748389) baseStart_3748389 baseEnd_3748389 := by
    simpa [prefixWord, tailWord_3748389, baseEnd_3748389] using wordTrace_append hprefix tailTrace_3748389
  have hstable : (prefixWord ++ tailWord_3748389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748389).length < 2 ^ (prefixWord ++ tailWord_3748389).sum := by decide
  have hdescent : baseEnd_3748389 < baseStart_3748389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748392 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3748392 : Nat := 118140960795 + 3748392 * 2 ^ 59
def prefixEnd_3748392 : Nat := 4983230072969 + 3 ^ 40 * 3748392 * 2
def baseEnd_3748392 : Nat := 1924726777468003632761465

theorem tailTrace_3748392 : CollatzResearch.WordTrace tailWord_3748392 prefixEnd_3748392 1924726777468003632761465 := by
  unfold tailWord_3748392
  simp only [CollatzResearch.WordTrace]
  refine ⟨68357543918111716615911715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91143391890815622154548953 68357543918111716615911715)
  ·
    refine ⟨102536315877167574923867573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68357543918111716615911715 102536315877167574923867573)
    ·
      refine ⟨9612779613484460149112585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102536315877167574923867573 9612779613484460149112585)
      ·
        refine ⟨7209584710113345111834439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9612779613484460149112585 7209584710113345111834439)
        ·
          refine ⟨10814377065170017667751659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7209584710113345111834439 10814377065170017667751659)
          ·
            refine ⟨16221565597755026501627489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814377065170017667751659 16221565597755026501627489)
            ·
              refine ⟨12166174198316269876220617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16221565597755026501627489 12166174198316269876220617)
              ·
                refine ⟨9124630648737202407165463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12166174198316269876220617 9124630648737202407165463)
                ·
                  refine ⟨13686945973105803610748195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124630648737202407165463 13686945973105803610748195)
                  ·
                    refine ⟨20530418959658705416122293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13686945973105803610748195 20530418959658705416122293)
                    ·
                      refine ⟨1924726777468003632761465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20530418959658705416122293 1924726777468003632761465)
                      ·
                        rfl

theorem cell23_3748392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3748392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748392 prefixEnd_3748392 := by exact prefixLift 3748392
  have htrace : WordTrace (prefixWord ++ tailWord_3748392) baseStart_3748392 baseEnd_3748392 := by
    simpa [prefixWord, tailWord_3748392, baseEnd_3748392] using wordTrace_append hprefix tailTrace_3748392
  have hstable : (prefixWord ++ tailWord_3748392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748392).length < 2 ^ (prefixWord ++ tailWord_3748392).sum := by decide
  have hdescent : baseEnd_3748392 < baseStart_3748392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748406 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_3748406 : Nat := 118140960795 + 3748406 * 2 ^ 59
def prefixEnd_3748406 : Nat := 4983230072969 + 3 ^ 40 * 3748406 * 2
def baseEnd_3748406 : Nat := 1924733966197166577986401

theorem tailTrace_3748406 : CollatzResearch.WordTrace tailWord_3748406 prefixEnd_3748406 1924733966197166577986401 := by
  unfold tailWord_3748406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8544724903635794601427067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91143732305448475748555381 8544724903635794601427067)
  ·
    refine ⟨12817087355453691902140601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8544724903635794601427067 12817087355453691902140601)
    ·
      refine ⟨9612815516590268926605451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12817087355453691902140601 9612815516590268926605451)
      ·
        refine ⟨14419223274885403389908177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9612815516590268926605451 14419223274885403389908177)
        ·
          refine ⟨10814417456164052542431133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14419223274885403389908177 10814417456164052542431133)
          ·
            refine ⟨4055406546061519703411675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10814417456164052542431133 4055406546061519703411675)
            ·
              refine ⟨6083109819092279555117513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055406546061519703411675 6083109819092279555117513)
              ·
                refine ⟨4562332364319209666338135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6083109819092279555117513 4562332364319209666338135)
                ·
                  refine ⟨6843498546478814499507203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4562332364319209666338135 6843498546478814499507203)
                  ·
                    refine ⟨10265247819718221749260805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6843498546478814499507203 10265247819718221749260805)
                    ·
                      refine ⟨1924733966197166577986401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10265247819718221749260805 1924733966197166577986401)
                      ·
                        rfl

theorem cell23_3748406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_3748406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748406 prefixEnd_3748406 := by exact prefixLift 3748406
  have htrace : WordTrace (prefixWord ++ tailWord_3748406) baseStart_3748406 baseEnd_3748406 := by
    simpa [prefixWord, tailWord_3748406, baseEnd_3748406] using wordTrace_append hprefix tailTrace_3748406
  have hstable : (prefixWord ++ tailWord_3748406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748406).length < 2 ^ (prefixWord ++ tailWord_3748406).sum := by decide
  have hdescent : baseEnd_3748406 < baseStart_3748406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748439 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_3748439 : Nat := 118140960795 + 3748439 * 2 ^ 59
def prefixEnd_3748439 : Nat := 4983230072969 + 3 ^ 40 * 3748439 * 2
def baseEnd_3748439 : Nat := 1924750911058764948873749

theorem tailTrace_3748439 : CollatzResearch.WordTrace tailWord_3748439 prefixEnd_3748439 1924750911058764948873749 := by
  unfold tailWord_3748439
  simp only [CollatzResearch.WordTrace]
  refine ⟨136716802067053160258784371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91144534711368773505856247 136716802067053160258784371)
  ·
    refine ⟨205075203100579740388176557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136716802067053160258784371 205075203100579740388176557)
    ·
      refine ⟨76903201162717402645566209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205075203100579740388176557 76903201162717402645566209)
      ·
        refine ⟨57677400872038051984174657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76903201162717402645566209 57677400872038051984174657)
        ·
          refine ⟨43258050654028538988130993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57677400872038051984174657 43258050654028538988130993)
          ·
            refine ⟨32443537990521404241098245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43258050654028538988130993 32443537990521404241098245)
            ·
              refine ⟨6083163373222763295205921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32443537990521404241098245 6083163373222763295205921)
              ·
                refine ⟨4562372529917072471404441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6083163373222763295205921 4562372529917072471404441)
                ·
                  refine ⟨3421779397437804353553331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4562372529917072471404441 3421779397437804353553331)
                  ·
                    refine ⟨5132669096156706530329997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421779397437804353553331 5132669096156706530329997)
                    ·
                      refine ⟨1924750911058764948873749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132669096156706530329997 1924750911058764948873749)
                      ·
                        rfl

theorem cell23_3748439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_3748439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748439 prefixEnd_3748439 := by exact prefixLift 3748439
  have htrace : WordTrace (prefixWord ++ tailWord_3748439) baseStart_3748439 baseEnd_3748439 := by
    simpa [prefixWord, tailWord_3748439, baseEnd_3748439] using wordTrace_append hprefix tailTrace_3748439
  have hstable : (prefixWord ++ tailWord_3748439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748439).length < 2 ^ (prefixWord ++ tailWord_3748439).sum := by decide
  have hdescent : baseEnd_3748439 < baseStart_3748439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748495 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 3]
def baseStart_3748495 : Nat := 118140960795 + 3748495 * 2 ^ 59
def prefixEnd_3748495 : Nat := 4983230072969 + 3 ^ 40 * 3748495 * 2
def baseEnd_3748495 : Nat := 1924779665975416729773491

theorem tailTrace_3748495 : CollatzResearch.WordTrace tailWord_3748495 prefixEnd_3748495 1924779665975416729773491 := by
  unfold tailWord_3748495
  simp only [CollatzResearch.WordTrace]
  refine ⟨136718844554850281822822939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91145896369900187881881959 136718844554850281822822939)
  ·
    refine ⟨205078266832275422734234409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136718844554850281822822939 205078266832275422734234409)
    ·
      refine ⟨153808700124206567050675807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205078266832275422734234409 153808700124206567050675807)
      ·
        refine ⟨230713050186309850576013711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153808700124206567050675807 230713050186309850576013711)
        ·
          refine ⟨346069575279464775864020567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230713050186309850576013711 346069575279464775864020567)
          ·
            refine ⟨519104362919197163796030851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346069575279464775864020567 519104362919197163796030851)
            ·
              refine ⟨778656544378795745694046277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519104362919197163796030851 778656544378795745694046277)
              ·
                refine ⟨145998102071024202317633677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 778656544378795745694046277 145998102071024202317633677)
                ·
                  refine ⟨54749288276634075869112629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 145998102071024202317633677 54749288276634075869112629)
                  ·
                    refine ⟨5132745775934444612729309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54749288276634075869112629 5132745775934444612729309)
                    ·
                      refine ⟨1924779665975416729773491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132745775934444612729309 1924779665975416729773491)
                      ·
                        rfl

theorem cell23_3748495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 3, 5, 3].length) (baseStart_3748495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748495 prefixEnd_3748495 := by exact prefixLift 3748495
  have htrace : WordTrace (prefixWord ++ tailWord_3748495) baseStart_3748495 baseEnd_3748495 := by
    simpa [prefixWord, tailWord_3748495, baseEnd_3748495] using wordTrace_append hprefix tailTrace_3748495
  have hstable : (prefixWord ++ tailWord_3748495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748495).length < 2 ^ (prefixWord ++ tailWord_3748495).sum := by decide
  have hdescent : baseEnd_3748495 < baseStart_3748495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748513 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_3748513 : Nat := 118140960795 + 3748513 * 2 ^ 59
def prefixEnd_3748513 : Nat := 4983230072969 + 3 ^ 40 * 3748513 * 2
def baseEnd_3748513 : Nat := 1924788908627197659348409

theorem tailTrace_3748513 : CollatzResearch.WordTrace tailWord_3748513 prefixEnd_3748513 1924788908627197659348409 := by
  unfold tailWord_3748513
  simp only [CollatzResearch.WordTrace]
  refine ⟨136719501068785070896978193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91146334045856713931318795 136719501068785070896978193)
  ·
    refine ⟨102539625801588803172733645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136719501068785070896978193 102539625801588803172733645)
    ·
      refine ⟨38452359675595801189775117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102539625801588803172733645 38452359675595801189775117)
      ·
        refine ⟨14419634878348425446165669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38452359675595801189775117 14419634878348425446165669)
        ·
          refine ⟨2703681539690329771156063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14419634878348425446165669 2703681539690329771156063)
          ·
            refine ⟨4055522309535494656734095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703681539690329771156063 4055522309535494656734095)
            ·
              refine ⟨6083283464303241985101143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055522309535494656734095 6083283464303241985101143)
              ·
                refine ⟨9124925196454862977651715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6083283464303241985101143 9124925196454862977651715)
                ·
                  refine ⟨13687387794682294466477573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9124925196454862977651715 13687387794682294466477573)
                  ·
                    refine ⟨2566385211502930212464545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13687387794682294466477573 2566385211502930212464545)
                    ·
                      refine ⟨1924788908627197659348409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566385211502930212464545 1924788908627197659348409)
                      ·
                        rfl

theorem cell23_3748513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_3748513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748513 prefixEnd_3748513 := by exact prefixLift 3748513
  have htrace : WordTrace (prefixWord ++ tailWord_3748513) baseStart_3748513 baseEnd_3748513 := by
    simpa [prefixWord, tailWord_3748513, baseEnd_3748513] using wordTrace_append hprefix tailTrace_3748513
  have hstable : (prefixWord ++ tailWord_3748513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748513).length < 2 ^ (prefixWord ++ tailWord_3748513).sum := by decide
  have hdescent : baseEnd_3748513 < baseStart_3748513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748515 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 6, 5]
def baseStart_3748515 : Nat := 118140960795 + 3748515 * 2 ^ 59
def prefixEnd_3748515 : Nat := 4983230072969 + 3 ^ 40 * 3748515 * 2
def baseEnd_3748515 : Nat := 641596645196168883841133

theorem tailTrace_3748515 : CollatzResearch.WordTrace tailWord_3748515 prefixEnd_3748515 641596645196168883841133 := by
  unfold tailWord_3748515
  simp only [CollatzResearch.WordTrace]
  refine ⟨136719574014777825238550999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91146382676518550159033999 136719574014777825238550999)
  ·
    refine ⟨205079361022166737857826499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136719574014777825238550999 205079361022166737857826499)
    ·
      refine ⟨307619041533250106786739749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205079361022166737857826499 307619041533250106786739749)
      ·
        refine ⟨57678570287484395022513703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 307619041533250106786739749 57678570287484395022513703)
        ·
          refine ⟨86517855431226592533770555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57678570287484395022513703 86517855431226592533770555)
          ·
            refine ⟨129776783146839888800655833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86517855431226592533770555 129776783146839888800655833)
            ·
              refine ⟨97332587360129916600491875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129776783146839888800655833 97332587360129916600491875)
              ·
                refine ⟨145998881040194874900737813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97332587360129916600491875 145998881040194874900737813)
                ·
                  refine ⟨6843697548759134760972085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 145998881040194874900737813 6843697548759134760972085)
                  ·
                    refine ⟨641596645196168883841133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6843697548759134760972085 641596645196168883841133)
                    ·
                      rfl

theorem cell23_3748515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 5].length) (baseStart_3748515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748515 prefixEnd_3748515 := by exact prefixLift 3748515
  have htrace : WordTrace (prefixWord ++ tailWord_3748515) baseStart_3748515 baseEnd_3748515 := by
    simpa [prefixWord, tailWord_3748515, baseEnd_3748515] using wordTrace_append hprefix tailTrace_3748515
  have hstable : (prefixWord ++ tailWord_3748515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748515).length < 2 ^ (prefixWord ++ tailWord_3748515).sum := by decide
  have hdescent : baseEnd_3748515 < baseStart_3748515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748542 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5]
def baseStart_3748542 : Nat := 118140960795 + 3748542 * 2 ^ 59
def prefixEnd_3748542 : Nat := 4983230072969 + 3 ^ 40 * 3748542 * 2
def baseEnd_3748542 : Nat := 1924803799566178045885775

theorem tailTrace_3748542 : CollatzResearch.WordTrace tailWord_3748542 prefixEnd_3748542 1924803799566178045885775 := by
  unfold tailWord_3748542
  simp only [CollatzResearch.WordTrace]
  refine ⟨17090069848210001106222985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91147039190453339233189253 17090069848210001106222985)
  ·
    refine ⟨12817552386157500829667239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17090069848210001106222985 12817552386157500829667239)
    ·
      refine ⟨19226328579236251244500859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12817552386157500829667239 19226328579236251244500859)
      ·
        refine ⟨28839492868854376866751289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19226328579236251244500859 28839492868854376866751289)
        ·
          refine ⟨21629619651640782650063467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28839492868854376866751289 21629619651640782650063467)
          ·
            refine ⟨32444429477461173975095201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21629619651640782650063467 32444429477461173975095201)
            ·
              refine ⟨24333322108095880481321401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32444429477461173975095201 24333322108095880481321401)
              ·
                refine ⟨18249991581071910360991051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24333322108095880481321401 18249991581071910360991051)
                ·
                  refine ⟨27374987371607865541486577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18249991581071910360991051 27374987371607865541486577)
                  ·
                    refine ⟨20531240528705899156114933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27374987371607865541486577 20531240528705899156114933)
                    ·
                      refine ⟨1924803799566178045885775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20531240528705899156114933 1924803799566178045885775)
                      ·
                        rfl

theorem cell23_3748542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_3748542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748542 prefixEnd_3748542 := by exact prefixLift 3748542
  have htrace : WordTrace (prefixWord ++ tailWord_3748542) baseStart_3748542 baseEnd_3748542 := by
    simpa [prefixWord, tailWord_3748542, baseEnd_3748542] using wordTrace_append hprefix tailTrace_3748542
  have hstable : (prefixWord ++ tailWord_3748542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748542).length < 2 ^ (prefixWord ++ tailWord_3748542).sum := by decide
  have hdescent : baseEnd_3748542 < baseStart_3748542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748552 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 4, 1, 4]
def baseStart_3748552 : Nat := 118140960795 + 3748552 * 2 ^ 59
def prefixEnd_3748552 : Nat := 4983230072969 + 3 ^ 40 * 3748552 * 2
def baseEnd_3748552 : Nat := 1924808934372723006760729

theorem tailTrace_3748552 : CollatzResearch.WordTrace tailWord_3748552 prefixEnd_3748552 1924808934372723006760729 := by
  unfold tailWord_3748552
  simp only [CollatzResearch.WordTrace]
  refine ⟨68360461757821890278823955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91147282343762520371765273 68360461757821890278823955)
  ·
    refine ⟨102540692636732835418235933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68360461757821890278823955 102540692636732835418235933)
    ·
      refine ⟨38452759738774813281838475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102540692636732835418235933 38452759738774813281838475)
      ·
        refine ⟨57679139608162219922757713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38452759738774813281838475 57679139608162219922757713)
        ·
          refine ⟨43259354706121664942068285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57679139608162219922757713 43259354706121664942068285)
          ·
            refine ⟨16222258014795624353275607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43259354706121664942068285 16222258014795624353275607)
            ·
              refine ⟨24333387022193436529913411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16222258014795624353275607 24333387022193436529913411)
              ·
                refine ⟨36500080533290154794870117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24333387022193436529913411 36500080533290154794870117)
                ·
                  refine ⟨6843765099991904024038147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36500080533290154794870117 6843765099991904024038147)
                  ·
                    refine ⟨10265647649987856036057221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6843765099991904024038147 10265647649987856036057221)
                    ·
                      refine ⟨1924808934372723006760729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10265647649987856036057221 1924808934372723006760729)
                      ·
                        rfl

theorem cell23_3748552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_3748552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748552 prefixEnd_3748552 := by exact prefixLift 3748552
  have htrace : WordTrace (prefixWord ++ tailWord_3748552) baseStart_3748552 baseEnd_3748552 := by
    simpa [prefixWord, tailWord_3748552, baseEnd_3748552] using wordTrace_append hprefix tailTrace_3748552
  have hstable : (prefixWord ++ tailWord_3748552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748552).length < 2 ^ (prefixWord ++ tailWord_3748552).sum := by decide
  have hdescent : baseEnd_3748552 < baseStart_3748552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748595 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8]
def baseStart_3748595 : Nat := 118140960795 + 3748595 * 2 ^ 59
def prefixEnd_3748595 : Nat := 4983230072969 + 3 ^ 40 * 3748595 * 2
def baseEnd_3748595 : Nat := 1924831014040866338523031

theorem tailTrace_3748595 : CollatzResearch.WordTrace tailWord_3748595 prefixEnd_3748595 1924831014040866338523031 := by
  unfold tailWord_3748595
  simp only [CollatzResearch.WordTrace]
  refine ⟨136722491854487998901463239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91148327902991999267642159 136722491854487998901463239)
  ·
    refine ⟨205083737781731998352194859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136722491854487998901463239 205083737781731998352194859)
    ·
      refine ⟨307625606672597997528292289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205083737781731998352194859 307625606672597997528292289)
      ·
        refine ⟨230719205004448498146219217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 307625606672597997528292289 230719205004448498146219217)
        ·
          refine ⟨173039403753336373609664413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230719205004448498146219217 173039403753336373609664413)
          ·
            refine ⟨64889776407501140103624155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173039403753336373609664413 64889776407501140103624155)
            ·
              refine ⟨97334664611251710155436233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64889776407501140103624155 97334664611251710155436233)
              ·
                refine ⟨73000998458438782616577175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97334664611251710155436233 73000998458438782616577175)
                ·
                  refine ⟨109501497687658173924865763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73000998458438782616577175 109501497687658173924865763)
                  ·
                    refine ⟨164252246531487260887298645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 109501497687658173924865763 164252246531487260887298645)
                    ·
                      refine ⟨1924831014040866338523031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 164252246531487260887298645 1924831014040866338523031)
                      ·
                        rfl

theorem cell23_3748595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_3748595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748595 prefixEnd_3748595 := by exact prefixLift 3748595
  have htrace : WordTrace (prefixWord ++ tailWord_3748595) baseStart_3748595 baseEnd_3748595 := by
    simpa [prefixWord, tailWord_3748595, baseEnd_3748595] using wordTrace_append hprefix tailTrace_3748595
  have hstable : (prefixWord ++ tailWord_3748595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748595).length < 2 ^ (prefixWord ++ tailWord_3748595).sum := by decide
  have hdescent : baseEnd_3748595 < baseStart_3748595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748606 : List Nat := [4, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3]
def baseStart_3748606 : Nat := 118140960795 + 3748606 * 2 ^ 59
def prefixEnd_3748606 : Nat := 4983230072969 + 3 ^ 40 * 3748606 * 2
def baseEnd_3748606 : Nat := 1924836662328065795485481

theorem tailTrace_3748606 : CollatzResearch.WordTrace tailWord_3748606 prefixEnd_3748606 1924836662328065795485481 := by
  unfold tailWord_3748606
  simp only [CollatzResearch.WordTrace]
  refine ⟨17090361632181018472514209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91148595371632098520075781 17090361632181018472514209)
  ·
    refine ⟨12817771224135763854385657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17090361632181018472514209 12817771224135763854385657)
    ·
      refine ⟨9613328418101822890789243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12817771224135763854385657 9613328418101822890789243)
      ·
        refine ⟨14419992627152734336183865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613328418101822890789243 14419992627152734336183865)
        ·
          refine ⟨10814994470364550752137899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14419992627152734336183865 10814994470364550752137899)
          ·
            refine ⟨16222491705546826128206849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10814994470364550752137899 16222491705546826128206849)
            ·
              refine ⟨12166868779160119596155137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16222491705546826128206849 12166868779160119596155137)
              ·
                refine ⟨9125151584370089697116353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12166868779160119596155137 9125151584370089697116353)
                ·
                  refine ⟨6843863688277567272837265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9125151584370089697116353 6843863688277567272837265)
                  ·
                    refine ⟨5132897766208175454627949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6843863688277567272837265 5132897766208175454627949)
                    ·
                      refine ⟨1924836662328065795485481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132897766208175454627949 1924836662328065795485481)
                      ·
                        rfl

theorem cell23_3748606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_3748606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748606 prefixEnd_3748606 := by exact prefixLift 3748606
  have htrace : WordTrace (prefixWord ++ tailWord_3748606) baseStart_3748606 baseEnd_3748606 := by
    simpa [prefixWord, tailWord_3748606, baseEnd_3748606] using wordTrace_append hprefix tailTrace_3748606
  have hstable : (prefixWord ++ tailWord_3748606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748606).length < 2 ^ (prefixWord ++ tailWord_3748606).sum := by decide
  have hdescent : baseEnd_3748606 < baseStart_3748606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748612 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3748612 : Nat := 118140960795 + 3748612 * 2 ^ 59
def prefixEnd_3748612 : Nat := 4983230072969 + 3 ^ 40 * 3748612 * 2
def baseEnd_3748612 : Nat := 1924839743211992772010453

theorem tailTrace_3748612 : CollatzResearch.WordTrace tailWord_3748612 prefixEnd_3748612 1924839743211992772010453 := by
  unfold tailWord_3748612
  simp only [CollatzResearch.WordTrace]
  refine ⟨68361555947713205402416045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91148741263617607203221393 68361555947713205402416045)
  ·
    refine ⟨25635583480392452025906017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68361555947713205402416045 25635583480392452025906017)
    ·
      refine ⟨19226687610294339019429513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25635583480392452025906017 19226687610294339019429513)
      ·
        refine ⟨14420015707720754264572135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19226687610294339019429513 14420015707720754264572135)
        ·
          refine ⟨21630023561581131396858203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14420015707720754264572135 21630023561581131396858203)
          ·
            refine ⟨32445035342371697095287305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21630023561581131396858203 32445035342371697095287305)
            ·
              refine ⟨24333776506778772821465479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32445035342371697095287305 24333776506778772821465479)
              ·
                refine ⟨36500664760168159232198219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24333776506778772821465479 36500664760168159232198219)
                ·
                  refine ⟨54750997140252238848297329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36500664760168159232198219 54750997140252238848297329)
                  ·
                    refine ⟨41063247855189179136222997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54750997140252238848297329 41063247855189179136222997)
                    ·
                      refine ⟨1924839743211992772010453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41063247855189179136222997 1924839743211992772010453)
                      ·
                        rfl

theorem cell23_3748612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3748612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748612 prefixEnd_3748612 := by exact prefixLift 3748612
  have htrace : WordTrace (prefixWord ++ tailWord_3748612) baseStart_3748612 baseEnd_3748612 := by
    simpa [prefixWord, tailWord_3748612, baseEnd_3748612] using wordTrace_append hprefix tailTrace_3748612
  have hstable : (prefixWord ++ tailWord_3748612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748612).length < 2 ^ (prefixWord ++ tailWord_3748612).sum := by decide
  have hdescent : baseEnd_3748612 < baseStart_3748612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748619 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 3]
def baseStart_3748619 : Nat := 118140960795 + 3748619 * 2 ^ 59
def prefixEnd_3748619 : Nat := 4983230072969 + 3 ^ 40 * 3748619 * 2
def baseEnd_3748619 : Nat := 1924843337576574244622921

theorem tailTrace_3748619 : CollatzResearch.WordTrace tailWord_3748619 prefixEnd_3748619 1924843337576574244622921 := by
  unfold tailWord_3748619
  simp only [CollatzResearch.WordTrace]
  refine ⟨136723367206401051000336911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91148911470934034000224607 136723367206401051000336911)
  ·
    refine ⟨205085050809601576500505367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136723367206401051000336911 205085050809601576500505367)
    ·
      refine ⟨307627576214402364750758051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205085050809601576500505367 307627576214402364750758051)
      ·
        refine ⟨461441364321603547126137077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 307627576214402364750758051 461441364321603547126137077)
        ·
          refine ⟨43260127905150332543075351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 461441364321603547126137077 43260127905150332543075351)
          ·
            refine ⟨64890191857725498814613027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43260127905150332543075351 64890191857725498814613027)
            ·
              refine ⟨97335287786588248221919541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64890191857725498814613027 97335287786588248221919541)
              ·
                refine ⟨9125183229992648270804957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97335287786588248221919541 9125183229992648270804957)
                ·
                  refine ⟨3421943711247243101551859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9125183229992648270804957 3421943711247243101551859)
                  ·
                    refine ⟨5132915566870864652327789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421943711247243101551859 5132915566870864652327789)
                    ·
                      refine ⟨1924843337576574244622921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132915566870864652327789 1924843337576574244622921)
                      ·
                        rfl

theorem cell23_3748619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 1, 3].length) (baseStart_3748619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748619 prefixEnd_3748619 := by exact prefixLift 3748619
  have htrace : WordTrace (prefixWord ++ tailWord_3748619) baseStart_3748619 baseEnd_3748619 := by
    simpa [prefixWord, tailWord_3748619, baseEnd_3748619] using wordTrace_append hprefix tailTrace_3748619
  have hstable : (prefixWord ++ tailWord_3748619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748619).length < 2 ^ (prefixWord ++ tailWord_3748619).sum := by decide
  have hdescent : baseEnd_3748619 < baseStart_3748619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748629 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 1, 5, 2]
def baseStart_3748629 : Nat := 118140960795 + 3748629 * 2 ^ 59
def prefixEnd_3748629 : Nat := 4983230072969 + 3 ^ 40 * 3748629 * 2
def baseEnd_3748629 : Nat := 1924848472383119205497875

theorem tailTrace_3748629 : CollatzResearch.WordTrace tailWord_3748629 prefixEnd_3748629 1924848472383119205497875 := by
  unfold tailWord_3748629
  simp only [CollatzResearch.WordTrace]
  refine ⟨136723731936364822708200941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91149154624243215138800627 136723731936364822708200941)
  ·
    refine ⟨51271399476136808515575353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136723731936364822708200941 51271399476136808515575353)
    ·
      refine ⟨38453549607102606386681515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51271399476136808515575353 38453549607102606386681515)
      ·
        refine ⟨57680324410653909580022273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38453549607102606386681515 57680324410653909580022273)
        ·
          refine ⟨43260243307990432185016705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57680324410653909580022273 43260243307990432185016705)
          ·
            refine ⟨32445182480992824138762529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43260243307990432185016705 32445182480992824138762529)
            ·
              refine ⟨24333886860744618104071897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32445182480992824138762529 24333886860744618104071897)
              ·
                refine ⟨18250415145558463578053923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24333886860744618104071897 18250415145558463578053923)
                ·
                  refine ⟨27375622718337695367080885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18250415145558463578053923 27375622718337695367080885)
                  ·
                    refine ⟨2566464629844158940663833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27375622718337695367080885 2566464629844158940663833)
                    ·
                      refine ⟨1924848472383119205497875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566464629844158940663833 1924848472383119205497875)
                      ·
                        rfl

theorem cell23_3748629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_3748629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748629 prefixEnd_3748629 := by exact prefixLift 3748629
  have htrace : WordTrace (prefixWord ++ tailWord_3748629) baseStart_3748629 baseEnd_3748629 := by
    simpa [prefixWord, tailWord_3748629, baseEnd_3748629] using wordTrace_append hprefix tailTrace_3748629
  have hstable : (prefixWord ++ tailWord_3748629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748629).length < 2 ^ (prefixWord ++ tailWord_3748629).sum := by decide
  have hdescent : baseEnd_3748629 < baseStart_3748629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748636 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_3748636 : Nat := 118140960795 + 3748636 * 2 ^ 59
def prefixEnd_3748636 : Nat := 4983230072969 + 3 ^ 40 * 3748636 * 2
def baseEnd_3748636 : Nat := 1924852066747700678110343

theorem tailTrace_3748636 : CollatzResearch.WordTrace tailWord_3748636 prefixEnd_3748636 1924852066747700678110343 := by
  unfold tailWord_3748636
  simp only [CollatzResearch.WordTrace]
  refine ⟨68361993623669731451852881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91149324831559641935803841 68361993623669731451852881)
  ·
    refine ⟨51271495217752298588889661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68361993623669731451852881 51271495217752298588889661)
    ·
      refine ⟨19226810706657111970833623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51271495217752298588889661 19226810706657111970833623)
      ·
        refine ⟨28840216059985667956250435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19226810706657111970833623 28840216059985667956250435)
        ·
          refine ⟨43260324089978501934375653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28840216059985667956250435 43260324089978501934375653)
          ·
            refine ⟨8111310766870969112695435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43260324089978501934375653 8111310766870969112695435)
            ·
              refine ⟨12166966150306453669043153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111310766870969112695435 12166966150306453669043153)
              ·
                refine ⟨9125224612729840251782365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12166966150306453669043153 9125224612729840251782365)
                ·
                  refine ⟨3421959229773690094418387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9125224612729840251782365 3421959229773690094418387)
                  ·
                    refine ⟨5132938844660535141627581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3421959229773690094418387 5132938844660535141627581)
                    ·
                      refine ⟨1924852066747700678110343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5132938844660535141627581 1924852066747700678110343)
                      ·
                        rfl

theorem cell23_3748636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_3748636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748636 prefixEnd_3748636 := by exact prefixLift 3748636
  have htrace : WordTrace (prefixWord ++ tailWord_3748636) baseStart_3748636 baseEnd_3748636 := by
    simpa [prefixWord, tailWord_3748636, baseEnd_3748636] using wordTrace_append hprefix tailTrace_3748636
  have hstable : (prefixWord ++ tailWord_3748636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748636).length < 2 ^ (prefixWord ++ tailWord_3748636).sum := by decide
  have hdescent : baseEnd_3748636 < baseStart_3748636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748652 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 1, 6]
def baseStart_3748652 : Nat := 118140960795 + 3748652 * 2 ^ 59
def prefixEnd_3748652 : Nat := 4983230072969 + 3 ^ 40 * 3748652 * 2
def baseEnd_3748652 : Nat := 641620094146057538503423

theorem tailTrace_3748652 : CollatzResearch.WordTrace tailWord_3748652 prefixEnd_3748652 641620094146057538503423 := by
  unfold tailWord_3748652
  simp only [CollatzResearch.WordTrace]
  refine ⟨68362285407640748818144105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91149713876854331757525473 68362285407640748818144105)
  ·
    refine ⟨51271714055730561613608079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68362285407640748818144105 51271714055730561613608079)
    ·
      refine ⟨76907571083595842420412119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51271714055730561613608079 76907571083595842420412119)
      ·
        refine ⟨115361356625393763630618179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76907571083595842420412119 115361356625393763630618179)
        ·
          refine ⟨173042034938090645445927269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115361356625393763630618179 173042034938090645445927269)
          ·
            refine ⟨32445381550891996021111363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173042034938090645445927269 32445381550891996021111363)
            ·
              refine ⟨48668072326337994031667045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32445381550891996021111363 48668072326337994031667045)
              ·
                refine ⟨9125263561188373880937571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48668072326337994031667045 9125263561188373880937571)
                ·
                  refine ⟨13687895341782560821406357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9125263561188373880937571 13687895341782560821406357)
                  ·
                    refine ⟨641620094146057538503423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13687895341782560821406357 641620094146057538503423)
                    ·
                      rfl

theorem cell23_3748652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_3748652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748652 prefixEnd_3748652 := by exact prefixLift 3748652
  have htrace : WordTrace (prefixWord ++ tailWord_3748652) baseStart_3748652 baseEnd_3748652 := by
    simpa [prefixWord, tailWord_3748652, baseEnd_3748652] using wordTrace_append hprefix tailTrace_3748652
  have hstable : (prefixWord ++ tailWord_3748652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748652).length < 2 ^ (prefixWord ++ tailWord_3748652).sum := by decide
  have hdescent : baseEnd_3748652 < baseStart_3748652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748672 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4]
def baseStart_3748672 : Nat := 118140960795 + 3748672 * 2 ^ 59
def prefixEnd_3748672 : Nat := 4983230072969 + 3 ^ 40 * 3748672 * 2
def baseEnd_3748672 : Nat := 1924870552051262537260177

theorem tailTrace_3748672 : CollatzResearch.WordTrace tailWord_3748672 prefixEnd_3748672 1924870552051262537260177 := by
  unfold tailWord_3748672
  simp only [CollatzResearch.WordTrace]
  refine ⟨68362650137604520526008135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91150200183472694034677513 68362650137604520526008135)
  ·
    refine ⟨102543975206406780789012203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68362650137604520526008135 102543975206406780789012203)
    ·
      refine ⟨153815962809610171183518305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102543975206406780789012203 153815962809610171183518305)
      ·
        refine ⟨115361972107207628387638729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153815962809610171183518305 115361972107207628387638729)
        ·
          refine ⟨86521479080405721290729047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115361972107207628387638729 86521479080405721290729047)
          ·
            refine ⟨129782218620608581936093571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86521479080405721290729047 129782218620608581936093571)
            ·
              refine ⟨194673327930912872904140357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129782218620608581936093571 194673327930912872904140357)
              ·
                refine ⟨36501248987046163669526317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194673327930912872904140357 36501248987046163669526317)
                ·
                  refine ⟨13687968370142311376072369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36501248987046163669526317 13687968370142311376072369)
                  ·
                    refine ⟨10265976277606733532054277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13687968370142311376072369 10265976277606733532054277)
                    ·
                      refine ⟨1924870552051262537260177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10265976277606733532054277 1924870552051262537260177)
                      ·
                        rfl

theorem cell23_3748672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_3748672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748672 prefixEnd_3748672 := by exact prefixLift 3748672
  have htrace : WordTrace (prefixWord ++ tailWord_3748672) baseStart_3748672 baseEnd_3748672 := by
    simpa [prefixWord, tailWord_3748672, baseEnd_3748672] using wordTrace_append hprefix tailTrace_3748672
  have hstable : (prefixWord ++ tailWord_3748672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748672).length < 2 ^ (prefixWord ++ tailWord_3748672).sum := by decide
  have hdescent : baseEnd_3748672 < baseStart_3748672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748689 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 6]
def baseStart_3748689 : Nat := 118140960795 + 3748689 * 2 ^ 59
def prefixEnd_3748689 : Nat := 4983230072969 + 3 ^ 40 * 3748689 * 2
def baseEnd_3748689 : Nat := 1924879281222388970747599

theorem tailTrace_3748689 : CollatzResearch.WordTrace tailWord_3748689 prefixEnd_3748689 1924879281222388970747599 := by
  unfold tailWord_3748689
  simp only [CollatzResearch.WordTrace]
  refine ⟨136725920316147452955385121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91150613544098301970256747 136725920316147452955385121)
  ·
    refine ⟨102544440237110589716538841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 136725920316147452955385121 102544440237110589716538841)
    ·
      refine ⟨76908330177832942287404131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102544440237110589716538841 76908330177832942287404131)
      ·
        refine ⟨115362495266749413431106197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76908330177832942287404131 115362495266749413431106197)
        ·
          refine ⟨5407616965628878754583103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115362495266749413431106197 5407616965628878754583103)
          ·
            refine ⟨8111425448443318131874655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5407616965628878754583103 8111425448443318131874655)
            ·
              refine ⟨12167138172664977197811983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111425448443318131874655 12167138172664977197811983)
              ·
                refine ⟨18250707258997465796717975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12167138172664977197811983 18250707258997465796717975)
                ·
                  refine ⟨27376060888496198695076963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18250707258997465796717975 27376060888496198695076963)
                  ·
                    refine ⟨41064091332744298042615445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27376060888496198695076963 41064091332744298042615445)
                    ·
                      refine ⟨1924879281222388970747599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 41064091332744298042615445 1924879281222388970747599)
                      ·
                        rfl

theorem cell23_3748689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_3748689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748689 prefixEnd_3748689 := by exact prefixLift 3748689
  have htrace : WordTrace (prefixWord ++ tailWord_3748689) baseStart_3748689 baseEnd_3748689 := by
    simpa [prefixWord, tailWord_3748689, baseEnd_3748689] using wordTrace_append hprefix tailTrace_3748689
  have hstable : (prefixWord ++ tailWord_3748689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748689).length < 2 ^ (prefixWord ++ tailWord_3748689).sum := by decide
  have hdescent : baseEnd_3748689 < baseStart_3748689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748709 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_3748709 : Nat := 118140960795 + 3748709 * 2 ^ 59
def prefixEnd_3748709 : Nat := 4983230072969 + 3 ^ 40 * 3748709 * 2
def baseEnd_3748709 : Nat := 1924889550835478892497507

theorem tailTrace_3748709 : CollatzResearch.WordTrace tailWord_3748709 prefixEnd_3748709 1924889550835478892497507 := by
  unfold tailWord_3748709
  simp only [CollatzResearch.WordTrace]
  refine ⟨136726649776074996371113181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91151099850716664247408787 136726649776074996371113181)
  ·
    refine ⟨51272493666028123639167443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136726649776074996371113181 51272493666028123639167443)
    ·
      refine ⟨76908740499042185458751165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51272493666028123639167443 76908740499042185458751165)
      ·
        refine ⟨28840777687140819547031687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76908740499042185458751165 28840777687140819547031687)
        ·
          refine ⟨43261166530711229320547531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28840777687140819547031687 43261166530711229320547531)
          ·
            refine ⟨64891749796066843980821297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43261166530711229320547531 64891749796066843980821297)
            ·
              refine ⟨48668812347050132985615973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64891749796066843980821297 48668812347050132985615973)
              ·
                refine ⟨9125402315071899934802995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48668812347050132985615973 9125402315071899934802995)
                ·
                  refine ⟨13688103472607849902204493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9125402315071899934802995 13688103472607849902204493)
                  ·
                    refine ⟨5133038802227943713326685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13688103472607849902204493 5133038802227943713326685)
                    ·
                      refine ⟨1924889550835478892497507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133038802227943713326685 1924889550835478892497507)
                      ·
                        rfl

theorem cell23_3748709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_3748709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748709 prefixEnd_3748709 := by exact prefixLift 3748709
  have htrace : WordTrace (prefixWord ++ tailWord_3748709) baseStart_3748709 baseEnd_3748709 := by
    simpa [prefixWord, tailWord_3748709, baseEnd_3748709] using wordTrace_append hprefix tailTrace_3748709
  have hstable : (prefixWord ++ tailWord_3748709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748709).length < 2 ^ (prefixWord ++ tailWord_3748709).sum := by decide
  have hdescent : baseEnd_3748709 < baseStart_3748709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748743 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_3748743 : Nat := 118140960795 + 3748743 * 2 ^ 59
def prefixEnd_3748743 : Nat := 4983230072969 + 3 ^ 40 * 3748743 * 2
def baseEnd_3748743 : Nat := 1924907009177731759472351

theorem tailTrace_3748743 : CollatzResearch.WordTrace tailWord_3748743 prefixEnd_3748743 1924907009177731759472351 := by
  unfold tailWord_3748743
  simp only [CollatzResearch.WordTrace]
  refine ⟨136727889857951820177850883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91151926571967880118567255 136727889857951820177850883)
  ·
    refine ⟨205091834786927730266776325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 136727889857951820177850883 205091834786927730266776325)
    ·
      refine ⟨38454719022548949425020561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 205091834786927730266776325 38454719022548949425020561)
      ·
        refine ⟨28841039266911712068765421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38454719022548949425020561 28841039266911712068765421)
        ·
          refine ⟨10815389725091892025787033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28841039266911712068765421 10815389725091892025787033)
          ·
            refine ⟨8111542293818919019340275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10815389725091892025787033 8111542293818919019340275)
            ·
              refine ⟨12167313440728378529010413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8111542293818919019340275 12167313440728378529010413)
              ·
                refine ⟨4562742540273141948378905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12167313440728378529010413 4562742540273141948378905)
                ·
                  refine ⟨3422056905204856461284179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4562742540273141948378905 3422056905204856461284179)
                  ·
                    refine ⟨5133085357807284691926269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3422056905204856461284179 5133085357807284691926269)
                    ·
                      refine ⟨1924907009177731759472351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133085357807284691926269 1924907009177731759472351)
                      ·
                        rfl

theorem cell23_3748743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_3748743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748743 prefixEnd_3748743 := by exact prefixLift 3748743
  have htrace : WordTrace (prefixWord ++ tailWord_3748743) baseStart_3748743 baseEnd_3748743 := by
    simpa [prefixWord, tailWord_3748743, baseEnd_3748743] using wordTrace_append hprefix tailTrace_3748743
  have hstable : (prefixWord ++ tailWord_3748743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748743).length < 2 ^ (prefixWord ++ tailWord_3748743).sum := by decide
  have hdescent : baseEnd_3748743 < baseStart_3748743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748789 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 7]
def baseStart_3748789 : Nat := 118140960795 + 3748789 * 2 ^ 59
def prefixEnd_3748789 : Nat := 4983230072969 + 3 ^ 40 * 3748789 * 2
def baseEnd_3748789 : Nat := 213881181031982064388571

theorem tailTrace_3748789 : CollatzResearch.WordTrace tailWord_3748789 prefixEnd_3748789 213881181031982064388571 := by
  unfold tailWord_3748789
  simp only [CollatzResearch.WordTrace]
  refine ⟨136729567615785170034025421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91153045077190113356016947 136729567615785170034025421)
  ·
    refine ⟨51273587855919438762759533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136729567615785170034025421 51273587855919438762759533)
    ·
      refine ⟨19227595445969789536034825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51273587855919438762759533 19227595445969789536034825)
      ·
        refine ⟨14420696584477342152026119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19227595445969789536034825 14420696584477342152026119)
        ·
          refine ⟨21631044876716013228039179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14420696584477342152026119 21631044876716013228039179)
          ·
            refine ⟨32446567315074019842058769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21631044876716013228039179 32446567315074019842058769)
            ·
              refine ⟨24334925486305514881544077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32446567315074019842058769 24334925486305514881544077)
              ·
                refine ⟨9125597057364568080579029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24334925486305514881544077 9125597057364568080579029)
                ·
                  refine ⟨213881181031982064388571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9125597057364568080579029 213881181031982064388571)
                  ·
                    rfl

theorem cell23_3748789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_3748789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748789 prefixEnd_3748789 := by exact prefixLift 3748789
  have htrace : WordTrace (prefixWord ++ tailWord_3748789) baseStart_3748789 baseEnd_3748789 := by
    simpa [prefixWord, tailWord_3748789, baseEnd_3748789] using wordTrace_append hprefix tailTrace_3748789
  have hstable : (prefixWord ++ tailWord_3748789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748789).length < 2 ^ (prefixWord ++ tailWord_3748789).sum := by decide
  have hdescent : baseEnd_3748789 < baseStart_3748789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748834 : List Nat := [3, 3, 3, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3748834 : Nat := 118140960795 + 3748834 * 2 ^ 59
def prefixEnd_3748834 : Nat := 4983230072969 + 3 ^ 40 * 3748834 * 2
def baseEnd_3748834 : Nat := 1924953735917290903434433

theorem tailTrace_3748834 : CollatzResearch.WordTrace tailWord_3748834 prefixEnd_3748834 1924953735917290903434433 := by
  unfold tailWord_3748834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34182802225155535679853389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91154139267081428479609037 34182802225155535679853389)
  ·
    refine ⟨12818550834433325879945021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34182802225155535679853389 12818550834433325879945021)
    ·
      refine ⟨4806956562912497204979383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12818550834433325879945021 4806956562912497204979383)
      ·
        refine ⟨7210434844368745807469075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4806956562912497204979383 7210434844368745807469075)
        ·
          refine ⟨10815652266553118711203613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7210434844368745807469075 10815652266553118711203613)
          ·
            refine ⟨4055869599957419516701355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10815652266553118711203613 4055869599957419516701355)
            ·
              refine ⟨6083804399936129275052033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055869599957419516701355 6083804399936129275052033)
              ·
                refine ⟨4562853299952096956289025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6083804399936129275052033 4562853299952096956289025)
                ·
                  refine ⟨3422139974964072717216769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4562853299952096956289025 3422139974964072717216769)
                  ·
                    refine ⟨2566604981223054537912577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3422139974964072717216769 2566604981223054537912577)
                    ·
                      refine ⟨1924953735917290903434433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2566604981223054537912577 1924953735917290903434433)
                      ·
                        rfl

theorem cell23_3748834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3748834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748834 prefixEnd_3748834 := by exact prefixLift 3748834
  have htrace : WordTrace (prefixWord ++ tailWord_3748834) baseStart_3748834 baseEnd_3748834 := by
    simpa [prefixWord, tailWord_3748834, baseEnd_3748834] using wordTrace_append hprefix tailTrace_3748834
  have hstable : (prefixWord ++ tailWord_3748834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748834).length < 2 ^ (prefixWord ++ tailWord_3748834).sum := by decide
  have hdescent : baseEnd_3748834 < baseStart_3748834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748869 : List Nat := [1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_3748869 : Nat := 118140960795 + 3748869 * 2 ^ 59
def prefixEnd_3748869 : Nat := 4983230072969 + 3 ^ 40 * 3748869 * 2
def baseEnd_3748869 : Nat := 1924971707740198266496771

theorem tailTrace_3748869 : CollatzResearch.WordTrace tailWord_3748869 prefixEnd_3748869 1924971707740198266496771 := by
  unfold tailWord_3748869
  simp only [CollatzResearch.WordTrace]
  refine ⟨136732485455495343696937661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91154990303663562464625107 136732485455495343696937661)
  ·
    refine ⟨51274682045810753886351623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 136732485455495343696937661 51274682045810753886351623)
    ·
      refine ⟨76912023068716130829527435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51274682045810753886351623 76912023068716130829527435)
      ·
        refine ⟨115368034603074196244291153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76912023068716130829527435 115368034603074196244291153)
        ·
          refine ⟨86526025952305647183218365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115368034603074196244291153 86526025952305647183218365)
          ·
            refine ⟨32447259732114617693706887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86526025952305647183218365 32447259732114617693706887)
            ·
              refine ⟨48670889598171926540560331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32447259732114617693706887 48670889598171926540560331)
              ·
                refine ⟨73006334397257889810840497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48670889598171926540560331 73006334397257889810840497)
                ·
                  refine ⟨54754750797943417358130373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73006334397257889810840497 54754750797943417358130373)
                  ·
                    refine ⟨10266515774614390754649445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54754750797943417358130373 10266515774614390754649445)
                    ·
                      refine ⟨1924971707740198266496771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10266515774614390754649445 1924971707740198266496771)
                      ·
                        rfl

theorem cell23_3748869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_3748869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748869 prefixEnd_3748869 := by exact prefixLift 3748869
  have htrace : WordTrace (prefixWord ++ tailWord_3748869) baseStart_3748869 baseEnd_3748869 := by
    simpa [prefixWord, tailWord_3748869, baseEnd_3748869] using wordTrace_append hprefix tailTrace_3748869
  have hstable : (prefixWord ++ tailWord_3748869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748869).length < 2 ^ (prefixWord ++ tailWord_3748869).sum := by decide
  have hdescent : baseEnd_3748869 < baseStart_3748869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3748876 : List Nat := [2, 2, 1, 2, 3, 2, 2, 1, 1, 4, 3]
def baseStart_3748876 : Nat := 118140960795 + 3748876 * 2 ^ 59
def prefixEnd_3748876 : Nat := 4983230072969 + 3 ^ 40 * 3748876 * 2
def baseEnd_3748876 : Nat := 1924975302104779739109239

theorem tailTrace_3748876 : CollatzResearch.WordTrace tailWord_3748876 prefixEnd_3748876 1924975302104779739109239 := by
  unfold tailWord_3748876
  simp only [CollatzResearch.WordTrace]
  refine ⟨68366370383234991946221241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91155160510979989261628321 68366370383234991946221241)
  ·
    refine ⟨51274777787426243959665931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68366370383234991946221241 51274777787426243959665931)
    ·
      refine ⟨76912166681139365939498897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51274777787426243959665931 76912166681139365939498897)
      ·
        refine ⟨57684125010854524454624173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76912166681139365939498897 57684125010854524454624173)
        ·
          refine ⟨21631546879070446670484065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57684125010854524454624173 21631546879070446670484065)
          ·
            refine ⟨16223660159302835002863049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21631546879070446670484065 16223660159302835002863049)
            ·
              refine ⟨12167745119477126252147287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16223660159302835002863049 12167745119477126252147287)
              ·
                refine ⟨18251617679215689378220931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12167745119477126252147287 18251617679215689378220931)
                ·
                  refine ⟨27377426518823534067331397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18251617679215689378220931 27377426518823534067331397)
                  ·
                    refine ⟨5133267472279412637624637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27377426518823534067331397 5133267472279412637624637)
                    ·
                      refine ⟨1924975302104779739109239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5133267472279412637624637 1924975302104779739109239)
                      ·
                        rfl

theorem cell23_3748876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_3748876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3748876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3748876 prefixEnd_3748876 := by exact prefixLift 3748876
  have htrace : WordTrace (prefixWord ++ tailWord_3748876) baseStart_3748876 baseEnd_3748876 := by
    simpa [prefixWord, tailWord_3748876, baseEnd_3748876] using wordTrace_append hprefix tailTrace_3748876
  have hstable : (prefixWord ++ tailWord_3748876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3748876).length < 2 ^ (prefixWord ++ tailWord_3748876).sum := by decide
  have hdescent : baseEnd_3748876 < baseStart_3748876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3748876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
