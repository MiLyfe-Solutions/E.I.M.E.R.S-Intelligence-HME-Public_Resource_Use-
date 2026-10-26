import V185TrunkScan20Chunk168

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1029281 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_1029281 : Nat := 118140960795 + 1029281 * 2 ^ 59
def prefixEnd_1029281 : Nat := 4983230072969 + 3 ^ 40 * 1029281 * 2
def baseEnd_1029281 : Nat := 469791894702660148492381

theorem tailTrace_1029281 : CollatzResearch.WordTrace tailWord_1029281 prefixEnd_1029281 469791894702660148492381 := by
  unfold tailWord_1029281
  simp only [CollatzResearch.WordTrace]
  refine ⟨37540962184098199044775697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25027308122732132696517131 37540962184098199044775697)
  ·
    refine ⟨28155721638073649283581773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37540962184098199044775697 28155721638073649283581773)
    ·
      refine ⟨10558395614277618481343165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28155721638073649283581773 10558395614277618481343165)
      ·
        refine ⟨3959398355354106930503687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10558395614277618481343165 3959398355354106930503687)
        ·
          refine ⟨5939097533031160395755531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3959398355354106930503687 5939097533031160395755531)
          ·
            refine ⟨8908646299546740593633297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5939097533031160395755531 8908646299546740593633297)
            ·
              refine ⟨6681484724660055445224973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8908646299546740593633297 6681484724660055445224973)
              ·
                refine ⟨2505556771747520791959365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6681484724660055445224973 2505556771747520791959365)
                ·
                  refine ⟨469791894702660148492381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505556771747520791959365 469791894702660148492381)
                  ·
                    rfl

theorem cell20_1029281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_1029281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029281 prefixEnd_1029281 := by exact prefixLift 1029281
  have htrace : WordTrace (prefixWord ++ tailWord_1029281) baseStart_1029281 baseEnd_1029281 := by
    simpa [prefixWord, tailWord_1029281, baseEnd_1029281] using wordTrace_append hprefix tailTrace_1029281
  have hstable : (prefixWord ++ tailWord_1029281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029281).length < 2 ^ (prefixWord ++ tailWord_1029281).sum := by decide
  have hdescent : baseEnd_1029281 < baseStart_1029281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029305 : List Nat := [1, 2, 1, 4, 1, 4, 3, 4]
def baseStart_1029305 : Nat := 118140960795 + 1029305 * 2 ^ 59
def prefixEnd_1029305 : Nat := 4983230072969 + 3 ^ 40 * 1029305 * 2
def baseEnd_1029305 : Nat := 156600949652207577230761

theorem tailTrace_1029305 : CollatzResearch.WordTrace tailWord_1029305 prefixEnd_1029305 156600949652207577230761 := by
  unfold tailWord_1029305
  simp only [CollatzResearch.WordTrace]
  refine ⟨37541837536011251143649369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25027891690674167429099579 37541837536011251143649369)
  ·
    refine ⟨28156378152008438357737027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37541837536011251143649369 28156378152008438357737027)
    ·
      refine ⟨42234567228012657536605541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28156378152008438357737027 42234567228012657536605541)
      ·
        refine ⟨7918981355252373288113539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42234567228012657536605541 7918981355252373288113539)
        ·
          refine ⟨11878472032878559932170309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7918981355252373288113539 11878472032878559932170309)
          ·
            refine ⟨2227213506164729987281933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11878472032878559932170309 2227213506164729987281933)
            ·
              refine ⟨835205064811773745230725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2227213506164729987281933 835205064811773745230725)
              ·
                refine ⟨156600949652207577230761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 835205064811773745230725 156600949652207577230761)
                ·
                  rfl

theorem cell20_1029305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 4].length) (baseStart_1029305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029305 prefixEnd_1029305 := by exact prefixLift 1029305
  have htrace : WordTrace (prefixWord ++ tailWord_1029305) baseStart_1029305 baseEnd_1029305 := by
    simpa [prefixWord, tailWord_1029305, baseEnd_1029305] using wordTrace_append hprefix tailTrace_1029305
  have hstable : (prefixWord ++ tailWord_1029305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029305).length < 2 ^ (prefixWord ++ tailWord_1029305).sum := by decide
  have hdescent : baseEnd_1029305 < baseStart_1029305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029336 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_1029336 : Nat := 118140960795 + 1029336 * 2 ^ 59
def prefixEnd_1029336 : Nat := 4983230072969 + 3 ^ 40 * 1029336 * 2
def baseEnd_1029336 : Nat := 469816998201324401658823

theorem tailTrace_1029336 : CollatzResearch.WordTrace tailWord_1029336 prefixEnd_1029336 469816998201324401658823 := by
  unfold tailWord_1029336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18771484099449471719013931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25028645465932628958685241 18771484099449471719013931)
  ·
    refine ⟨28157226149174207578520897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18771484099449471719013931 28157226149174207578520897)
    ·
      refine ⟨21117919611880655683890673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28157226149174207578520897 21117919611880655683890673)
      ·
        refine ⟨15838439708910491762918005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21117919611880655683890673 15838439708910491762918005)
        ·
          refine ⟨1484853722710358602773563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15838439708910491762918005 1484853722710358602773563)
          ·
            refine ⟨2227280584065537904160345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1484853722710358602773563 2227280584065537904160345)
            ·
              refine ⟨1670460438049153428120259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227280584065537904160345 1670460438049153428120259)
              ·
                refine ⟨2505690657073730142180389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1670460438049153428120259 2505690657073730142180389)
                ·
                  refine ⟨469816998201324401658823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2505690657073730142180389 469816998201324401658823)
                  ·
                    rfl

theorem cell20_1029336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_1029336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029336 prefixEnd_1029336 := by exact prefixLift 1029336
  have htrace : WordTrace (prefixWord ++ tailWord_1029336) baseStart_1029336 baseEnd_1029336 := by
    simpa [prefixWord, tailWord_1029336, baseEnd_1029336] using wordTrace_append hprefix tailTrace_1029336
  have hstable : (prefixWord ++ tailWord_1029336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029336).length < 2 ^ (prefixWord ++ tailWord_1029336).sum := by decide
  have hdescent : baseEnd_1029336 < baseStart_1029336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029402 : List Nat := [3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1029402 : Nat := 118140960795 + 1029402 * 2 ^ 59
def prefixEnd_1029402 : Nat := 4983230072969 + 3 ^ 40 * 1029402 * 2
def baseEnd_1029402 : Nat := 156615707466573835152851

theorem tailTrace_1029402 : CollatzResearch.WordTrace tailWord_1029402 prefixEnd_1029402 156615707466573835152851 := by
  unfold tailWord_1029402
  simp only [CollatzResearch.WordTrace]
  refine ⟨9386343854164959177482615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25030250277773224473286973 9386343854164959177482615)
  ·
    refine ⟨14079515781247438766223923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9386343854164959177482615 14079515781247438766223923)
    ·
      refine ⟨21119273671871158149335885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14079515781247438766223923 21119273671871158149335885)
      ·
        refine ⟨7919727626951684306000957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21119273671871158149335885 7919727626951684306000957)
        ·
          refine ⟨2969897860106881614750359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7919727626951684306000957 2969897860106881614750359)
          ·
            refine ⟨4454846790160322422125539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969897860106881614750359 4454846790160322422125539)
            ·
              refine ⟨6682270185240483633188309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4454846790160322422125539 6682270185240483633188309)
              ·
                refine ⟨156615707466573835152851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6682270185240483633188309 156615707466573835152851)
                ·
                  rfl

theorem cell20_1029402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1029402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029402 prefixEnd_1029402 := by exact prefixLift 1029402
  have htrace : WordTrace (prefixWord ++ tailWord_1029402) baseStart_1029402 baseEnd_1029402 := by
    simpa [prefixWord, tailWord_1029402, baseEnd_1029402] using wordTrace_append hprefix tailTrace_1029402
  have hstable : (prefixWord ++ tailWord_1029402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029402).length < 2 ^ (prefixWord ++ tailWord_1029402).sum := by decide
  have hdescent : baseEnd_1029402 < baseStart_1029402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029405 : List Nat := [1, 4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1029405 : Nat := 118140960795 + 1029405 * 2 ^ 59
def prefixEnd_1029405 : Nat := 4983230072969 + 3 ^ 40 * 1029405 * 2
def baseEnd_1029405 : Nat := 469848491681466828358541

theorem tailTrace_1029405 : CollatzResearch.WordTrace tailWord_1029405 prefixEnd_1029405 469848491681466828358541 := by
  unfold tailWord_1029405
  simp only [CollatzResearch.WordTrace]
  refine ⟨37545484835648968222289669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25030323223765978814859779 37545484835648968222289669)
  ·
    refine ⟨7039778406684181541679313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37545484835648968222289669 7039778406684181541679313)
    ·
      refine ⟨5279833805013136156259485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7039778406684181541679313 5279833805013136156259485)
      ·
        refine ⟨1979937676879926058597307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5279833805013136156259485 1979937676879926058597307)
        ·
          refine ⟨2969906515319889087895961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979937676879926058597307 2969906515319889087895961)
          ·
            refine ⟨2227429886489916815921971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2969906515319889087895961 2227429886489916815921971)
            ·
              refine ⟨3341144829734875223882957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227429886489916815921971 3341144829734875223882957)
              ·
                refine ⟨1252929311150578208956109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3341144829734875223882957 1252929311150578208956109)
                ·
                  refine ⟨469848491681466828358541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1252929311150578208956109 469848491681466828358541)
                  ·
                    rfl

theorem cell20_1029405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1029405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029405 prefixEnd_1029405 := by exact prefixLift 1029405
  have htrace : WordTrace (prefixWord ++ tailWord_1029405) baseStart_1029405 baseEnd_1029405 := by
    simpa [prefixWord, tailWord_1029405, baseEnd_1029405] using wordTrace_append hprefix tailTrace_1029405
  have hstable : (prefixWord ++ tailWord_1029405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029405).length < 2 ^ (prefixWord ++ tailWord_1029405).sum := by decide
  have hdescent : baseEnd_1029405 < baseStart_1029405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029453 : List Nat := [1, 6, 1, 3, 1, 2, 1, 5]
def baseStart_1029453 : Nat := 118140960795 + 1029453 * 2 ^ 59
def prefixEnd_1029453 : Nat := 4983230072969 + 3 ^ 40 * 1029453 * 2
def baseEnd_1029453 : Nat := 156623466729797331586115

theorem tailTrace_1029453 : CollatzResearch.WordTrace tailWord_1029453 prefixEnd_1029453 156623466729797331586115 := by
  unfold tailWord_1029453
  simp only [CollatzResearch.WordTrace]
  refine ⟨37547235539475072420037013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25031490359650048280024675 37547235539475072420037013)
  ·
    refine ⟨1760026665912894019689235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37547235539475072420037013 1760026665912894019689235)
    ·
      refine ⟨2640039998869341029533853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760026665912894019689235 2640039998869341029533853)
      ·
        refine ⟨990014999576002886075195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2640039998869341029533853 990014999576002886075195)
        ·
          refine ⟨1485022499364004329112793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990014999576002886075195 1485022499364004329112793)
          ·
            refine ⟨1113766874523003246834595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1485022499364004329112793 1113766874523003246834595)
            ·
              refine ⟨1670650311784504870251893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113766874523003246834595 1670650311784504870251893)
              ·
                refine ⟨156623466729797331586115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1670650311784504870251893 156623466729797331586115)
                ·
                  rfl

theorem cell20_1029453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_1029453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029453 prefixEnd_1029453 := by exact prefixLift 1029453
  have htrace : WordTrace (prefixWord ++ tailWord_1029453) baseStart_1029453 baseEnd_1029453 := by
    simpa [prefixWord, tailWord_1029453, baseEnd_1029453] using wordTrace_append hprefix tailTrace_1029453
  have hstable : (prefixWord ++ tailWord_1029453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029453).length < 2 ^ (prefixWord ++ tailWord_1029453).sum := by decide
  have hdescent : baseEnd_1029453 < baseStart_1029453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029488 : List Nat := [2, 1, 1, 1, 4, 2, 4, 3, 2]
def baseStart_1029488 : Nat := 118140960795 + 1029488 * 2 ^ 59
def prefixEnd_1029488 : Nat := 4983230072969 + 3 ^ 40 * 1029488 * 2
def baseEnd_1029488 : Nat := 469886375143087428591535

theorem tailTrace_1029488 : CollatzResearch.WordTrace tailWord_1029488 prefixEnd_1029488 469886375143087428591535 := by
  unfold tailWord_1029488
  simp only [CollatzResearch.WordTrace]
  refine ⟨18774256047174136698780559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25032341396232182265040745 18774256047174136698780559)
  ·
    refine ⟨28161384070761205048170839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18774256047174136698780559 28161384070761205048170839)
    ·
      refine ⟨42242076106141807572256259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28161384070761205048170839 42242076106141807572256259)
      ·
        refine ⟨63363114159212711358384389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42242076106141807572256259 63363114159212711358384389)
        ·
          refine ⟨11880583904852383379697073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63363114159212711358384389 11880583904852383379697073)
          ·
            refine ⟨8910437928639287534772805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11880583904852383379697073 8910437928639287534772805)
            ·
              refine ⟨1670707111619866412769901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8910437928639287534772805 1670707111619866412769901)
              ·
                refine ⟨626515166857449904788713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1670707111619866412769901 626515166857449904788713)
                ·
                  refine ⟨469886375143087428591535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626515166857449904788713 469886375143087428591535)
                  ·
                    rfl

theorem cell20_1029488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_1029488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029488 prefixEnd_1029488 := by exact prefixLift 1029488
  have htrace : WordTrace (prefixWord ++ tailWord_1029488) baseStart_1029488 baseEnd_1029488 := by
    simpa [prefixWord, tailWord_1029488, baseEnd_1029488] using wordTrace_append hprefix tailTrace_1029488
  have hstable : (prefixWord ++ tailWord_1029488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029488).length < 2 ^ (prefixWord ++ tailWord_1029488).sum := by decide
  have hdescent : baseEnd_1029488 < baseStart_1029488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029499 : List Nat := [1, 1, 1, 1, 1, 6, 9]
def baseStart_1029499 : Nat := 118140960795 + 1029499 * 2 ^ 59
def prefixEnd_1029499 : Nat := 4983230072969 + 3 ^ 40 * 1029499 * 2
def baseEnd_1029499 : Nat := 52210155093646697691647

theorem tailTrace_1029499 : CollatzResearch.WordTrace tailWord_1029499 prefixEnd_1029499 52210155093646697691647 := by
  unfold tailWord_1029499
  simp only [CollatzResearch.WordTrace]
  refine ⟨37548913297308422276211551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25032608864872281517474367 37548913297308422276211551)
  ·
    refine ⟨56323369945962633414317327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37548913297308422276211551 56323369945962633414317327)
    ·
      refine ⟨84485054918943950121475991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56323369945962633414317327 84485054918943950121475991)
      ·
        refine ⟨126727582378415925182213987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84485054918943950121475991 126727582378415925182213987)
        ·
          refine ⟨190091373567623887773320981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126727582378415925182213987 190091373567623887773320981)
          ·
            refine ⟨8910533135982369739374421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 190091373567623887773320981 8910533135982369739374421)
            ·
              refine ⟨52210155093646697691647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8910533135982369739374421 52210155093646697691647)
              ·
                rfl

theorem cell20_1029499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_1029499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029499 prefixEnd_1029499 := by exact prefixLift 1029499
  have htrace : WordTrace (prefixWord ++ tailWord_1029499) baseStart_1029499 baseEnd_1029499 := by
    simpa [prefixWord, tailWord_1029499, baseEnd_1029499] using wordTrace_append hprefix tailTrace_1029499
  have hstable : (prefixWord ++ tailWord_1029499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029499).length < 2 ^ (prefixWord ++ tailWord_1029499).sum := by decide
  have hdescent : baseEnd_1029499 < baseStart_1029499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029533 : List Nat := [1, 4, 2, 1, 3, 1, 4, 4]
def baseStart_1029533 : Nat := 118140960795 + 1029533 * 2 ^ 59
def prefixEnd_1029533 : Nat := 4983230072969 + 3 ^ 40 * 1029533 * 2
def baseEnd_1029533 : Nat := 156635638123089090697117

theorem tailTrace_1029533 : CollatzResearch.WordTrace tailWord_1029533 prefixEnd_1029533 156635638123089090697117 := by
  unfold tailWord_1029533
  simp only [CollatzResearch.WordTrace]
  refine ⟨37550153379185246082949253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25033435586123497388632835 37550153379185246082949253)
  ·
    refine ⟨7040653758597233640552985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37550153379185246082949253 7040653758597233640552985)
    ·
      refine ⟨5280490318947925230414739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7040653758597233640552985 5280490318947925230414739)
      ·
        refine ⟨7920735478421887845622109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5280490318947925230414739 7920735478421887845622109)
        ·
          refine ⟨2970275804408207942108291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7920735478421887845622109 2970275804408207942108291)
          ·
            refine ⟨4455413706612311913162437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970275804408207942108291 4455413706612311913162437)
            ·
              refine ⟨835390069989808483717957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4455413706612311913162437 835390069989808483717957)
              ·
                refine ⟨156635638123089090697117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 835390069989808483717957 156635638123089090697117)
                ·
                  rfl

theorem cell20_1029533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 4].length) (baseStart_1029533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029533 prefixEnd_1029533 := by exact prefixLift 1029533
  have htrace : WordTrace (prefixWord ++ tailWord_1029533) baseStart_1029533 baseEnd_1029533 := by
    simpa [prefixWord, tailWord_1029533, baseEnd_1029533] using wordTrace_append hprefix tailTrace_1029533
  have hstable : (prefixWord ++ tailWord_1029533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029533).length < 2 ^ (prefixWord ++ tailWord_1029533).sum := by decide
  have hdescent : baseEnd_1029533 < baseStart_1029533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029570 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_1029570 : Nat := 118140960795 + 1029570 * 2 ^ 59
def prefixEnd_1029570 : Nat := 4983230072969 + 3 ^ 40 * 1029570 * 2
def baseEnd_1029570 : Nat := 469923802177459587857867

theorem tailTrace_1029570 : CollatzResearch.WordTrace tailWord_1029570 prefixEnd_1029570 469923802177459587857867 := by
  unfold tailWord_1029570
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387875720012800350511541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25034335253367467601364109 9387875720012800350511541)
  ·
    refine ⟨880113348751200032860457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9387875720012800350511541 880113348751200032860457)
    ·
      refine ⟨660085011563400024645343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 880113348751200032860457 660085011563400024645343)
      ·
        refine ⟨990127517345100036968015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660085011563400024645343 990127517345100036968015)
        ·
          refine ⟨1485191276017650055452023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990127517345100036968015 1485191276017650055452023)
          ·
            refine ⟨2227786914026475083178035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485191276017650055452023 2227786914026475083178035)
            ·
              refine ⟨3341680371039712624767053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227786914026475083178035 3341680371039712624767053)
              ·
                refine ⟨1253130139139892234287645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3341680371039712624767053 1253130139139892234287645)
                ·
                  refine ⟨469923802177459587857867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253130139139892234287645 469923802177459587857867)
                  ·
                    rfl

theorem cell20_1029570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_1029570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029570 prefixEnd_1029570 := by exact prefixLift 1029570
  have htrace : WordTrace (prefixWord ++ tailWord_1029570) baseStart_1029570 baseEnd_1029570 := by
    simpa [prefixWord, tailWord_1029570, baseEnd_1029570] using wordTrace_append hprefix tailTrace_1029570
  have hstable : (prefixWord ++ tailWord_1029570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029570).length < 2 ^ (prefixWord ++ tailWord_1029570).sum := by decide
  have hdescent : baseEnd_1029570 < baseStart_1029570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029578 : List Nat := [3, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1029578 : Nat := 118140960795 + 1029578 * 2 ^ 59
def prefixEnd_1029578 : Nat := 4983230072969 + 3 ^ 40 * 1029578 * 2
def baseEnd_1029578 : Nat := 469927453595447115591167

theorem tailTrace_1029578 : CollatzResearch.WordTrace tailWord_1029578 prefixEnd_1029578 469927453595447115591167 := by
  unfold tailWord_1029578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9387948666005554692084347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25034529776014812512224925 9387948666005554692084347)
  ·
    refine ⟨14081922999008332038126521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9387948666005554692084347 14081922999008332038126521)
    ·
      refine ⟨10561442249256249028594891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14081922999008332038126521 10561442249256249028594891)
      ·
        refine ⟨15842163373884373542892337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10561442249256249028594891 15842163373884373542892337)
        ·
          refine ⟨11881622530413280157169253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15842163373884373542892337 11881622530413280157169253)
          ·
            refine ⟨2227804224452490029469235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11881622530413280157169253 2227804224452490029469235)
            ·
              refine ⟨3341706336678735044203853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2227804224452490029469235 3341706336678735044203853)
              ·
                refine ⟨1253139876254525641576445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3341706336678735044203853 1253139876254525641576445)
                ·
                  refine ⟨469927453595447115591167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253139876254525641576445 469927453595447115591167)
                  ·
                    rfl

theorem cell20_1029578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1029578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029578 prefixEnd_1029578 := by exact prefixLift 1029578
  have htrace : WordTrace (prefixWord ++ tailWord_1029578) baseStart_1029578 baseEnd_1029578 := by
    simpa [prefixWord, tailWord_1029578, baseEnd_1029578] using wordTrace_append hprefix tailTrace_1029578
  have hstable : (prefixWord ++ tailWord_1029578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029578).length < 2 ^ (prefixWord ++ tailWord_1029578).sum := by decide
  have hdescent : baseEnd_1029578 < baseStart_1029578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029616 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1029616 : Nat := 118140960795 + 1029616 * 2 ^ 59
def prefixEnd_1029616 : Nat := 4983230072969 + 3 ^ 40 * 1029616 * 2
def baseEnd_1029616 : Nat := 469944797830887872324345

theorem tailTrace_1029616 : CollatzResearch.WordTrace tailWord_1029616 prefixEnd_1029616 469944797830887872324345 := by
  unfold tailWord_1029616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776590318942275629110351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25035453758589700838813801 18776590318942275629110351)
  ·
    refine ⟨28164885478413413443665527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18776590318942275629110351 28164885478413413443665527)
    ·
      refine ⟨42247328217620120165498291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28164885478413413443665527 42247328217620120165498291)
      ·
        refine ⟨63370992326430180248247437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42247328217620120165498291 63370992326430180248247437)
        ·
          refine ⟨23764122122411317593092789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63370992326430180248247437 23764122122411317593092789)
          ·
            refine ⟨2227886448976061024352449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23764122122411317593092789 2227886448976061024352449)
            ·
              refine ⟨1670914836732045768264337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227886448976061024352449 1670914836732045768264337)
              ·
                refine ⟨1253186127549034326198253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670914836732045768264337 1253186127549034326198253)
                ·
                  refine ⟨469944797830887872324345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253186127549034326198253 469944797830887872324345)
                  ·
                    rfl

theorem cell20_1029616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1029616 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029616 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029616 prefixEnd_1029616 := by exact prefixLift 1029616
  have htrace : WordTrace (prefixWord ++ tailWord_1029616) baseStart_1029616 baseEnd_1029616 := by
    simpa [prefixWord, tailWord_1029616, baseEnd_1029616] using wordTrace_append hprefix tailTrace_1029616
  have hstable : (prefixWord ++ tailWord_1029616).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029616).length < 2 ^ (prefixWord ++ tailWord_1029616).sum := by decide
  have hdescent : baseEnd_1029616 < baseStart_1029616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029678 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1029678 : Nat := 118140960795 + 1029678 * 2 ^ 59
def prefixEnd_1029678 : Nat := 4983230072969 + 3 ^ 40 * 1029678 * 2
def baseEnd_1029678 : Nat := 469973096320291212257425

theorem tailTrace_1029678 : CollatzResearch.WordTrace tailWord_1029678 prefixEnd_1029678 469973096320291212257425 := by
  unfold tailWord_1029678
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694430245457491980872211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25036961309106623897985125 4694430245457491980872211)
  ·
    refine ⟨7041645368186237971308317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4694430245457491980872211 7041645368186237971308317)
    ·
      refine ⟨2640617013069839239240619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7041645368186237971308317 2640617013069839239240619)
      ·
        refine ⟨3960925519604758858860929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640617013069839239240619 3960925519604758858860929)
        ·
          refine ⟨2970694139703569144145697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3960925519604758858860929 2970694139703569144145697)
          ·
            refine ⟨2228020604777676858109273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970694139703569144145697 2228020604777676858109273)
            ·
              refine ⟨1671015453583257643581955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228020604777676858109273 1671015453583257643581955)
              ·
                refine ⟨2506523180374886465372933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671015453583257643581955 2506523180374886465372933)
                ·
                  refine ⟨469973096320291212257425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2506523180374886465372933 469973096320291212257425)
                  ·
                    rfl

theorem cell20_1029678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1029678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029678 prefixEnd_1029678 := by exact prefixLift 1029678
  have htrace : WordTrace (prefixWord ++ tailWord_1029678) baseStart_1029678 baseEnd_1029678 := by
    simpa [prefixWord, tailWord_1029678, baseEnd_1029678] using wordTrace_append hprefix tailTrace_1029678
  have hstable : (prefixWord ++ tailWord_1029678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029678).length < 2 ^ (prefixWord ++ tailWord_1029678).sum := by decide
  have hdescent : baseEnd_1029678 < baseStart_1029678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029702 : List Nat := [6, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1029702 : Nat := 118140960795 + 1029702 * 2 ^ 59
def prefixEnd_1029702 : Nat := 4983230072969 + 3 ^ 40 * 1029702 * 2
def baseEnd_1029702 : Nat := 156661350191417931819109

theorem tailTrace_1029702 : CollatzResearch.WordTrace tailWord_1029702 prefixEnd_1029702 156661350191417931819109 := by
  unfold tailWord_1029702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1173634916111655873307855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 25037544877048658630567573 1173634916111655873307855)
  ·
    refine ⟨1760452374167483809961783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1173634916111655873307855 1760452374167483809961783)
    ·
      refine ⟨2640678561251225714942675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760452374167483809961783 2640678561251225714942675)
      ·
        refine ⟨3961017841876838572414013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2640678561251225714942675 3961017841876838572414013)
        ·
          refine ⟨1485381690703814464655255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3961017841876838572414013 1485381690703814464655255)
          ·
            refine ⟨2228072536055721696982883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485381690703814464655255 2228072536055721696982883)
            ·
              refine ⟨3342108804083582545474325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228072536055721696982883 3342108804083582545474325)
              ·
                refine ⟨156661350191417931819109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3342108804083582545474325 156661350191417931819109)
                ·
                  rfl

theorem cell20_1029702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1029702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029702 prefixEnd_1029702 := by exact prefixLift 1029702
  have htrace : WordTrace (prefixWord ++ tailWord_1029702) baseStart_1029702 baseEnd_1029702 := by
    simpa [prefixWord, tailWord_1029702, baseEnd_1029702] using wordTrace_append hprefix tailTrace_1029702
  have hstable : (prefixWord ++ tailWord_1029702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029702).length < 2 ^ (prefixWord ++ tailWord_1029702).sum := by decide
  have hdescent : baseEnd_1029702 < baseStart_1029702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029733 : List Nat := [1, 3, 1, 3, 3, 2, 3, 2, 2]
def baseStart_1029733 : Nat := 118140960795 + 1029733 * 2 ^ 59
def prefixEnd_1029733 : Nat := 4983230072969 + 3 ^ 40 * 1029733 * 2
def baseEnd_1029733 : Nat := 469998199818955465423867

theorem tailTrace_1029733 : CollatzResearch.WordTrace tailWord_1029733 prefixEnd_1029733 469998199818955465423867 := by
  unfold tailWord_1029733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37557447978460680240229853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25038298652307120160153235 37557447978460680240229853)
  ·
    refine ⟨14084042991922755090086195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37557447978460680240229853 14084042991922755090086195)
    ·
      refine ⟨21126064487884132635129293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14084042991922755090086195 21126064487884132635129293)
      ·
        refine ⟨7922274182956549738173485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21126064487884132635129293 7922274182956549738173485)
        ·
          refine ⟨2970852818608706151815057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7922274182956549738173485 2970852818608706151815057)
          ·
            refine ⟨2228139613956529613861293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970852818608706151815057 2228139613956529613861293)
            ·
              refine ⟨835552355233698605197985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2228139613956529613861293 835552355233698605197985)
              ·
                refine ⟨626664266425273953898489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835552355233698605197985 626664266425273953898489)
                ·
                  refine ⟨469998199818955465423867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626664266425273953898489 469998199818955465423867)
                  ·
                    rfl

theorem cell20_1029733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_1029733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029733 prefixEnd_1029733 := by exact prefixLift 1029733
  have htrace : WordTrace (prefixWord ++ tailWord_1029733) baseStart_1029733 baseEnd_1029733 := by
    simpa [prefixWord, tailWord_1029733, baseEnd_1029733] using wordTrace_append hprefix tailTrace_1029733
  have hstable : (prefixWord ++ tailWord_1029733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029733).length < 2 ^ (prefixWord ++ tailWord_1029733).sum := by decide
  have hdescent : baseEnd_1029733 < baseStart_1029733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029737 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 2]
def baseStart_1029737 : Nat := 118140960795 + 1029737 * 2 ^ 59
def prefixEnd_1029737 : Nat := 4983230072969 + 3 ^ 40 * 1029737 * 2
def baseEnd_1029737 : Nat := 470000025527949229290517

theorem tailTrace_1029737 : CollatzResearch.WordTrace tailWord_1029737 prefixEnd_1029737 470000025527949229290517 := by
  unfold tailWord_1029737
  simp only [CollatzResearch.WordTrace]
  refine ⟨37557593870446188923375465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25038395913630792615583643 37557593870446188923375465)
  ·
    refine ⟨28168195402834641692531599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37557593870446188923375465 28168195402834641692531599)
    ·
      refine ⟨42252293104251962538797399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28168195402834641692531599 42252293104251962538797399)
      ·
        refine ⟨63378439656377943808196099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42252293104251962538797399 63378439656377943808196099)
        ·
          refine ⟨95067659484566915712294149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63378439656377943808196099 95067659484566915712294149)
          ·
            refine ⟨17825186153356296696055153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95067659484566915712294149 17825186153356296696055153)
            ·
              refine ⟨13368889615017222522041365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17825186153356296696055153 13368889615017222522041365)
              ·
                refine ⟨626666700703932305720689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13368889615017222522041365 626666700703932305720689)
                ·
                  refine ⟨470000025527949229290517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626666700703932305720689 470000025527949229290517)
                  ·
                    rfl

theorem cell20_1029737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_1029737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029737 prefixEnd_1029737 := by exact prefixLift 1029737
  have htrace : WordTrace (prefixWord ++ tailWord_1029737) baseStart_1029737 baseEnd_1029737 := by
    simpa [prefixWord, tailWord_1029737, baseEnd_1029737] using wordTrace_append hprefix tailTrace_1029737
  have hstable : (prefixWord ++ tailWord_1029737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029737).length < 2 ^ (prefixWord ++ tailWord_1029737).sum := by decide
  have hdescent : baseEnd_1029737 < baseStart_1029737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029744 : List Nat := [2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_1029744 : Nat := 118140960795 + 1029744 * 2 ^ 59
def prefixEnd_1029744 : Nat := 4983230072969 + 3 ^ 40 * 1029744 * 2
def baseEnd_1029744 : Nat := 156667740172896105352385

theorem tailTrace_1029744 : CollatzResearch.WordTrace tailWord_1029744 prefixEnd_1029744 156667740172896105352385 := by
  unfold tailWord_1029744
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778924590710414559440143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25038566120947219412586857 18778924590710414559440143)
  ·
    refine ⟨28168386886065621839160215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18778924590710414559440143 28168386886065621839160215)
    ·
      refine ⟨42252580329098432758740323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28168386886065621839160215 42252580329098432758740323)
      ·
        refine ⟨63378870493647649138110485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42252580329098432758740323 63378870493647649138110485)
        ·
          refine ⟨2970884554389733553348929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63378870493647649138110485 2970884554389733553348929)
          ·
            refine ⟨2228163415792300165011697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970884554389733553348929 2228163415792300165011697)
            ·
              refine ⟨1671122561844225123758773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228163415792300165011697 1671122561844225123758773)
              ·
                refine ⟨156667740172896105352385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1671122561844225123758773 156667740172896105352385)
                ·
                  rfl

theorem cell20_1029744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_1029744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029744 prefixEnd_1029744 := by exact prefixLift 1029744
  have htrace : WordTrace (prefixWord ++ tailWord_1029744) baseStart_1029744 baseEnd_1029744 := by
    simpa [prefixWord, tailWord_1029744, baseEnd_1029744] using wordTrace_append hprefix tailTrace_1029744
  have hstable : (prefixWord ++ tailWord_1029744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029744).length < 2 ^ (prefixWord ++ tailWord_1029744).sum := by decide
  have hdescent : baseEnd_1029744 < baseStart_1029744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029765 : List Nat := [1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_1029765 : Nat := 118140960795 + 1029765 * 2 ^ 59
def prefixEnd_1029765 : Nat := 4983230072969 + 3 ^ 40 * 1029765 * 2
def baseEnd_1029765 : Nat := 156670935163635192119023

theorem tailTrace_1029765 : CollatzResearch.WordTrace tailWord_1029765 prefixEnd_1029765 156670935163635192119023 := by
  unfold tailWord_1029765
  simp only [CollatzResearch.WordTrace]
  refine ⟨37558615114344749705394749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25039076742896499803596499 37558615114344749705394749)
  ·
    refine ⟨14084480667879281139523031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37558615114344749705394749 14084480667879281139523031)
    ·
      refine ⟨21126721001818921709284547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14084480667879281139523031 21126721001818921709284547)
      ·
        refine ⟨31690081502728382563926821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21126721001818921709284547 31690081502728382563926821)
        ·
          refine ⟨5941890281761571730736279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31690081502728382563926821 5941890281761571730736279)
          ·
            refine ⟨8912835422642357596104419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5941890281761571730736279 8912835422642357596104419)
            ·
              refine ⟨13369253133963536394156629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8912835422642357596104419 13369253133963536394156629)
              ·
                refine ⟨156670935163635192119023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13369253133963536394156629 156670935163635192119023)
                ·
                  rfl

theorem cell20_1029765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_1029765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029765 prefixEnd_1029765 := by exact prefixLift 1029765
  have htrace : WordTrace (prefixWord ++ tailWord_1029765) baseStart_1029765 baseEnd_1029765 := by
    simpa [prefixWord, tailWord_1029765, baseEnd_1029765] using wordTrace_append hprefix tailTrace_1029765
  have hstable : (prefixWord ++ tailWord_1029765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029765).length < 2 ^ (prefixWord ++ tailWord_1029765).sum := by decide
  have hdescent : baseEnd_1029765 < baseStart_1029765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029782 : List Nat := [5, 3, 12]
def baseStart_1029782 : Nat := 118140960795 + 1029782 * 2 ^ 59
def prefixEnd_1029782 : Nat := 4983230072969 + 3 ^ 40 * 1029782 * 2
def baseEnd_1029782 : Nat := 644747002406212719877

theorem tailTrace_1029782 : CollatzResearch.WordTrace tailWord_1029782 prefixEnd_1029782 644747002406212719877 := by
  unfold tailWord_1029782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2347452197205197600547725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25039490103522107739175733 2347452197205197600547725)
  ·
    refine ⟨880294573951949100205397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2347452197205197600547725 880294573951949100205397)
    ·
      refine ⟨644747002406212719877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 12 880294573951949100205397 644747002406212719877)
      ·
        rfl

theorem cell20_1029782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 12].length) (baseStart_1029782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029782 prefixEnd_1029782 := by exact prefixLift 1029782
  have htrace : WordTrace (prefixWord ++ tailWord_1029782) baseStart_1029782 baseEnd_1029782 := by
    simpa [prefixWord, tailWord_1029782, baseEnd_1029782] using wordTrace_append hprefix tailTrace_1029782
  have hstable : (prefixWord ++ tailWord_1029782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029782).length < 2 ^ (prefixWord ++ tailWord_1029782).sum := by decide
  have hdescent : baseEnd_1029782 < baseStart_1029782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029788 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 2]
def baseStart_1029788 : Nat := 118140960795 + 1029788 * 2 ^ 59
def prefixEnd_1029788 : Nat := 4983230072969 + 3 ^ 40 * 1029788 * 2
def baseEnd_1029788 : Nat := 470023303317619718590309

theorem tailTrace_1029788 : CollatzResearch.WordTrace tailWord_1029788 prefixEnd_1029788 470023303317619718590309 := by
  unfold tailWord_1029788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779726996630712316741009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25039635995507616422321345 18779726996630712316741009)
  ·
    refine ⟨14084795247473034237555757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18779726996630712316741009 14084795247473034237555757)
    ·
      refine ⟨5281798217802387839083409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14084795247473034237555757 5281798217802387839083409)
      ·
        refine ⟨3961348663351790879312557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5281798217802387839083409 3961348663351790879312557)
        ·
          refine ⟨1485505748756921579742209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3961348663351790879312557 1485505748756921579742209)
          ·
            refine ⟨1114129311567691184806657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1485505748756921579742209 1114129311567691184806657)
            ·
              refine ⟨835596983675768388604993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114129311567691184806657 835596983675768388604993)
              ·
                refine ⟨626697737756826291453745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835596983675768388604993 626697737756826291453745)
                ·
                  refine ⟨470023303317619718590309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626697737756826291453745 470023303317619718590309)
                  ·
                    rfl

theorem cell20_1029788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_1029788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029788 prefixEnd_1029788 := by exact prefixLift 1029788
  have htrace : WordTrace (prefixWord ++ tailWord_1029788) baseStart_1029788 baseEnd_1029788 := by
    simpa [prefixWord, tailWord_1029788, baseEnd_1029788] using wordTrace_append hprefix tailTrace_1029788
  have hstable : (prefixWord ++ tailWord_1029788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029788).length < 2 ^ (prefixWord ++ tailWord_1029788).sum := by decide
  have hdescent : baseEnd_1029788 < baseStart_1029788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029792 : List Nat := [2, 1, 1, 4, 3, 2, 1, 4, 2]
def baseStart_1029792 : Nat := 118140960795 + 1029792 * 2 ^ 59
def prefixEnd_1029792 : Nat := 4983230072969 + 3 ^ 40 * 1029792 * 2
def baseEnd_1029792 : Nat := 470025129026613482456959

theorem tailTrace_1029792 : CollatzResearch.WordTrace tailWord_1029792 prefixEnd_1029792 470025129026613482456959 := by
  unfold tailWord_1029792
  simp only [CollatzResearch.WordTrace]
  refine ⟨18779799942623466658313815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25039733256831288877751753 18779799942623466658313815)
  ·
    refine ⟨28169699913935199987470723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18779799942623466658313815 28169699913935199987470723)
    ·
      refine ⟨42254549870902799981206085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28169699913935199987470723 42254549870902799981206085)
      ·
        refine ⟨7922728100794274996476141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42254549870902799981206085 7922728100794274996476141)
        ·
          refine ⟨2971023037797853123678553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7922728100794274996476141 2971023037797853123678553)
          ·
            refine ⟨2228267278348389842758915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2971023037797853123678553 2228267278348389842758915)
            ·
              refine ⟨3342400917522584764138373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228267278348389842758915 3342400917522584764138373)
              ·
                refine ⟨626700172035484643275945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3342400917522584764138373 626700172035484643275945)
                ·
                  refine ⟨470025129026613482456959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626700172035484643275945 470025129026613482456959)
                  ·
                    rfl

theorem cell20_1029792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_1029792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029792 prefixEnd_1029792 := by exact prefixLift 1029792
  have htrace : WordTrace (prefixWord ++ tailWord_1029792) baseStart_1029792 baseEnd_1029792 := by
    simpa [prefixWord, tailWord_1029792, baseEnd_1029792] using wordTrace_append hprefix tailTrace_1029792
  have hstable : (prefixWord ++ tailWord_1029792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029792).length < 2 ^ (prefixWord ++ tailWord_1029792).sum := by decide
  have hdescent : baseEnd_1029792 < baseStart_1029792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029837 : List Nat := [1, 6, 2, 1, 1, 2, 7]
def baseStart_1029837 : Nat := 118140960795 + 1029837 * 2 ^ 59
def prefixEnd_1029837 : Nat := 4983230072969 + 3 ^ 40 * 1029837 * 2
def baseEnd_1029837 : Nat := 52227296472532591772975

theorem tailTrace_1029837 : CollatzResearch.WordTrace tailWord_1029837 prefixEnd_1029837 52227296472532591772975 := by
  unfold tailWord_1029837
  simp only [CollatzResearch.WordTrace]
  refine ⟨37561241170083906002015765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25040827446722604001343843 37561241170083906002015765)
  ·
    refine ⟨1760683179847683093844489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37561241170083906002015765 1760683179847683093844489)
    ·
      refine ⟨1320512384885762320383367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1760683179847683093844489 1320512384885762320383367)
      ·
        refine ⟨1980768577328643480575051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320512384885762320383367 1980768577328643480575051)
        ·
          refine ⟨2971152865992965220862577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980768577328643480575051 2971152865992965220862577)
          ·
            refine ⟨2228364649494723915646933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2971152865992965220862577 2228364649494723915646933)
            ·
              refine ⟨52227296472532591772975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2228364649494723915646933 52227296472532591772975)
              ·
                rfl

theorem cell20_1029837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_1029837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029837 prefixEnd_1029837 := by exact prefixLift 1029837
  have htrace : WordTrace (prefixWord ++ tailWord_1029837) baseStart_1029837 baseEnd_1029837 := by
    simpa [prefixWord, tailWord_1029837, baseEnd_1029837] using wordTrace_append hprefix tailTrace_1029837
  have hstable : (prefixWord ++ tailWord_1029837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029837).length < 2 ^ (prefixWord ++ tailWord_1029837).sum := by decide
  have hdescent : baseEnd_1029837 < baseStart_1029837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029841 : List Nat := [1, 2, 2, 1, 2, 5, 7]
def baseStart_1029841 : Nat := 118140960795 + 1029841 * 2 ^ 59
def prefixEnd_1029841 : Nat := 4983230072969 + 3 ^ 40 * 1029841 * 2
def baseEnd_1029841 : Nat := 52227499329087454424825

theorem tailTrace_1029841 : CollatzResearch.WordTrace tailWord_1029841 prefixEnd_1029841 52227499329087454424825 := by
  unfold tailWord_1029841
  simp only [CollatzResearch.WordTrace]
  refine ⟨37561387062069414685161377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25040924708046276456774251 37561387062069414685161377)
  ·
    refine ⟨28171040296552061013871033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37561387062069414685161377 28171040296552061013871033)
    ·
      refine ⟨21128280222414045760403275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28171040296552061013871033 21128280222414045760403275)
      ·
        refine ⟨31692420333621068640604913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21128280222414045760403275 31692420333621068640604913)
        ·
          refine ⟨23769315250215801480453685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31692420333621068640604913 23769315250215801480453685)
          ·
            refine ⟨2228373304707731388792533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23769315250215801480453685 2228373304707731388792533)
            ·
              refine ⟨52227499329087454424825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2228373304707731388792533 52227499329087454424825)
              ·
                rfl

theorem cell20_1029841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_1029841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029841 prefixEnd_1029841 := by exact prefixLift 1029841
  have htrace : WordTrace (prefixWord ++ tailWord_1029841) baseStart_1029841 baseEnd_1029841 := by
    simpa [prefixWord, tailWord_1029841, baseEnd_1029841] using wordTrace_append hprefix tailTrace_1029841
  have hstable : (prefixWord ++ tailWord_1029841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029841).length < 2 ^ (prefixWord ++ tailWord_1029841).sum := by decide
  have hdescent : baseEnd_1029841 < baseStart_1029841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029844 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1029844 : Nat := 118140960795 + 1029844 * 2 ^ 59
def prefixEnd_1029844 : Nat := 4983230072969 + 3 ^ 40 * 1029844 * 2
def baseEnd_1029844 : Nat := 470048863243532412723413

theorem tailTrace_1029844 : CollatzResearch.WordTrace tailWord_1029844 prefixEnd_1029844 470048863243532412723413 := by
  unfold tailWord_1029844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18780748240529273098760293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25040997654039030798347057 18780748240529273098760293)
  ·
    refine ⟨3521390295099238706017555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18780748240529273098760293 3521390295099238706017555)
    ·
      refine ⟨5282085442648858059026333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3521390295099238706017555 5282085442648858059026333)
      ·
        refine ⟨1980782040993321772134875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5282085442648858059026333 1980782040993321772134875)
        ·
          refine ⟨2971173061489982658202313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980782040993321772134875 2971173061489982658202313)
          ·
            refine ⟨2228379796117486993651735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2971173061489982658202313 2228379796117486993651735)
            ·
              refine ⟨3342569694176230490477603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228379796117486993651735 3342569694176230490477603)
              ·
                refine ⟨5013854541264345735716405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342569694176230490477603 5013854541264345735716405)
                ·
                  refine ⟨470048863243532412723413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5013854541264345735716405 470048863243532412723413)
                  ·
                    rfl

theorem cell20_1029844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1029844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029844 prefixEnd_1029844 := by exact prefixLift 1029844
  have htrace : WordTrace (prefixWord ++ tailWord_1029844) baseStart_1029844 baseEnd_1029844 := by
    simpa [prefixWord, tailWord_1029844, baseEnd_1029844] using wordTrace_append hprefix tailTrace_1029844
  have hstable : (prefixWord ++ tailWord_1029844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029844).length < 2 ^ (prefixWord ++ tailWord_1029844).sum := by decide
  have hdescent : baseEnd_1029844 < baseStart_1029844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029906 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1029906 : Nat := 118140960795 + 1029906 * 2 ^ 59
def prefixEnd_1029906 : Nat := 4983230072969 + 3 ^ 40 * 1029906 * 2
def baseEnd_1029906 : Nat := 470077161732935752656493

theorem tailTrace_1029906 : CollatzResearch.WordTrace tailWord_1029906 prefixEnd_1029906 470077161732935752656493 := by
  unfold tailWord_1029906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9390939451708482696569393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25042505204555953857518381 9390939451708482696569393)
  ·
    refine ⟨7043204588781362022427045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9390939451708482696569393 7043204588781362022427045)
    ·
      refine ⟨1320600860396505379205071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7043204588781362022427045 1320600860396505379205071)
      ·
        refine ⟨1980901290594758068807607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320600860396505379205071 1980901290594758068807607)
        ·
          refine ⟨2971351935892137103211411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980901290594758068807607 2971351935892137103211411)
          ·
            refine ⟨4457027903838205654817117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971351935892137103211411 4457027903838205654817117)
            ·
              refine ⟨1671385463939327120556419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4457027903838205654817117 1671385463939327120556419)
              ·
                refine ⟨2507078195908990680834629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671385463939327120556419 2507078195908990680834629)
                ·
                  refine ⟨470077161732935752656493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507078195908990680834629 470077161732935752656493)
                  ·
                    rfl

theorem cell20_1029906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1029906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029906 prefixEnd_1029906 := by exact prefixLift 1029906
  have htrace : WordTrace (prefixWord ++ tailWord_1029906) baseStart_1029906 baseEnd_1029906 := by
    simpa [prefixWord, tailWord_1029906, baseEnd_1029906] using wordTrace_append hprefix tailTrace_1029906
  have hstable : (prefixWord ++ tailWord_1029906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029906).length < 2 ^ (prefixWord ++ tailWord_1029906).sum := by decide
  have hdescent : baseEnd_1029906 < baseStart_1029906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1029972 : List Nat := [2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1029972 : Nat := 118140960795 + 1029972 * 2 ^ 59
def prefixEnd_1029972 : Nat := 4983230072969 + 3 ^ 40 * 1029972 * 2
def baseEnd_1029972 : Nat := 156702428643777618818741

theorem tailTrace_1029972 : CollatzResearch.WordTrace tailWord_1029972 prefixEnd_1029972 156702428643777618818741 := by
  unfold tailWord_1029972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18783082512297412029090085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25044110016396549372120113 18783082512297412029090085)
  ·
    refine ⟨3521827971055764755454391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18783082512297412029090085 3521827971055764755454391)
    ·
      refine ⟨5282741956583647133181587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3521827971055764755454391 5282741956583647133181587)
      ·
        refine ⟨7924112934875470699772381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5282741956583647133181587 7924112934875470699772381)
        ·
          refine ⟨2971542350578301512414643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7924112934875470699772381 2971542350578301512414643)
          ·
            refine ⟨4457313525867452268621965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971542350578301512414643 4457313525867452268621965)
            ·
              refine ⟨1671492572200294600733237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4457313525867452268621965 1671492572200294600733237)
              ·
                refine ⟨156702428643777618818741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1671492572200294600733237 156702428643777618818741)
                ·
                  rfl

theorem cell20_1029972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1029972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1029972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1029972 prefixEnd_1029972 := by exact prefixLift 1029972
  have htrace : WordTrace (prefixWord ++ tailWord_1029972) baseStart_1029972 baseEnd_1029972 := by
    simpa [prefixWord, tailWord_1029972, baseEnd_1029972] using wordTrace_append hprefix tailTrace_1029972
  have hstable : (prefixWord ++ tailWord_1029972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1029972).length < 2 ^ (prefixWord ++ tailWord_1029972).sum := by decide
  have hdescent : baseEnd_1029972 < baseStart_1029972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1029972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030000 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 5]
def baseStart_1030000 : Nat := 118140960795 + 1030000 * 2 ^ 59
def prefixEnd_1030000 : Nat := 4983230072969 + 3 ^ 40 * 1030000 * 2
def baseEnd_1030000 : Nat := 470120065894289203522775

theorem tailTrace_1030000 : CollatzResearch.WordTrace tailWord_1030000 prefixEnd_1030000 470120065894289203522775 := by
  unfold tailWord_1030000
  simp only [CollatzResearch.WordTrace]
  refine ⟨18783593134246692420099727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25044790845662256560132969 18783593134246692420099727)
  ·
    refine ⟨28175389701370038630149591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18783593134246692420099727 28175389701370038630149591)
    ·
      refine ⟨42263084552055057945224387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28175389701370038630149591 42263084552055057945224387)
      ·
        refine ⟨63394626828082586917836581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42263084552055057945224387 63394626828082586917836581)
        ·
          refine ⟨11886492530265485047094359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63394626828082586917836581 11886492530265485047094359)
          ·
            refine ⟨17829738795398227570641539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11886492530265485047094359 17829738795398227570641539)
            ·
              refine ⟨26744608193097341355962309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17829738795398227570641539 26744608193097341355962309)
              ·
                refine ⟨5014614036205751504242933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26744608193097341355962309 5014614036205751504242933)
                ·
                  refine ⟨470120065894289203522775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014614036205751504242933 470120065894289203522775)
                  ·
                    rfl

theorem cell20_1030000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_1030000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030000 prefixEnd_1030000 := by exact prefixLift 1030000
  have htrace : WordTrace (prefixWord ++ tailWord_1030000) baseStart_1030000 baseEnd_1030000 := by
    simpa [prefixWord, tailWord_1030000, baseEnd_1030000] using wordTrace_append hprefix tailTrace_1030000
  have hstable : (prefixWord ++ tailWord_1030000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030000).length < 2 ^ (prefixWord ++ tailWord_1030000).sum := by decide
  have hdescent : baseEnd_1030000 < baseStart_1030000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030030 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_1030030 : Nat := 118140960795 + 1030030 * 2 ^ 59
def prefixEnd_1030030 : Nat := 4983230072969 + 3 ^ 40 * 1030030 * 2
def baseEnd_1030030 : Nat := 470133758711742432522653

theorem tailTrace_1030030 : CollatzResearch.WordTrace tailWord_1030030 prefixEnd_1030030 470133758711742432522653 := by
  unfold tailWord_1030030
  simp only [CollatzResearch.WordTrace]
  refine ⟨4696035057298087495473943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25045520305589799975861029 4696035057298087495473943)
  ·
    refine ⟨7044052585947131243210915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4696035057298087495473943 7044052585947131243210915)
    ·
      refine ⟨10566078878920696864816373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7044052585947131243210915 10566078878920696864816373)
      ·
        refine ⟨990569894898815331076535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10566078878920696864816373 990569894898815331076535)
        ·
          refine ⟨1485854842348222996614803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990569894898815331076535 1485854842348222996614803)
          ·
            refine ⟨2228782263522334494922205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485854842348222996614803 2228782263522334494922205)
            ·
              refine ⟨835793348820875435595827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2228782263522334494922205 835793348820875435595827)
              ·
                refine ⟨1253690023231313153393741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835793348820875435595827 1253690023231313153393741)
                ·
                  refine ⟨470133758711742432522653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253690023231313153393741 470133758711742432522653)
                  ·
                    rfl

theorem cell20_1030030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_1030030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030030 prefixEnd_1030030 := by exact prefixLift 1030030
  have htrace : WordTrace (prefixWord ++ tailWord_1030030) baseStart_1030030 baseEnd_1030030 := by
    simpa [prefixWord, tailWord_1030030, baseEnd_1030030] using wordTrace_append hprefix tailTrace_1030030
  have hstable : (prefixWord ++ tailWord_1030030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030030).length < 2 ^ (prefixWord ++ tailWord_1030030).sum := by decide
  have hdescent : baseEnd_1030030 < baseStart_1030030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030055 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 5]
def baseStart_1030055 : Nat := 118140960795 + 1030055 * 2 ^ 59
def prefixEnd_1030055 : Nat := 4983230072969 + 3 ^ 40 * 1030055 * 2
def baseEnd_1030055 : Nat := 470145169392953456689217

theorem tailTrace_1030055 : CollatzResearch.WordTrace tailWord_1030055 prefixEnd_1030055 470145169392953456689217 := by
  unfold tailWord_1030055
  simp only [CollatzResearch.WordTrace]
  refine ⟨37569192283294129233451619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25046128188862752822301079 37569192283294129233451619)
  ·
    refine ⟨56353788424941193850177429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37569192283294129233451619 56353788424941193850177429)
    ·
      refine ⟨2641583832419118461727067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56353788424941193850177429 2641583832419118461727067)
      ·
        refine ⟨3962375748628677692590601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641583832419118461727067 3962375748628677692590601)
        ·
          refine ⟨2971781811471508269442951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3962375748628677692590601 2971781811471508269442951)
          ·
            refine ⟨4457672717207262404164427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971781811471508269442951 4457672717207262404164427)
            ·
              refine ⟨6686509075810893606246641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457672717207262404164427 6686509075810893606246641)
              ·
                refine ⟨5014881806858170204684981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6686509075810893606246641 5014881806858170204684981)
                ·
                  refine ⟨470145169392953456689217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014881806858170204684981 470145169392953456689217)
                  ·
                    rfl

theorem cell20_1030055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 5].length) (baseStart_1030055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030055 prefixEnd_1030055 := by exact prefixLift 1030055
  have htrace : WordTrace (prefixWord ++ tailWord_1030055) baseStart_1030055 baseEnd_1030055 := by
    simpa [prefixWord, tailWord_1030055, baseEnd_1030055] using wordTrace_append hprefix tailTrace_1030055
  have hstable : (prefixWord ++ tailWord_1030055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030055).length < 2 ^ (prefixWord ++ tailWord_1030055).sum := by decide
  have hdescent : baseEnd_1030055 < baseStart_1030055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030069 : List Nat := [1, 3, 3, 2, 1, 2, 8]
def baseStart_1030069 : Nat := 118140960795 + 1030069 * 2 ^ 59
def prefixEnd_1030069 : Nat := 4983230072969 + 3 ^ 40 * 1030069 * 2
def baseEnd_1030069 : Nat := 52239062152714625580277

theorem tailTrace_1030069 : CollatzResearch.WordTrace tailWord_1030069 prefixEnd_1030069 52239062152714625580277 := by
  unfold tailWord_1030069
  simp only [CollatzResearch.WordTrace]
  refine ⟨37569702905243409624461261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25046468603495606416307507 37569702905243409624461261)
  ·
    refine ⟨14088638589466278609172973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37569702905243409624461261 14088638589466278609172973)
    ·
      refine ⟨5283239471049854478439865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14088638589466278609172973 5283239471049854478439865)
      ·
        refine ⟨3962429603287390858829899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283239471049854478439865 3962429603287390858829899)
        ·
          refine ⟨5943644404931086288244849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962429603287390858829899 5943644404931086288244849)
          ·
            refine ⟨4457733303698314716183637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5943644404931086288244849 4457733303698314716183637)
            ·
              refine ⟨52239062152714625580277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4457733303698314716183637 52239062152714625580277)
              ·
                rfl

theorem cell20_1030069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 8].length) (baseStart_1030069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030069 prefixEnd_1030069 := by exact prefixLift 1030069
  have htrace : WordTrace (prefixWord ++ tailWord_1030069) baseStart_1030069 baseEnd_1030069 := by
    simpa [prefixWord, tailWord_1030069, baseEnd_1030069] using wordTrace_append hprefix tailTrace_1030069
  have hstable : (prefixWord ++ tailWord_1030069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030069).length < 2 ^ (prefixWord ++ tailWord_1030069).sum := by decide
  have hdescent : baseEnd_1030069 < baseStart_1030069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030100 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_1030100 : Nat := 118140960795 + 1030100 * 2 ^ 59
def prefixEnd_1030100 : Nat := 4983230072969 + 3 ^ 40 * 1030100 * 2
def baseEnd_1030100 : Nat := 470165708619133300189033

theorem tailTrace_1030100 : CollatzResearch.WordTrace tailWord_1030100 prefixEnd_1030100 470165708619133300189033 := by
  unfold tailWord_1030100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785416784065550959419877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25047222378754067945893169 18785416784065550959419877)
  ·
    refine ⟨3522265647012290804891227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18785416784065550959419877 3522265647012290804891227)
    ·
      refine ⟨5283398470518436207336841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522265647012290804891227 5283398470518436207336841)
      ·
        refine ⟨3962548852888827155502631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283398470518436207336841 3962548852888827155502631)
        ·
          refine ⟨5943823279333240733253947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962548852888827155502631 5943823279333240733253947)
          ·
            refine ⟨8915734918999861099880921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5943823279333240733253947 8915734918999861099880921)
            ·
              refine ⟨6686801189249895824910691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8915734918999861099880921 6686801189249895824910691)
              ·
                refine ⟨10030201783874843737366037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6686801189249895824910691 10030201783874843737366037)
                ·
                  refine ⟨470165708619133300189033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10030201783874843737366037 470165708619133300189033)
                  ·
                    rfl

theorem cell20_1030100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_1030100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030100 prefixEnd_1030100 := by exact prefixLift 1030100
  have htrace : WordTrace (prefixWord ++ tailWord_1030100) baseStart_1030100 baseEnd_1030100 := by
    simpa [prefixWord, tailWord_1030100, baseEnd_1030100] using wordTrace_append hprefix tailTrace_1030100
  have hstable : (prefixWord ++ tailWord_1030100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030100).length < 2 ^ (prefixWord ++ tailWord_1030100).sum := by decide
  have hdescent : baseEnd_1030100 < baseStart_1030100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030172 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 2]
def baseStart_1030172 : Nat := 118140960795 + 1030172 * 2 ^ 59
def prefixEnd_1030172 : Nat := 4983230072969 + 3 ^ 40 * 1030172 * 2
def baseEnd_1030172 : Nat := 470198571381021049788739

theorem tailTrace_1030172 : CollatzResearch.WordTrace tailWord_1030172 prefixEnd_1030172 470198571381021049788739 := by
  unfold tailWord_1030172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786729811935129107730385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25048973082580172143640513 18786729811935129107730385)
  ·
    refine ⟨14090047358951346830797789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18786729811935129107730385 14090047358951346830797789)
    ·
      refine ⟨5283767759606755061549171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14090047358951346830797789 5283767759606755061549171)
      ·
        refine ⟨7925651639410132592323757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283767759606755061549171 7925651639410132592323757)
        ·
          refine ⟨2972119364778799722121409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7925651639410132592323757 2972119364778799722121409)
          ·
            refine ⟨2229089523584099791591057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2972119364778799722121409 2229089523584099791591057)
            ·
              refine ⟨1671817142688074843693293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229089523584099791591057 1671817142688074843693293)
              ·
                refine ⟨626931428508028066384985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1671817142688074843693293 626931428508028066384985)
                ·
                  refine ⟨470198571381021049788739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626931428508028066384985 470198571381021049788739)
                  ·
                    rfl

theorem cell20_1030172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_1030172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030172 prefixEnd_1030172 := by exact prefixLift 1030172
  have htrace : WordTrace (prefixWord ++ tailWord_1030172) baseStart_1030172 baseEnd_1030172 := by
    simpa [prefixWord, tailWord_1030172, baseEnd_1030172] using wordTrace_append hprefix tailTrace_1030172
  have hstable : (prefixWord ++ tailWord_1030172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030172).length < 2 ^ (prefixWord ++ tailWord_1030172).sum := by decide
  have hdescent : baseEnd_1030172 < baseStart_1030172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030186 : List Nat := [3, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_1030186 : Nat := 118140960795 + 1030186 * 2 ^ 59
def prefixEnd_1030186 : Nat := 4983230072969 + 3 ^ 40 * 1030186 * 2
def baseEnd_1030186 : Nat := 470204961362499223322015

theorem tailTrace_1030186 : CollatzResearch.WordTrace tailWord_1030186 prefixEnd_1030186 470204961362499223322015 := by
  unfold tailWord_1030186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9393492561454884651617603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25049313497213025737646941 9393492561454884651617603)
  ·
    refine ⟨14090238842182326977426405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9393492561454884651617603 14090238842182326977426405)
    ·
      refine ⟨2641919782909186308267451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14090238842182326977426405 2641919782909186308267451)
      ·
        refine ⟨3962879674363779462401177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2641919782909186308267451 3962879674363779462401177)
        ·
          refine ⟨2972159755772834596800883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3962879674363779462401177 2972159755772834596800883)
          ·
            refine ⟨4458239633659251895201325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972159755772834596800883 4458239633659251895201325)
            ·
              refine ⟨1671839862622219460700497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4458239633659251895201325 1671839862622219460700497)
              ·
                refine ⟨1253879896966664595525373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671839862622219460700497 1253879896966664595525373)
                ·
                  refine ⟨470204961362499223322015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253879896966664595525373 470204961362499223322015)
                  ·
                    rfl

theorem cell20_1030186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_1030186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030186 prefixEnd_1030186 := by exact prefixLift 1030186
  have htrace : WordTrace (prefixWord ++ tailWord_1030186) baseStart_1030186 baseEnd_1030186 := by
    simpa [prefixWord, tailWord_1030186, baseEnd_1030186] using wordTrace_append hprefix tailTrace_1030186
  have hstable : (prefixWord ++ tailWord_1030186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030186).length < 2 ^ (prefixWord ++ tailWord_1030186).sum := by decide
  have hdescent : baseEnd_1030186 < baseStart_1030186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030193 : List Nat := [1, 2, 2, 3, 1, 3, 2, 4, 2]
def baseStart_1030193 : Nat := 118140960795 + 1030193 * 2 ^ 59
def prefixEnd_1030193 : Nat := 4983230072969 + 3 ^ 40 * 1030193 * 2
def baseEnd_1030193 : Nat := 470208156353238310088653

theorem tailTrace_1030193 : CollatzResearch.WordTrace tailWord_1030193 prefixEnd_1030193 470208156353238310088653 := by
  unfold tailWord_1030193
  simp only [CollatzResearch.WordTrace]
  refine ⟨37574225556794178801975233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25049483704529452534650155 37574225556794178801975233)
  ·
    refine ⟨28180669167595634101481425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37574225556794178801975233 28180669167595634101481425)
    ·
      refine ⟨21135501875696725576111069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28180669167595634101481425 21135501875696725576111069)
      ·
        refine ⟨7925813203386272091041651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21135501875696725576111069 7925813203386272091041651)
        ·
          refine ⟨11888719805079408136562477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925813203386272091041651 11888719805079408136562477)
          ·
            refine ⟨4458269926904778051210929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11888719805079408136562477 4458269926904778051210929)
            ·
              refine ⟨3343702445178583538408197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458269926904778051210929 3343702445178583538408197)
              ·
                refine ⟨626944208470984413451537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3343702445178583538408197 626944208470984413451537)
                ·
                  refine ⟨470208156353238310088653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626944208470984413451537 470208156353238310088653)
                  ·
                    rfl

theorem cell20_1030193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 2].length) (baseStart_1030193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030193 prefixEnd_1030193 := by exact prefixLift 1030193
  have htrace : WordTrace (prefixWord ++ tailWord_1030193) baseStart_1030193 baseEnd_1030193 := by
    simpa [prefixWord, tailWord_1030193, baseEnd_1030193] using wordTrace_append hprefix tailTrace_1030193
  have hstable : (prefixWord ++ tailWord_1030193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030193).length < 2 ^ (prefixWord ++ tailWord_1030193).sum := by decide
  have hdescent : baseEnd_1030193 < baseStart_1030193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030231 : List Nat := [1, 1, 3, 2, 2, 1, 5, 3, 2]
def baseStart_1030231 : Nat := 118140960795 + 1030231 * 2 ^ 59
def prefixEnd_1030231 : Nat := 4983230072969 + 3 ^ 40 * 1030231 * 2
def baseEnd_1030231 : Nat := 470225500588679066821831

theorem tailTrace_1030231 : CollatzResearch.WordTrace tailWord_1030231 prefixEnd_1030231 470225500588679066821831 := by
  unfold tailWord_1030231
  simp only [CollatzResearch.WordTrace]
  refine ⟨37575611530656511291858547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25050407687104340861239031 37575611530656511291858547)
  ·
    refine ⟨56363417295984766937787821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37575611530656511291858547 56363417295984766937787821)
    ·
      refine ⟨21136281485994287601670433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56363417295984766937787821 21136281485994287601670433)
      ·
        refine ⟨15852211114495715701252825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21136281485994287601670433 15852211114495715701252825)
        ·
          refine ⟨11889158335871786775939619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15852211114495715701252825 11889158335871786775939619)
          ·
            refine ⟨17833737503807680163909429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889158335871786775939619 17833737503807680163909429)
            ·
              refine ⟨1671912890981970015366509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17833737503807680163909429 1671912890981970015366509)
              ·
                refine ⟨626967334118238755762441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1671912890981970015366509 626967334118238755762441)
                ·
                  refine ⟨470225500588679066821831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626967334118238755762441 470225500588679066821831)
                  ·
                    rfl

theorem cell20_1030231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 3, 2].length) (baseStart_1030231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030231 prefixEnd_1030231 := by exact prefixLift 1030231
  have htrace : WordTrace (prefixWord ++ tailWord_1030231) baseStart_1030231 baseEnd_1030231 := by
    simpa [prefixWord, tailWord_1030231, baseEnd_1030231] using wordTrace_append hprefix tailTrace_1030231
  have hstable : (prefixWord ++ tailWord_1030231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030231).length < 2 ^ (prefixWord ++ tailWord_1030231).sum := by decide
  have hdescent : baseEnd_1030231 < baseStart_1030231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030252 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 4]
def baseStart_1030252 : Nat := 118140960795 + 1030252 * 2 ^ 59
def prefixEnd_1030252 : Nat := 4983230072969 + 3 ^ 40 * 1030252 * 2
def baseEnd_1030252 : Nat := 470235085560896327121745

theorem tailTrace_1030252 : CollatzResearch.WordTrace tailWord_1030252 prefixEnd_1030252 470235085560896327121745 := by
  unfold tailWord_1030252
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788188731790215939186505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25050918309053621252248673 18788188731790215939186505)
  ·
    refine ⟨14091141548842661954389879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18788188731790215939186505 14091141548842661954389879)
    ·
      refine ⟨21136712323263992931584819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14091141548842661954389879 21136712323263992931584819)
      ·
        refine ⟨31705068484895989397377229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136712323263992931584819 31705068484895989397377229)
        ·
          refine ⟨11889400681835996024016461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31705068484895989397377229 11889400681835996024016461)
          ·
            refine ⟨4458525255688498509006173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11889400681835996024016461 4458525255688498509006173)
            ·
              refine ⟨1671946970883186940877315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4458525255688498509006173 1671946970883186940877315)
              ·
                refine ⟨2507920456324780411315973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671946970883186940877315 2507920456324780411315973)
                ·
                  refine ⟨470235085560896327121745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507920456324780411315973 470235085560896327121745)
                  ·
                    rfl

theorem cell20_1030252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_1030252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030252 prefixEnd_1030252 := by exact prefixLift 1030252
  have htrace : WordTrace (prefixWord ++ tailWord_1030252) baseStart_1030252 baseEnd_1030252 := by
    simpa [prefixWord, tailWord_1030252, baseEnd_1030252] using wordTrace_append hprefix tailTrace_1030252
  have hstable : (prefixWord ++ tailWord_1030252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030252).length < 2 ^ (prefixWord ++ tailWord_1030252).sum := by decide
  have hdescent : baseEnd_1030252 < baseStart_1030252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030262 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1030262 : Nat := 118140960795 + 1030262 * 2 ^ 59
def prefixEnd_1030262 : Nat := 4983230072969 + 3 ^ 40 * 1030262 * 2
def baseEnd_1030262 : Nat := 470239649833380736788371

theorem tailTrace_1030262 : CollatzResearch.WordTrace tailWord_1030262 prefixEnd_1030262 470239649833380736788371 := by
  unfold tailWord_1030262
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348546387096512724139815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25051161462362802390824693 2348546387096512724139815)
  ·
    refine ⟨3522819580644769086209723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2348546387096512724139815 3522819580644769086209723)
    ·
      refine ⟨5284229370967153629314585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522819580644769086209723 5284229370967153629314585)
      ·
        refine ⟨3963172028225365221985939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5284229370967153629314585 3963172028225365221985939)
        ·
          refine ⟨5944758042338047832978909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3963172028225365221985939 5944758042338047832978909)
          ·
            refine ⟨2229284265876767937367091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5944758042338047832978909 2229284265876767937367091)
            ·
              refine ⟨3343926398815151906050637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229284265876767937367091 3343926398815151906050637)
              ·
                refine ⟨1253972399555681964768989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3343926398815151906050637 1253972399555681964768989)
                ·
                  refine ⟨470239649833380736788371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253972399555681964768989 470239649833380736788371)
                  ·
                    rfl

theorem cell20_1030262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1030262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030262 prefixEnd_1030262 := by exact prefixLift 1030262
  have htrace : WordTrace (prefixWord ++ tailWord_1030262) baseStart_1030262 baseEnd_1030262 := by
    simpa [prefixWord, tailWord_1030262, baseEnd_1030262] using wordTrace_append hprefix tailTrace_1030262
  have hstable : (prefixWord ++ tailWord_1030262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030262).length < 2 ^ (prefixWord ++ tailWord_1030262).sum := by decide
  have hdescent : baseEnd_1030262 < baseStart_1030262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030303 : List Nat := [1, 1, 2, 6, 1, 3, 2, 2, 2]
def baseStart_1030303 : Nat := 118140960795 + 1030303 * 2 ^ 59
def prefixEnd_1030303 : Nat := 4983230072969 + 3 ^ 40 * 1030303 * 2
def baseEnd_1030303 : Nat := 470258363350566816421537

theorem tailTrace_1030303 : CollatzResearch.WordTrace tailWord_1030303 prefixEnd_1030303 470258363350566816421537 := by
  unfold tailWord_1030303
  simp only [CollatzResearch.WordTrace]
  refine ⟨37578237586395667588479563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25052158390930445058986375 37578237586395667588479563)
  ·
    refine ⟨56367356379593501382719345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37578237586395667588479563 56367356379593501382719345)
    ·
      refine ⟨42275517284695126037039509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56367356379593501382719345 42275517284695126037039509)
      ·
        refine ⟨1981664872720084032986227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42275517284695126037039509 1981664872720084032986227)
        ·
          refine ⟨2972497309080126049479341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981664872720084032986227 2972497309080126049479341)
          ·
            refine ⟨1114686490905047268554753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2972497309080126049479341 1114686490905047268554753)
            ·
              refine ⟨836014868178785451416065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114686490905047268554753 836014868178785451416065)
              ·
                refine ⟨627011151134089088562049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836014868178785451416065 627011151134089088562049)
                ·
                  refine ⟨470258363350566816421537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627011151134089088562049 470258363350566816421537)
                  ·
                    rfl

theorem cell20_1030303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 2, 2].length) (baseStart_1030303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030303 prefixEnd_1030303 := by exact prefixLift 1030303
  have htrace : WordTrace (prefixWord ++ tailWord_1030303) baseStart_1030303 baseEnd_1030303 := by
    simpa [prefixWord, tailWord_1030303, baseEnd_1030303] using wordTrace_append hprefix tailTrace_1030303
  have hstable : (prefixWord ++ tailWord_1030303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030303).length < 2 ^ (prefixWord ++ tailWord_1030303).sum := by decide
  have hdescent : baseEnd_1030303 < baseStart_1030303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030376 : List Nat := [2, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_1030376 : Nat := 118140960795 + 1030376 * 2 ^ 59
def prefixEnd_1030376 : Nat := 4983230072969 + 3 ^ 40 * 1030376 * 2
def baseEnd_1030376 : Nat := 470291682539703006987905

theorem tailTrace_1030376 : CollatzResearch.WordTrace tailWord_1030376 prefixEnd_1030376 470291682539703006987905 := by
  unfold tailWord_1030376
  simp only [CollatzResearch.WordTrace]
  refine ⟨18790450057565600527943491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25053933410087467370591321 18790450057565600527943491)
  ·
    refine ⟨28185675086348400791915237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18790450057565600527943491 28185675086348400791915237)
    ·
      refine ⟨5284814078690325148484107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28185675086348400791915237 5284814078690325148484107)
      ·
        refine ⟨7927221118035487722726161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284814078690325148484107 7927221118035487722726161)
        ·
          refine ⟨5945415838526615792044621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7927221118035487722726161 5945415838526615792044621)
          ·
            refine ⟨2229530939447480922016733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5945415838526615792044621 2229530939447480922016733)
            ·
              refine ⟨836074102292805345756275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2229530939447480922016733 836074102292805345756275)
              ·
                refine ⟨1254111153439208018634413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836074102292805345756275 1254111153439208018634413)
                ·
                  refine ⟨470291682539703006987905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254111153439208018634413 470291682539703006987905)
                  ·
                    rfl

theorem cell20_1030376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_1030376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030376 prefixEnd_1030376 := by exact prefixLift 1030376
  have htrace : WordTrace (prefixWord ++ tailWord_1030376) baseStart_1030376 baseEnd_1030376 := by
    simpa [prefixWord, tailWord_1030376, baseEnd_1030376] using wordTrace_append hprefix tailTrace_1030376
  have hstable : (prefixWord ++ tailWord_1030376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030376).length < 2 ^ (prefixWord ++ tailWord_1030376).sum := by decide
  have hdescent : baseEnd_1030376 < baseStart_1030376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030387 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 4]
def baseStart_1030387 : Nat := 118140960795 + 1030387 * 2 ^ 59
def prefixEnd_1030387 : Nat := 4983230072969 + 3 ^ 40 * 1030387 * 2
def baseEnd_1030387 : Nat := 470296703239435857621193

theorem tailTrace_1030387 : CollatzResearch.WordTrace tailWord_1030387 prefixEnd_1030387 470296703239435857621193 := by
  unfold tailWord_1030387
  simp only [CollatzResearch.WordTrace]
  refine ⟨37581301318091349934537415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25054200878727566623024943 37581301318091349934537415)
  ·
    refine ⟨56371951977137024901806123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37581301318091349934537415 56371951977137024901806123)
    ·
      refine ⟨84557927965705537352709185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56371951977137024901806123 84557927965705537352709185)
      ·
        refine ⟨63418445974279153014531889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84557927965705537352709185 63418445974279153014531889)
        ·
          refine ⟨47563834480709364760898917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63418445974279153014531889 47563834480709364760898917)
          ·
            refine ⟨8918218965133005892668547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47563834480709364760898917 8918218965133005892668547)
            ·
              refine ⟨13377328447699508839002821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8918218965133005892668547 13377328447699508839002821)
              ·
                refine ⟨2508249083943657907313029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13377328447699508839002821 2508249083943657907313029)
                ·
                  refine ⟨470296703239435857621193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508249083943657907313029 470296703239435857621193)
                  ·
                    rfl

theorem cell20_1030387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_1030387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030387 prefixEnd_1030387 := by exact prefixLift 1030387
  have htrace : WordTrace (prefixWord ++ tailWord_1030387) baseStart_1030387 baseEnd_1030387 := by
    simpa [prefixWord, tailWord_1030387, baseEnd_1030387] using wordTrace_append hprefix tailTrace_1030387
  have hstable : (prefixWord ++ tailWord_1030387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030387).length < 2 ^ (prefixWord ++ tailWord_1030387).sum := by decide
  have hdescent : baseEnd_1030387 < baseStart_1030387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030390 : List Nat := [5, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1030390 : Nat := 118140960795 + 1030390 * 2 ^ 59
def prefixEnd_1030390 : Nat := 4983230072969 + 3 ^ 40 * 1030390 * 2
def baseEnd_1030390 : Nat := 156766024173727060173727

theorem tailTrace_1030390 : CollatzResearch.WordTrace tailWord_1030390 prefixEnd_1030390 156766024173727060173727 := by
  unfold tailWord_1030390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348838171067530090431039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25054273824720320964597749 2348838171067530090431039)
  ·
    refine ⟨3523257256601295135646559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2348838171067530090431039 3523257256601295135646559)
    ·
      refine ⟨5284885884901942703469839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523257256601295135646559 5284885884901942703469839)
      ·
        refine ⟨7927328827352914055204759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284885884901942703469839 7927328827352914055204759)
        ·
          refine ⟨11890993241029371082807139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927328827352914055204759 11890993241029371082807139)
          ·
            refine ⟨17836489861544056624210709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11890993241029371082807139 17836489861544056624210709)
            ·
              refine ⟨836085462259877654259877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17836489861544056624210709 836085462259877654259877)
              ·
                refine ⟨156766024173727060173727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836085462259877654259877 156766024173727060173727)
                ·
                  rfl

theorem cell20_1030390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1030390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030390 prefixEnd_1030390 := by exact prefixLift 1030390
  have htrace : WordTrace (prefixWord ++ tailWord_1030390) baseStart_1030390 baseEnd_1030390 := by
    simpa [prefixWord, tailWord_1030390, baseEnd_1030390] using wordTrace_append hprefix tailTrace_1030390
  have hstable : (prefixWord ++ tailWord_1030390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030390).length < 2 ^ (prefixWord ++ tailWord_1030390).sum := by decide
  have hdescent : baseEnd_1030390 < baseStart_1030390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030407 : List Nat := [1, 1, 4, 5, 2, 1, 6]
def baseStart_1030407 : Nat := 118140960795 + 1030407 * 2 ^ 59
def prefixEnd_1030407 : Nat := 4983230072969 + 3 ^ 40 * 1030407 * 2
def baseEnd_1030407 : Nat := 52256203531600519661605

theorem tailTrace_1030407 : CollatzResearch.WordTrace tailWord_1030407 prefixEnd_1030407 52256203531600519661605 := by
  unfold tailWord_1030407
  simp only [CollatzResearch.WordTrace]
  refine ⟨37582030778018893350265475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25054687185345928900176983 37582030778018893350265475)
  ·
    refine ⟨56373046167028340025398213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37582030778018893350265475 56373046167028340025398213)
    ·
      refine ⟨10569946156317813754762165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56373046167028340025398213 10569946156317813754762165)
      ·
        refine ⟨990932452154795039508953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10569946156317813754762165 990932452154795039508953)
        ·
          refine ⟨743199339116096279631715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990932452154795039508953 743199339116096279631715)
          ·
            refine ⟨1114799008674144419447573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743199339116096279631715 1114799008674144419447573)
            ·
              refine ⟨52256203531600519661605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1114799008674144419447573 52256203531600519661605)
              ·
                rfl

theorem cell20_1030407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 6].length) (baseStart_1030407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030407 prefixEnd_1030407 := by exact prefixLift 1030407
  have htrace : WordTrace (prefixWord ++ tailWord_1030407) baseStart_1030407 baseEnd_1030407 := by
    simpa [prefixWord, tailWord_1030407, baseEnd_1030407] using wordTrace_append hprefix tailTrace_1030407
  have hstable : (prefixWord ++ tailWord_1030407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030407).length < 2 ^ (prefixWord ++ tailWord_1030407).sum := by decide
  have hdescent : baseEnd_1030407 < baseStart_1030407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030501 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 6]
def baseStart_1030501 : Nat := 118140960795 + 1030501 * 2 ^ 59
def prefixEnd_1030501 : Nat := 4983230072969 + 3 ^ 40 * 1030501 * 2
def baseEnd_1030501 : Nat := 470348735945758127820727

theorem tailTrace_1030501 : CollatzResearch.WordTrace tailWord_1030501 prefixEnd_1030501 470348735945758127820727 := by
  unfold tailWord_1030501
  simp only [CollatzResearch.WordTrace]
  refine ⟨37585459239678347404187357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25056972826452231602791571 37585459239678347404187357)
  ·
    refine ⟨14094547214879380276570259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37585459239678347404187357 14094547214879380276570259)
    ·
      refine ⟨21141820822319070414855389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14094547214879380276570259 21141820822319070414855389)
      ·
        refine ⟨7928182808369651405570771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21141820822319070414855389 7928182808369651405570771)
        ·
          refine ⟨11892274212554477108356157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928182808369651405570771 11892274212554477108356157)
          ·
            refine ⟨4459602829707928915633559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11892274212554477108356157 4459602829707928915633559)
            ·
              refine ⟨6689404244561893373450339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459602829707928915633559 6689404244561893373450339)
              ·
                refine ⟨10034106366842840060175509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6689404244561893373450339 10034106366842840060175509)
                ·
                  refine ⟨470348735945758127820727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10034106366842840060175509 470348735945758127820727)
                  ·
                    rfl

theorem cell20_1030501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_1030501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030501 prefixEnd_1030501 := by exact prefixLift 1030501
  have htrace : WordTrace (prefixWord ++ tailWord_1030501) baseStart_1030501 baseEnd_1030501 := by
    simpa [prefixWord, tailWord_1030501, baseEnd_1030501] using wordTrace_append hprefix tailTrace_1030501
  have hstable : (prefixWord ++ tailWord_1030501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030501).length < 2 ^ (prefixWord ++ tailWord_1030501).sum := by decide
  have hdescent : baseEnd_1030501 < baseStart_1030501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030504 : List Nat := [2, 1, 4, 2, 2, 2, 3, 4]
def baseStart_1030504 : Nat := 118140960795 + 1030504 * 2 ^ 59
def prefixEnd_1030504 : Nat := 4983230072969 + 3 ^ 40 * 1030504 * 2
def baseEnd_1030504 : Nat := 156783368409167816906905

theorem tailTrace_1030504 : CollatzResearch.WordTrace tailWord_1030504 prefixEnd_1030504 156783368409167816906905 := by
  unfold tailWord_1030504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18792784329333739458273283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25057045772444985944364377 18792784329333739458273283)
  ·
    refine ⟨28189176494000609187409925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18792784329333739458273283 28189176494000609187409925)
    ·
      refine ⟨5285470592625114222639361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28189176494000609187409925 5285470592625114222639361)
      ·
        refine ⟨3964102944468835666979521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5285470592625114222639361 3964102944468835666979521)
        ·
          refine ⟨2973077208351626750234641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3964102944468835666979521 2973077208351626750234641)
          ·
            refine ⟨2229807906263720062675981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2973077208351626750234641 2229807906263720062675981)
            ·
              refine ⟨836177964848895023503493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2229807906263720062675981 836177964848895023503493)
              ·
                refine ⟨156783368409167816906905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836177964848895023503493 156783368409167816906905)
                ·
                  rfl

theorem cell20_1030504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_1030504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030504 prefixEnd_1030504 := by exact prefixLift 1030504
  have htrace : WordTrace (prefixWord ++ tailWord_1030504) baseStart_1030504 baseEnd_1030504 := by
    simpa [prefixWord, tailWord_1030504, baseEnd_1030504] using wordTrace_append hprefix tailTrace_1030504
  have hstable : (prefixWord ++ tailWord_1030504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030504).length < 2 ^ (prefixWord ++ tailWord_1030504).sum := by decide
  have hdescent : baseEnd_1030504 < baseStart_1030504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030515 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 7]
def baseStart_1030515 : Nat := 118140960795 + 1030515 * 2 ^ 59
def prefixEnd_1030515 : Nat := 4983230072969 + 3 ^ 40 * 1030515 * 2
def baseEnd_1030515 : Nat := 470355125927236301354003

theorem tailTrace_1030515 : CollatzResearch.WordTrace tailWord_1030515 prefixEnd_1030515 470355125927236301354003 := by
  unfold tailWord_1030515
  simp only [CollatzResearch.WordTrace]
  refine ⟨37585969861627627795196999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25057313241085085196797999 37585969861627627795196999)
  ·
    refine ⟨56378954792441441692795499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37585969861627627795196999 56378954792441441692795499)
    ·
      refine ⟨84568432188662162539193249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56378954792441441692795499 84568432188662162539193249)
      ·
        refine ⟨63426324141496621904394937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84568432188662162539193249 63426324141496621904394937)
        ·
          refine ⟨47569743106122466428296203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63426324141496621904394937 47569743106122466428296203)
          ·
            refine ⟨71354614659183699642444305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47569743106122466428296203 71354614659183699642444305)
            ·
              refine ⟨53515960994387774731833229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71354614659183699642444305 53515960994387774731833229)
              ·
                refine ⟨20068485372895415524437461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53515960994387774731833229 20068485372895415524437461)
                ·
                  refine ⟨470355125927236301354003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20068485372895415524437461 470355125927236301354003)
                  ·
                    rfl

theorem cell20_1030515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 7].length) (baseStart_1030515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030515 prefixEnd_1030515 := by exact prefixLift 1030515
  have htrace : WordTrace (prefixWord ++ tailWord_1030515) baseStart_1030515 baseEnd_1030515 := by
    simpa [prefixWord, tailWord_1030515, baseEnd_1030515] using wordTrace_append hprefix tailTrace_1030515
  have hstable : (prefixWord ++ tailWord_1030515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030515).length < 2 ^ (prefixWord ++ tailWord_1030515).sum := by decide
  have hdescent : baseEnd_1030515 < baseStart_1030515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030532 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_1030532 : Nat := 118140960795 + 1030532 * 2 ^ 59
def prefixEnd_1030532 : Nat := 4983230072969 + 3 ^ 40 * 1030532 * 2
def baseEnd_1030532 : Nat := 470362885190459797787267

theorem tailTrace_1030532 : CollatzResearch.WordTrace tailWord_1030532 prefixEnd_1030532 470362885190459797787267 := by
  unfold tailWord_1030532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18793294951283019849282925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25057726601710693132377233 18793294951283019849282925)
  ·
    refine ⟨7047485606731132443481097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18793294951283019849282925 7047485606731132443481097)
    ·
      refine ⟨5285614205048349332610823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7047485606731132443481097 5285614205048349332610823)
      ·
        refine ⟨7928421307572523998916235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5285614205048349332610823 7928421307572523998916235)
        ·
          refine ⟨11892631961358785998374353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7928421307572523998916235 11892631961358785998374353)
          ·
            refine ⟨8919473971019089498780765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11892631961358785998374353 8919473971019089498780765)
            ·
              refine ⟨3344802739132158562042787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8919473971019089498780765 3344802739132158562042787)
              ·
                refine ⟨5017204108698237843064181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344802739132158562042787 5017204108698237843064181)
                ·
                  refine ⟨470362885190459797787267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017204108698237843064181 470362885190459797787267)
                  ·
                    rfl

theorem cell20_1030532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_1030532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030532 prefixEnd_1030532 := by exact prefixLift 1030532
  have htrace : WordTrace (prefixWord ++ tailWord_1030532) baseStart_1030532 baseEnd_1030532 := by
    simpa [prefixWord, tailWord_1030532, baseEnd_1030532] using wordTrace_append hprefix tailTrace_1030532
  have hstable : (prefixWord ++ tailWord_1030532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030532).length < 2 ^ (prefixWord ++ tailWord_1030532).sum := by decide
  have hdescent : baseEnd_1030532 < baseStart_1030532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030539 : List Nat := [1, 1, 1, 1, 4, 4, 1, 3, 4]
def baseStart_1030539 : Nat := 118140960795 + 1030539 * 2 ^ 59
def prefixEnd_1030539 : Nat := 4983230072969 + 3 ^ 40 * 1030539 * 2
def baseEnd_1030539 : Nat := 470366080181198884553905

theorem tailTrace_1030539 : CollatzResearch.WordTrace tailWord_1030539 prefixEnd_1030539 470366080181198884553905 := by
  unfold tailWord_1030539
  simp only [CollatzResearch.WordTrace]
  refine ⟨37586845213540679894070671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25057896809027119929380447 37586845213540679894070671)
  ·
    refine ⟨56380267820311019841106007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37586845213540679894070671 56380267820311019841106007)
    ·
      refine ⟨84570401730466529761659011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56380267820311019841106007 84570401730466529761659011)
      ·
        refine ⟨126855602595699794642488517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84570401730466529761659011 126855602595699794642488517)
        ·
          refine ⟨23785425486693711495466597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126855602595699794642488517 23785425486693711495466597)
          ·
            refine ⟨4459767278755070905399987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23785425486693711495466597 4459767278755070905399987)
            ·
              refine ⟨6689650918132606358099981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459767278755070905399987 6689650918132606358099981)
              ·
                refine ⟨2508619094299727384287493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6689650918132606358099981 2508619094299727384287493)
                ·
                  refine ⟨470366080181198884553905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508619094299727384287493 470366080181198884553905)
                  ·
                    rfl

theorem cell20_1030539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 4].length) (baseStart_1030539 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030539 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030539 prefixEnd_1030539 := by exact prefixLift 1030539
  have htrace : WordTrace (prefixWord ++ tailWord_1030539) baseStart_1030539 baseEnd_1030539 := by
    simpa [prefixWord, tailWord_1030539, baseEnd_1030539] using wordTrace_append hprefix tailTrace_1030539
  have hstable : (prefixWord ++ tailWord_1030539).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030539).length < 2 ^ (prefixWord ++ tailWord_1030539).sum := by decide
  have hdescent : baseEnd_1030539 < baseStart_1030539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030563 : List Nat := [1, 1, 1, 4, 1, 4, 4, 4]
def baseStart_1030563 : Nat := 118140960795 + 1030563 * 2 ^ 59
def prefixEnd_1030563 : Nat := 4983230072969 + 3 ^ 40 * 1030563 * 2
def baseEnd_1030563 : Nat := 156792344811720489251269

theorem tailTrace_1030563 : CollatzResearch.WordTrace tailWord_1030563 prefixEnd_1030563 156792344811720489251269 := by
  unfold tailWord_1030563
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587720565453731992944343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25058480376969154661962895 37587720565453731992944343)
  ·
    refine ⟨56381580848180597989416515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37587720565453731992944343 56381580848180597989416515)
    ·
      refine ⟨84572371272270896984124773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56381580848180597989416515 84572371272270896984124773)
      ·
        refine ⟨15857319613550793184523395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84572371272270896984124773 15857319613550793184523395)
        ·
          refine ⟨23785979420326189776785093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15857319613550793184523395 23785979420326189776785093)
          ·
            refine ⟨4459871141311160583147205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23785979420326189776785093 4459871141311160583147205)
            ·
              refine ⟨836225838995842609340101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4459871141311160583147205 836225838995842609340101)
              ·
                refine ⟨156792344811720489251269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836225838995842609340101 156792344811720489251269)
                ·
                  rfl

theorem cell20_1030563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_1030563 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030563 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030563 prefixEnd_1030563 := by exact prefixLift 1030563
  have htrace : WordTrace (prefixWord ++ tailWord_1030563) baseStart_1030563 baseEnd_1030563 := by
    simpa [prefixWord, tailWord_1030563, baseEnd_1030563] using wordTrace_append hprefix tailTrace_1030563
  have hstable : (prefixWord ++ tailWord_1030563).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030563).length < 2 ^ (prefixWord ++ tailWord_1030563).sum := by decide
  have hdescent : baseEnd_1030563 < baseStart_1030563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030642 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_1030642 : Nat := 118140960795 + 1030642 * 2 ^ 59
def prefixEnd_1030642 : Nat := 4983230072969 + 3 ^ 40 * 1030642 * 2
def baseEnd_1030642 : Nat := 470413092187788304120151

theorem tailTrace_1030642 : CollatzResearch.WordTrace tailWord_1030642 prefixEnd_1030642 470413092187788304120151 := by
  unfold tailWord_1030642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9397650483041882121267545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25060401288111685656713453 9397650483041882121267545)
  ·
    refine ⟨7048237862281411590950659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9397650483041882121267545 7048237862281411590950659)
    ·
      refine ⟨10572356793422117386425989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048237862281411590950659 10572356793422117386425989)
      ·
        refine ⟨1982316898766647009954873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10572356793422117386425989 1982316898766647009954873)
        ·
          refine ⟨1486737674074985257466155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982316898766647009954873 1486737674074985257466155)
          ·
            refine ⟨2230106511112477886199233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486737674074985257466155 2230106511112477886199233)
            ·
              refine ⟨1672579883334358414649425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230106511112477886199233 1672579883334358414649425)
              ·
                refine ⟨1254434912500768810987069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672579883334358414649425 1254434912500768810987069)
                ·
                  refine ⟨470413092187788304120151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254434912500768810987069 470413092187788304120151)
                  ·
                    rfl

theorem cell20_1030642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_1030642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030642 prefixEnd_1030642 := by exact prefixLift 1030642
  have htrace : WordTrace (prefixWord ++ tailWord_1030642) baseStart_1030642 baseEnd_1030642 := by
    simpa [prefixWord, tailWord_1030642, baseEnd_1030642] using wordTrace_append hprefix tailTrace_1030642
  have hstable : (prefixWord ++ tailWord_1030642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030642).length < 2 ^ (prefixWord ++ tailWord_1030642).sum := by decide
  have hdescent : baseEnd_1030642 < baseStart_1030642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030649 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 2]
def baseStart_1030649 : Nat := 118140960795 + 1030649 * 2 ^ 59
def prefixEnd_1030649 : Nat := 4983230072969 + 3 ^ 40 * 1030649 * 2
def baseEnd_1030649 : Nat := 470416287178527390886789

theorem tailTrace_1030649 : CollatzResearch.WordTrace tailWord_1030649 prefixEnd_1030649 470416287178527390886789 := by
  unfold tailWord_1030649
  simp only [CollatzResearch.WordTrace]
  refine ⟨37590857243142168680575001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25060571495428112453716667 37590857243142168680575001)
  ·
    refine ⟨28193142932356626510431251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37590857243142168680575001 28193142932356626510431251)
    ·
      refine ⟨42289714398534939765646877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28193142932356626510431251 42289714398534939765646877)
      ·
        refine ⟨15858642899450602412117579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42289714398534939765646877 15858642899450602412117579)
        ·
          refine ⟨23787964349175903618176369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15858642899450602412117579 23787964349175903618176369)
          ·
            refine ⟨17840973261881927713632277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23787964349175903618176369 17840973261881927713632277)
            ·
              refine ⟨836295621650715361576513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17840973261881927713632277 836295621650715361576513)
              ·
                refine ⟨627221716238036521182385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836295621650715361576513 627221716238036521182385)
                ·
                  refine ⟨470416287178527390886789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627221716238036521182385 470416287178527390886789)
                  ·
                    rfl

theorem cell20_1030649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 2].length) (baseStart_1030649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030649 prefixEnd_1030649 := by exact prefixLift 1030649
  have htrace : WordTrace (prefixWord ++ tailWord_1030649) baseStart_1030649 baseEnd_1030649 := by
    simpa [prefixWord, tailWord_1030649, baseEnd_1030649] using wordTrace_append hprefix tailTrace_1030649
  have hstable : (prefixWord ++ tailWord_1030649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030649).length < 2 ^ (prefixWord ++ tailWord_1030649).sum := by decide
  have hdescent : baseEnd_1030649 < baseStart_1030649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030653 : List Nat := [1, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1030653 : Nat := 118140960795 + 1030653 * 2 ^ 59
def prefixEnd_1030653 : Nat := 4983230072969 + 3 ^ 40 * 1030653 * 2
def baseEnd_1030653 : Nat := 470418112887521154753439

theorem tailTrace_1030653 : CollatzResearch.WordTrace tailWord_1030653 prefixEnd_1030653 470418112887521154753439 := by
  unfold tailWord_1030653
  simp only [CollatzResearch.WordTrace]
  refine ⟨37591003135127677363720613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25060668756751784909147075 37591003135127677363720613)
  ·
    refine ⟨7048313087836439505697615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37591003135127677363720613 7048313087836439505697615)
    ·
      refine ⟨10572469631754659258546423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048313087836439505697615 10572469631754659258546423)
      ·
        refine ⟨15858704447631988887819635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10572469631754659258546423 15858704447631988887819635)
        ·
          refine ⟨23788056671447983331729453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15858704447631988887819635 23788056671447983331729453)
          ·
            refine ⟨8920521251792993749398545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23788056671447983331729453 8920521251792993749398545)
            ·
              refine ⟨6690390938844745312048909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8920521251792993749398545 6690390938844745312048909)
              ·
                refine ⟨2508896602066779492018341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6690390938844745312048909 2508896602066779492018341)
                ·
                  refine ⟨470418112887521154753439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508896602066779492018341 470418112887521154753439)
                  ·
                    rfl

theorem cell20_1030653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1030653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030653 prefixEnd_1030653 := by exact prefixLift 1030653
  have htrace : WordTrace (prefixWord ++ tailWord_1030653) baseStart_1030653 baseEnd_1030653 := by
    simpa [prefixWord, tailWord_1030653, baseEnd_1030653] using wordTrace_append hprefix tailTrace_1030653
  have hstable : (prefixWord ++ tailWord_1030653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030653).length < 2 ^ (prefixWord ++ tailWord_1030653).sum := by decide
  have hdescent : baseEnd_1030653 < baseStart_1030653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030670 : List Nat := [4, 1, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1030670 : Nat := 118140960795 + 1030670 * 2 ^ 59
def prefixEnd_1030670 : Nat := 4983230072969 + 3 ^ 40 * 1030670 * 2
def baseEnd_1030670 : Nat := 470425872150744651186703

theorem tailTrace_1030670 : CollatzResearch.WordTrace tailWord_1030670 prefixEnd_1030670 470425872150744651186703 := by
  unfold tailWord_1030670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698952897008261158386183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25061082117377392844726309 4698952897008261158386183)
  ·
    refine ⟨7048429345512391737579275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4698952897008261158386183 7048429345512391737579275)
    ·
      refine ⟨10572644018268587606368913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7048429345512391737579275 10572644018268587606368913)
      ·
        refine ⟨7929483013701440704776685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10572644018268587606368913 7929483013701440704776685)
        ·
          refine ⟨2973556130138040264291257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7929483013701440704776685 2973556130138040264291257)
          ·
            refine ⟨2230167097603530198218443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2973556130138040264291257 2230167097603530198218443)
            ·
              refine ⟨3345250646405295297327665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230167097603530198218443 3345250646405295297327665)
              ·
                refine ⟨2508937984803971472995749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3345250646405295297327665 2508937984803971472995749)
                ·
                  refine ⟨470425872150744651186703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508937984803971472995749 470425872150744651186703)
                  ·
                    rfl

theorem cell20_1030670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1030670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030670 prefixEnd_1030670 := by exact prefixLift 1030670
  have htrace : WordTrace (prefixWord ++ tailWord_1030670) baseStart_1030670 baseEnd_1030670 := by
    simpa [prefixWord, tailWord_1030670, baseEnd_1030670] using wordTrace_append hprefix tailTrace_1030670
  have hstable : (prefixWord ++ tailWord_1030670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030670).length < 2 ^ (prefixWord ++ tailWord_1030670).sum := by decide
  have hdescent : baseEnd_1030670 < baseStart_1030670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030677 : List Nat := [1, 3, 2, 1, 3, 1, 5, 4]
def baseStart_1030677 : Nat := 118140960795 + 1030677 * 2 ^ 59
def prefixEnd_1030677 : Nat := 4983230072969 + 3 ^ 40 * 1030677 * 2
def baseEnd_1030677 : Nat := 156809689047161245984447

theorem tailTrace_1030677 : CollatzResearch.WordTrace tailWord_1030677 prefixEnd_1030677 156809689047161245984447 := by
  unfold tailWord_1030677
  simp only [CollatzResearch.WordTrace]
  refine ⟨37591878487040729462594285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25061252324693819641729523 37591878487040729462594285)
  ·
    refine ⟨14096954432640273548472857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37591878487040729462594285 14096954432640273548472857)
    ·
      refine ⟨10572715824480205161354643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14096954432640273548472857 10572715824480205161354643)
      ·
        refine ⟨15859073736720307742031965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10572715824480205161354643 15859073736720307742031965)
        ·
          refine ⟨5947152651270115403261987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15859073736720307742031965 5947152651270115403261987)
          ·
            refine ⟨8920728976905173104892981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5947152651270115403261987 8920728976905173104892981)
            ·
              refine ⟨836318341584859978583717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8920728976905173104892981 836318341584859978583717)
              ·
                refine ⟨156809689047161245984447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836318341584859978583717 156809689047161245984447)
                ·
                  rfl

theorem cell20_1030677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_1030677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030677 prefixEnd_1030677 := by exact prefixLift 1030677
  have htrace : WordTrace (prefixWord ++ tailWord_1030677) baseStart_1030677 baseEnd_1030677 := by
    simpa [prefixWord, tailWord_1030677, baseEnd_1030677] using wordTrace_append hprefix tailTrace_1030677
  have hstable : (prefixWord ++ tailWord_1030677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030677).length < 2 ^ (prefixWord ++ tailWord_1030677).sum := by decide
  have hdescent : baseEnd_1030677 < baseStart_1030677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030743 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_1030743 : Nat := 118140960795 + 1030743 * 2 ^ 59
def prefixEnd_1030743 : Nat := 4983230072969 + 3 ^ 40 * 1030743 * 2
def baseEnd_1030743 : Nat := 470459191339880841753071

theorem tailTrace_1030743 : CollatzResearch.WordTrace tailWord_1030743 prefixEnd_1030743 470459191339880841753071 := by
  unfold tailWord_1030743
  simp only [CollatzResearch.WordTrace]
  refine ⟨37594285704801622734496883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25062857136534415156331255 37594285704801622734496883)
  ·
    refine ⟨56391428557202434101745325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37594285704801622734496883 56391428557202434101745325)
    ·
      refine ⟨21146785708950912788154497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56391428557202434101745325 21146785708950912788154497)
      ·
        refine ⟨15860089281713184591115873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21146785708950912788154497 15860089281713184591115873)
        ·
          refine ⟨11895066961284888443336905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15860089281713184591115873 11895066961284888443336905)
          ·
            refine ⟨8921300220963666332502679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11895066961284888443336905 8921300220963666332502679)
            ·
              refine ⟨13381950331445499498754019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8921300220963666332502679 13381950331445499498754019)
              ·
                refine ⟨20072925497168249248131029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13381950331445499498754019 20072925497168249248131029)
                ·
                  refine ⟨470459191339880841753071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20072925497168249248131029 470459191339880841753071)
                  ·
                    rfl

theorem cell20_1030743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_1030743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030743 prefixEnd_1030743 := by exact prefixLift 1030743
  have htrace : WordTrace (prefixWord ++ tailWord_1030743) baseStart_1030743 baseEnd_1030743 := by
    simpa [prefixWord, tailWord_1030743, baseEnd_1030743] using wordTrace_append hprefix tailTrace_1030743
  have hstable : (prefixWord ++ tailWord_1030743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030743).length < 2 ^ (prefixWord ++ tailWord_1030743).sum := by decide
  have hdescent : baseEnd_1030743 < baseStart_1030743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030767 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 4]
def baseStart_1030767 : Nat := 118140960795 + 1030767 * 2 ^ 59
def prefixEnd_1030767 : Nat := 4983230072969 + 3 ^ 40 * 1030767 * 2
def baseEnd_1030767 : Nat := 470470145593843424952973

theorem tailTrace_1030767 : CollatzResearch.WordTrace tailWord_1030767 prefixEnd_1030767 470470145593843424952973 := by
  unfold tailWord_1030767
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595161056714674833370555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25063440704476449888913703 37595161056714674833370555)
  ·
    refine ⟨56392741585072012250055833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37595161056714674833370555 56392741585072012250055833)
    ·
      refine ⟨42294556188804009187541875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56392741585072012250055833 42294556188804009187541875)
      ·
        refine ⟨63441834283206013781312813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42294556188804009187541875 63441834283206013781312813)
        ·
          refine ⟨23790687856202255167992305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63441834283206013781312813 23790687856202255167992305)
          ·
            refine ⟨17843015892151691375994229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23790687856202255167992305 17843015892151691375994229)
            ·
              refine ⟨1672782739889221066499459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17843015892151691375994229 1672782739889221066499459)
              ·
                refine ⟨2509174109833831599749189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672782739889221066499459 2509174109833831599749189)
                ·
                  refine ⟨470470145593843424952973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509174109833831599749189 470470145593843424952973)
                  ·
                    rfl

theorem cell20_1030767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 4].length) (baseStart_1030767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030767 prefixEnd_1030767 := by exact prefixLift 1030767
  have htrace : WordTrace (prefixWord ++ tailWord_1030767) baseStart_1030767 baseEnd_1030767 := by
    simpa [prefixWord, tailWord_1030767, baseEnd_1030767] using wordTrace_append hprefix tailTrace_1030767
  have hstable : (prefixWord ++ tailWord_1030767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030767).length < 2 ^ (prefixWord ++ tailWord_1030767).sum := by decide
  have hdescent : baseEnd_1030767 < baseStart_1030767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030773 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 3]
def baseStart_1030773 : Nat := 118140960795 + 1030773 * 2 ^ 59
def prefixEnd_1030773 : Nat := 4983230072969 + 3 ^ 40 * 1030773 * 2
def baseEnd_1030773 : Nat := 470472884157334070752949

theorem tailTrace_1030773 : CollatzResearch.WordTrace tailWord_1030773 prefixEnd_1030773 470472884157334070752949 := by
  unfold tailWord_1030773
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595379894692937858088973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25063586596461958572059315 37595379894692937858088973)
  ·
    refine ⟨14098267460509851696783365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37595379894692937858088973 14098267460509851696783365)
    ·
      refine ⟨2643425148845597193146881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14098267460509851696783365 2643425148845597193146881)
      ·
        refine ⟨1982568861634197894860161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643425148845597193146881 1982568861634197894860161)
        ·
          refine ⟨1486926646225648421145121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982568861634197894860161 1486926646225648421145121)
          ·
            refine ⟨1115194984669236315858841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1486926646225648421145121 1115194984669236315858841)
            ·
              refine ⟨836396238501927236894131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115194984669236315858841 836396238501927236894131)
              ·
                refine ⟨1254594357752890855341197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836396238501927236894131 1254594357752890855341197)
                ·
                  refine ⟨470472884157334070752949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254594357752890855341197 470472884157334070752949)
                  ·
                    rfl

theorem cell20_1030773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_1030773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030773 prefixEnd_1030773 := by exact prefixLift 1030773
  have htrace : WordTrace (prefixWord ++ tailWord_1030773) baseStart_1030773 baseEnd_1030773 := by
    simpa [prefixWord, tailWord_1030773, baseEnd_1030773] using wordTrace_append hprefix tailTrace_1030773
  have hstable : (prefixWord ++ tailWord_1030773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030773).length < 2 ^ (prefixWord ++ tailWord_1030773).sum := by decide
  have hdescent : baseEnd_1030773 < baseStart_1030773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030777 : List Nat := [1, 2, 1, 3, 3, 2, 4, 1, 3]
def baseStart_1030777 : Nat := 118140960795 + 1030777 * 2 ^ 59
def prefixEnd_1030777 : Nat := 4983230072969 + 3 ^ 40 * 1030777 * 2
def baseEnd_1030777 : Nat := 470474709866327834619599

theorem tailTrace_1030777 : CollatzResearch.WordTrace tailWord_1030777 prefixEnd_1030777 470474709866327834619599 := by
  unfold tailWord_1030777
  simp only [CollatzResearch.WordTrace]
  refine ⟨37595525786678446541234585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25063683857785631027489723 37595525786678446541234585)
  ·
    refine ⟨28196644340008834905925939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37595525786678446541234585 28196644340008834905925939)
    ·
      refine ⟨42294966510013252358888909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28196644340008834905925939 42294966510013252358888909)
      ·
        refine ⟨15860612441254969634583341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42294966510013252358888909 15860612441254969634583341)
        ·
          refine ⟨5947729665470613612968753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15860612441254969634583341 5947729665470613612968753)
          ·
            refine ⟨4460797249102960209726565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947729665470613612968753 4460797249102960209726565)
            ·
              refine ⟨836399484206805039323731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4460797249102960209726565 836399484206805039323731)
              ·
                refine ⟨1254599226310207558985597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836399484206805039323731 1254599226310207558985597)
                ·
                  refine ⟨470474709866327834619599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254599226310207558985597 470474709866327834619599)
                  ·
                    rfl

theorem cell20_1030777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_1030777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030777 prefixEnd_1030777 := by exact prefixLift 1030777
  have htrace : WordTrace (prefixWord ++ tailWord_1030777) baseStart_1030777 baseEnd_1030777 := by
    simpa [prefixWord, tailWord_1030777, baseEnd_1030777] using wordTrace_append hprefix tailTrace_1030777
  have hstable : (prefixWord ++ tailWord_1030777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030777).length < 2 ^ (prefixWord ++ tailWord_1030777).sum := by decide
  have hdescent : baseEnd_1030777 < baseStart_1030777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030812 : List Nat := [2, 2, 3, 2, 2, 9]
def baseStart_1030812 : Nat := 118140960795 + 1030812 * 2 ^ 59
def prefixEnd_1030812 : Nat := 4983230072969 + 3 ^ 40 * 1030812 * 2
def baseEnd_1030812 : Nat := 17425580919260121053807

theorem tailTrace_1030812 : CollatzResearch.WordTrace tailWord_1030812 prefixEnd_1030812 17425580919260121053807 := by
  unfold tailWord_1030812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18798401170775823759379345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25064534894367765012505793 18798401170775823759379345)
  ·
    refine ⟨14098800878081867819534509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18798401170775823759379345 14098800878081867819534509)
    ·
      refine ⟨5287050329280700432325441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14098800878081867819534509 5287050329280700432325441)
      ·
        refine ⟨3965287746960525324244081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5287050329280700432325441 3965287746960525324244081)
        ·
          refine ⟨2973965810220393993183061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3965287746960525324244081 2973965810220393993183061)
          ·
            refine ⟨17425580919260121053807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2973965810220393993183061 17425580919260121053807)
            ·
              rfl

theorem cell20_1030812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 9].length) (baseStart_1030812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030812 prefixEnd_1030812 := by exact prefixLift 1030812
  have htrace : WordTrace (prefixWord ++ tailWord_1030812) baseStart_1030812 baseEnd_1030812 := by
    simpa [prefixWord, tailWord_1030812, baseEnd_1030812] using wordTrace_append hprefix tailTrace_1030812
  have hstable : (prefixWord ++ tailWord_1030812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030812).length < 2 ^ (prefixWord ++ tailWord_1030812).sum := by decide
  have hdescent : baseEnd_1030812 < baseStart_1030812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030829 : List Nat := [1, 5, 2, 1, 1, 2, 3, 5]
def baseStart_1030829 : Nat := 118140960795 + 1030829 * 2 ^ 59
def prefixEnd_1030829 : Nat := 4983230072969 + 3 ^ 40 * 1030829 * 2
def baseEnd_1030829 : Nat := 156832814694415588295351

theorem tailTrace_1030829 : CollatzResearch.WordTrace tailWord_1030829 prefixEnd_1030829 156832814694415588295351 := by
  unfold tailWord_1030829
  simp only [CollatzResearch.WordTrace]
  refine ⟨37597422382490059422127541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25064948254993372948085027 37597422382490059422127541)
  ·
    refine ⟨3524758348358443070824457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37597422382490059422127541 3524758348358443070824457)
    ·
      refine ⟨2643568761268832303118343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3524758348358443070824457 2643568761268832303118343)
      ·
        refine ⟨3965353141903248454677515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2643568761268832303118343 3965353141903248454677515)
        ·
          refine ⟨5948029712854872682016273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3965353141903248454677515 5948029712854872682016273)
          ·
            refine ⟨4461022284641154511512205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5948029712854872682016273 4461022284641154511512205)
            ·
              refine ⟨1672883356740432941817077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4461022284641154511512205 1672883356740432941817077)
              ·
                refine ⟨156832814694415588295351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1672883356740432941817077 156832814694415588295351)
                ·
                  rfl

theorem cell20_1030829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 5].length) (baseStart_1030829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030829 prefixEnd_1030829 := by exact prefixLift 1030829
  have htrace : WordTrace (prefixWord ++ tailWord_1030829) baseStart_1030829 baseEnd_1030829 := by
    simpa [prefixWord, tailWord_1030829, baseEnd_1030829] using wordTrace_append hprefix tailTrace_1030829
  have hstable : (prefixWord ++ tailWord_1030829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030829).length < 2 ^ (prefixWord ++ tailWord_1030829).sum := by decide
  have hdescent : baseEnd_1030829 < baseStart_1030829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030881 : List Nat := [1, 2, 3, 1, 4, 1, 1, 3, 4]
def baseStart_1030881 : Nat := 118140960795 + 1030881 * 2 ^ 59
def prefixEnd_1030881 : Nat := 4983230072969 + 3 ^ 40 * 1030881 * 2
def baseEnd_1030881 : Nat := 470522178300165695152507

theorem tailTrace_1030881 : CollatzResearch.WordTrace tailWord_1030881 prefixEnd_1030881 470522178300165695152507 := by
  unfold tailWord_1030881
  simp only [CollatzResearch.WordTrace]
  refine ⟨37599318978301672303020497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25066212652201114868680331 37599318978301672303020497)
  ·
    refine ⟨28199489233726254227265373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37599318978301672303020497 28199489233726254227265373)
    ·
      refine ⟨10574808462647345335224515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28199489233726254227265373 10574808462647345335224515)
      ·
        refine ⟨15862212693971018002836773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10574808462647345335224515 15862212693971018002836773)
        ·
          refine ⟨2974164880119565875531895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15862212693971018002836773 2974164880119565875531895)
          ·
            refine ⟨4461247320179348813297843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974164880119565875531895 4461247320179348813297843)
            ·
              refine ⟨6691870980269023219946765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461247320179348813297843 6691870980269023219946765)
              ·
                refine ⟨2509451617600883707480037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6691870980269023219946765 2509451617600883707480037)
                ·
                  refine ⟨470522178300165695152507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509451617600883707480037 470522178300165695152507)
                  ·
                    rfl

theorem cell20_1030881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 4].length) (baseStart_1030881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030881 prefixEnd_1030881 := by exact prefixLift 1030881
  have htrace : WordTrace (prefixWord ++ tailWord_1030881) baseStart_1030881 baseEnd_1030881 := by
    simpa [prefixWord, tailWord_1030881, baseEnd_1030881] using wordTrace_append hprefix tailTrace_1030881
  have hstable : (prefixWord ++ tailWord_1030881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030881).length < 2 ^ (prefixWord ++ tailWord_1030881).sum := by decide
  have hdescent : baseEnd_1030881 < baseStart_1030881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030901 : List Nat := [1, 3, 6, 1, 1, 1, 1, 6]
def baseStart_1030901 : Nat := 118140960795 + 1030901 * 2 ^ 59
def prefixEnd_1030901 : Nat := 4983230072969 + 3 ^ 40 * 1030901 * 2
def baseEnd_1030901 : Nat := 156843768948378171495253

theorem tailTrace_1030901 : CollatzResearch.WordTrace tailWord_1030901 prefixEnd_1030901 156843768948378171495253 := by
  unfold tailWord_1030901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37600048438229215718748557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25066698958819477145832371 37600048438229215718748557)
  ·
    refine ⟨14100018164335955894530709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37600048438229215718748557 14100018164335955894530709)
    ·
      refine ⟨660938351453247932556127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 14100018164335955894530709 660938351453247932556127)
      ·
        refine ⟨991407527179871898834191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660938351453247932556127 991407527179871898834191)
        ·
          refine ⟨1487111290769807848251287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991407527179871898834191 1487111290769807848251287)
          ·
            refine ⟨2230666936154711772376931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487111290769807848251287 2230666936154711772376931)
            ·
              refine ⟨3346000404232067658565397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230666936154711772376931 3346000404232067658565397)
              ·
                refine ⟨156843768948378171495253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3346000404232067658565397 156843768948378171495253)
                ·
                  rfl

theorem cell20_1030901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 6].length) (baseStart_1030901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030901 prefixEnd_1030901 := by exact prefixLift 1030901
  have htrace : WordTrace (prefixWord ++ tailWord_1030901) baseStart_1030901 baseEnd_1030901 := by
    simpa [prefixWord, tailWord_1030901, baseEnd_1030901] using wordTrace_append hprefix tailTrace_1030901
  have hstable : (prefixWord ++ tailWord_1030901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030901).length < 2 ^ (prefixWord ++ tailWord_1030901).sum := by decide
  have hdescent : baseEnd_1030901 < baseStart_1030901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030933 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1030933 : Nat := 118140960795 + 1030933 * 2 ^ 59
def prefixEnd_1030933 : Nat := 4983230072969 + 3 ^ 40 * 1030933 * 2
def baseEnd_1030933 : Nat := 470545912517084625418961

theorem tailTrace_1030933 : CollatzResearch.WordTrace tailWord_1030933 prefixEnd_1030933 470545912517084625418961 := by
  unfold tailWord_1030933
  simp only [CollatzResearch.WordTrace]
  refine ⟨37601215574113285183913453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25067477049408856789275635 37601215574113285183913453)
  ·
    refine ⟨14100455840292481943967545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37601215574113285183913453 14100455840292481943967545)
    ·
      refine ⟨10575341880219361457975659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14100455840292481943967545 10575341880219361457975659)
      ·
        refine ⟨15863012820329042186963489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10575341880219361457975659 15863012820329042186963489)
        ·
          refine ⟨11897259615246781640222617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15863012820329042186963489 11897259615246781640222617)
          ·
            refine ⟨8922944711435086230166963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11897259615246781640222617 8922944711435086230166963)
            ·
              refine ⟨13384417067152629345250445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8922944711435086230166963 13384417067152629345250445)
              ·
                refine ⟨5019156400182236004468917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13384417067152629345250445 5019156400182236004468917)
                ·
                  refine ⟨470545912517084625418961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5019156400182236004468917 470545912517084625418961)
                  ·
                    rfl

theorem cell20_1030933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1030933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030933 prefixEnd_1030933 := by exact prefixLift 1030933
  have htrace : WordTrace (prefixWord ++ tailWord_1030933) baseStart_1030933 baseEnd_1030933 := by
    simpa [prefixWord, tailWord_1030933, baseEnd_1030933] using wordTrace_append hprefix tailTrace_1030933
  have hstable : (prefixWord ++ tailWord_1030933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030933).length < 2 ^ (prefixWord ++ tailWord_1030933).sum := by decide
  have hdescent : baseEnd_1030933 < baseStart_1030933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030946 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 3]
def baseStart_1030946 : Nat := 118140960795 + 1030946 * 2 ^ 59
def prefixEnd_1030946 : Nat := 4983230072969 + 3 ^ 40 * 1030946 * 2
def baseEnd_1030946 : Nat := 470551846071314357985575

theorem tailTrace_1030946 : CollatzResearch.WordTrace tailWord_1030946 prefixEnd_1030946 470551846071314357985575 := by
  unfold tailWord_1030946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400422430766547101034173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25067793148710792269424461 9400422430766547101034173)
  ·
    refine ⟨3525158411537455162887815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9400422430766547101034173 3525158411537455162887815)
    ·
      refine ⟨5287737617306182744331723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525158411537455162887815 5287737617306182744331723)
      ·
        refine ⟨7931606425959274116497585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5287737617306182744331723 7931606425959274116497585)
        ·
          refine ⟨5948704819469455587373189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931606425959274116497585 5948704819469455587373189)
          ·
            refine ⟨1115382153650522922632473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5948704819469455587373189 1115382153650522922632473)
            ·
              refine ⟨836536615237892191974355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115382153650522922632473 836536615237892191974355)
              ·
                refine ⟨1254804922856838287961533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836536615237892191974355 1254804922856838287961533)
                ·
                  refine ⟨470551846071314357985575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254804922856838287961533 470551846071314357985575)
                  ·
                    rfl

theorem cell20_1030946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_1030946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030946 prefixEnd_1030946 := by exact prefixLift 1030946
  have htrace : WordTrace (prefixWord ++ tailWord_1030946) baseStart_1030946 baseEnd_1030946 := by
    simpa [prefixWord, tailWord_1030946, baseEnd_1030946] using wordTrace_append hprefix tailTrace_1030946
  have hstable : (prefixWord ++ tailWord_1030946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030946).length < 2 ^ (prefixWord ++ tailWord_1030946).sum := by decide
  have hdescent : baseEnd_1030946 < baseStart_1030946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030985 : List Nat := [1, 2, 1, 1, 2, 13]
def baseStart_1030985 : Nat := 118140960795 + 1030985 * 2 ^ 59
def prefixEnd_1030985 : Nat := 4983230072969 + 3 ^ 40 * 1030985 * 2
def baseEnd_1030985 : Nat := 17428505434592724284645

theorem tailTrace_1030985 : CollatzResearch.WordTrace tailWord_1030985 prefixEnd_1030985 17428505434592724284645 := by
  unfold tailWord_1030985
  simp only [CollatzResearch.WordTrace]
  refine ⟨37603112169924898064806409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25068741446616598709870939 37603112169924898064806409)
  ·
    refine ⟨28202334127443673548604807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37603112169924898064806409 28202334127443673548604807)
    ·
      refine ⟨42303501191165510322907211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28202334127443673548604807 42303501191165510322907211)
      ·
        refine ⟨63455251786748265484360817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42303501191165510322907211 63455251786748265484360817)
        ·
          refine ⟨47591438840061199113270613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63455251786748265484360817 47591438840061199113270613)
          ·
            refine ⟨17428505434592724284645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 47591438840061199113270613 17428505434592724284645)
            ·
              rfl

theorem cell20_1030985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 13].length) (baseStart_1030985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030985 prefixEnd_1030985 := by exact prefixLift 1030985
  have htrace : WordTrace (prefixWord ++ tailWord_1030985) baseStart_1030985 baseEnd_1030985 := by
    simpa [prefixWord, tailWord_1030985, baseEnd_1030985] using wordTrace_append hprefix tailTrace_1030985
  have hstable : (prefixWord ++ tailWord_1030985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030985).length < 2 ^ (prefixWord ++ tailWord_1030985).sum := by decide
  have hdescent : baseEnd_1030985 < baseStart_1030985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1030988 : List Nat := [2, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_1030988 : Nat := 118140960795 + 1030988 * 2 ^ 59
def prefixEnd_1030988 : Nat := 4983230072969 + 3 ^ 40 * 1030988 * 2
def baseEnd_1030988 : Nat := 470571016015748878585403

theorem tailTrace_1030988 : CollatzResearch.WordTrace tailWord_1030988 prefixEnd_1030988 470571016015748878585403 := by
  unfold tailWord_1030988
  simp only [CollatzResearch.WordTrace]
  refine ⟨18801610794457014788582809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25068814392609353051443745 18801610794457014788582809)
  ·
    refine ⟨14101208095842761091437107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18801610794457014788582809 14101208095842761091437107)
    ·
      refine ⟨21151812143764141637155661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14101208095842761091437107 21151812143764141637155661)
      ·
        refine ⟨7931929553911553113933373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21151812143764141637155661 7931929553911553113933373)
        ·
          refine ⟨2974473582716832417725015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7931929553911553113933373 2974473582716832417725015)
          ·
            refine ⟨4461710374075248626587523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974473582716832417725015 4461710374075248626587523)
            ·
              refine ⟨6692565561112872939881285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461710374075248626587523 6692565561112872939881285)
              ·
                refine ⟨1254856042708663676227741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6692565561112872939881285 1254856042708663676227741)
                ·
                  refine ⟨470571016015748878585403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254856042708663676227741 470571016015748878585403)
                  ·
                    rfl

theorem cell20_1030988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_1030988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1030988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1030988 prefixEnd_1030988 := by exact prefixLift 1030988
  have htrace : WordTrace (prefixWord ++ tailWord_1030988) baseStart_1030988 baseEnd_1030988 := by
    simpa [prefixWord, tailWord_1030988, baseEnd_1030988] using wordTrace_append hprefix tailTrace_1030988
  have hstable : (prefixWord ++ tailWord_1030988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1030988).length < 2 ^ (prefixWord ++ tailWord_1030988).sum := by decide
  have hdescent : baseEnd_1030988 < baseStart_1030988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1030988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031002 : List Nat := [3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_1031002 : Nat := 118140960795 + 1031002 * 2 ^ 59
def prefixEnd_1031002 : Nat := 4983230072969 + 3 ^ 40 * 1031002 * 2
def baseEnd_1031002 : Nat := 156859135332409017372893

theorem tailTrace_1031002 : CollatzResearch.WordTrace tailWord_1031002 prefixEnd_1031002 156859135332409017372893 := by
  unfold tailWord_1031002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400933052715827492043815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25069154807242206645450173 9400933052715827492043815)
  ·
    refine ⟨14101399579073741238065723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9400933052715827492043815 14101399579073741238065723)
    ·
      refine ⟨21152099368610611857098585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14101399579073741238065723 21152099368610611857098585)
      ·
        refine ⟨15864074526457958892823939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21152099368610611857098585 15864074526457958892823939)
        ·
          refine ⟨23796111789686938339235909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15864074526457958892823939 23796111789686938339235909)
          ·
            refine ⟨4461770960566300938606733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23796111789686938339235909 4461770960566300938606733)
            ·
              refine ⟨1673164110212362851977525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4461770960566300938606733 1673164110212362851977525)
              ·
                refine ⟨156859135332409017372893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673164110212362851977525 156859135332409017372893)
                ·
                  rfl

theorem cell20_1031002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_1031002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031002 prefixEnd_1031002 := by exact prefixLift 1031002
  have htrace : WordTrace (prefixWord ++ tailWord_1031002) baseStart_1031002 baseEnd_1031002 := by
    simpa [prefixWord, tailWord_1031002, baseEnd_1031002] using wordTrace_append hprefix tailTrace_1031002
  have hstable : (prefixWord ++ tailWord_1031002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031002).length < 2 ^ (prefixWord ++ tailWord_1031002).sum := by decide
  have hdescent : baseEnd_1031002 < baseStart_1031002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031023 : List Nat := [1, 1, 2, 1, 3, 1, 1, 10]
def baseStart_1031023 : Nat := 118140960795 + 1031023 * 2 ^ 59
def prefixEnd_1031023 : Nat := 4983230072969 + 3 ^ 40 * 1031023 * 2
def baseEnd_1031023 : Nat := 156862330323148104139531

theorem tailTrace_1031023 : CollatzResearch.WordTrace tailWord_1031023 prefixEnd_1031023 156862330323148104139531 := by
  unfold tailWord_1031023
  simp only [CollatzResearch.WordTrace]
  refine ⟨37604498143787230554689723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25069665429191487036459815 37604498143787230554689723)
  ·
    refine ⟨56406747215680845832034585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37604498143787230554689723 56406747215680845832034585)
    ·
      refine ⟨42305060411760634374025939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56406747215680845832034585 42305060411760634374025939)
      ·
        refine ⟨63457590617640951561038909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42305060411760634374025939 63457590617640951561038909)
        ·
          refine ⟨23796596481615356835389591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63457590617640951561038909 23796596481615356835389591)
          ·
            refine ⟨35694894722423035253084387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23796596481615356835389591 35694894722423035253084387)
            ·
              refine ⟨53542342083634552879626581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35694894722423035253084387 53542342083634552879626581)
              ·
                refine ⟨156862330323148104139531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53542342083634552879626581 156862330323148104139531)
                ·
                  rfl

theorem cell20_1031023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 10].length) (baseStart_1031023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031023 prefixEnd_1031023 := by exact prefixLift 1031023
  have htrace : WordTrace (prefixWord ++ tailWord_1031023) baseStart_1031023 baseEnd_1031023 := by
    simpa [prefixWord, tailWord_1031023, baseEnd_1031023] using wordTrace_append hprefix tailTrace_1031023
  have hstable : (prefixWord ++ tailWord_1031023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031023).length < 2 ^ (prefixWord ++ tailWord_1031023).sum := by decide
  have hdescent : baseEnd_1031023 < baseStart_1031023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031029 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 2]
def baseStart_1031029 : Nat := 118140960795 + 1031029 * 2 ^ 59
def prefixEnd_1031029 : Nat := 4983230072969 + 3 ^ 40 * 1031029 * 2
def baseEnd_1031029 : Nat := 470589729532934958218569

theorem tailTrace_1031029 : CollatzResearch.WordTrace tailWord_1031029 prefixEnd_1031029 470589729532934958218569 := by
  unfold tailWord_1031029
  simp only [CollatzResearch.WordTrace]
  refine ⟨37604716981765493579408141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25069811321176995719605427 37604716981765493579408141)
  ·
    refine ⟨14101768868162060092278053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37604716981765493579408141 14101768868162060092278053)
    ·
      refine ⟨2644081662780386267302135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14101768868162060092278053 2644081662780386267302135)
      ·
        refine ⟨3966122494170579400953203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2644081662780386267302135 3966122494170579400953203)
        ·
          refine ⟨5949183741255869101429805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966122494170579400953203 5949183741255869101429805)
          ·
            refine ⟨2230943902970950913036177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5949183741255869101429805 2230943902970950913036177)
            ·
              refine ⟨1673207927228213184777133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230943902970950913036177 1673207927228213184777133)
              ·
                refine ⟨627452972710579944291425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673207927228213184777133 627452972710579944291425)
                ·
                  refine ⟨470589729532934958218569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627452972710579944291425 470589729532934958218569)
                  ·
                    rfl

theorem cell20_1031029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_1031029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031029 prefixEnd_1031029 := by exact prefixLift 1031029
  have htrace : WordTrace (prefixWord ++ tailWord_1031029) baseStart_1031029 baseEnd_1031029 := by
    simpa [prefixWord, tailWord_1031029, baseEnd_1031029] using wordTrace_append hprefix tailTrace_1031029
  have hstable : (prefixWord ++ tailWord_1031029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031029).length < 2 ^ (prefixWord ++ tailWord_1031029).sum := by decide
  have hdescent : baseEnd_1031029 < baseStart_1031029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031050 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_1031050 : Nat := 118140960795 + 1031050 * 2 ^ 59
def prefixEnd_1031050 : Nat := 4983230072969 + 3 ^ 40 * 1031050 * 2
def baseEnd_1031050 : Nat := 470599314505152218518483

theorem tailTrace_1031050 : CollatzResearch.WordTrace tailWord_1031050 prefixEnd_1031050 470599314505152218518483 := by
  unfold tailWord_1031050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401370728672353541480651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25070321943126276110615069 9401370728672353541480651)
  ·
    refine ⟨14102056093008530312220977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401370728672353541480651 14102056093008530312220977)
    ·
      refine ⟨10576542069756397734165733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14102056093008530312220977 10576542069756397734165733)
      ·
        refine ⟨1983101638079324575156075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10576542069756397734165733 1983101638079324575156075)
        ·
          refine ⟨2974652457118986862734113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983101638079324575156075 2974652457118986862734113)
          ·
            refine ⟨2230989342839240147050585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974652457118986862734113 2230989342839240147050585)
            ·
              refine ⟨1673242007129430110287939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230989342839240147050585 1673242007129430110287939)
              ·
                refine ⟨2509863010694145165431909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673242007129430110287939 2509863010694145165431909)
                ·
                  refine ⟨470599314505152218518483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509863010694145165431909 470599314505152218518483)
                  ·
                    rfl

theorem cell20_1031050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_1031050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031050 prefixEnd_1031050 := by exact prefixLift 1031050
  have htrace : WordTrace (prefixWord ++ tailWord_1031050) baseStart_1031050 baseEnd_1031050 := by
    simpa [prefixWord, tailWord_1031050, baseEnd_1031050] using wordTrace_append hprefix tailTrace_1031050
  have hstable : (prefixWord ++ tailWord_1031050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031050).length < 2 ^ (prefixWord ++ tailWord_1031050).sum := by decide
  have hdescent : baseEnd_1031050 < baseStart_1031050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031071 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 4]
def baseStart_1031071 : Nat := 118140960795 + 1031071 * 2 ^ 59
def prefixEnd_1031071 : Nat := 4983230072969 + 3 ^ 40 * 1031071 * 2
def baseEnd_1031071 : Nat := 470608899477369478818397

theorem tailTrace_1031071 : CollatzResearch.WordTrace tailWord_1031071 prefixEnd_1031071 470608899477369478818397 := by
  unfold tailWord_1031071
  simp only [CollatzResearch.WordTrace]
  refine ⟨37606248847613334752437067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25070832565075556501624711 37606248847613334752437067)
  ·
    refine ⟨56409373271420002128655601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37606248847613334752437067 56409373271420002128655601)
    ·
      refine ⟨42307029953565001596491701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56409373271420002128655601 42307029953565001596491701)
      ·
        refine ⟨3966284058146718899671097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42307029953565001596491701 3966284058146718899671097)
        ·
          refine ⟨2974713043610039174753323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966284058146718899671097 2974713043610039174753323)
          ·
            refine ⟨4462069565415058762129985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974713043610039174753323 4462069565415058762129985)
            ·
              refine ⟨3346552174061294071597489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4462069565415058762129985 3346552174061294071597489)
              ·
                refine ⟨2509914130545970553698117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346552174061294071597489 2509914130545970553698117)
                ·
                  refine ⟨470608899477369478818397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509914130545970553698117 470608899477369478818397)
                  ·
                    rfl

theorem cell20_1031071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_1031071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031071 prefixEnd_1031071 := by exact prefixLift 1031071
  have htrace : WordTrace (prefixWord ++ tailWord_1031071) baseStart_1031071 baseEnd_1031071 := by
    simpa [prefixWord, tailWord_1031071, baseEnd_1031071] using wordTrace_append hprefix tailTrace_1031071
  have hstable : (prefixWord ++ tailWord_1031071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031071).length < 2 ^ (prefixWord ++ tailWord_1031071).sum := by decide
  have hdescent : baseEnd_1031071 < baseStart_1031071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031074 : List Nat := [3, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1031074 : Nat := 118140960795 + 1031074 * 2 ^ 59
def prefixEnd_1031074 : Nat := 4983230072969 + 3 ^ 40 * 1031074 * 2
def baseEnd_1031074 : Nat := 156870089586371600572795

theorem tailTrace_1031074 : CollatzResearch.WordTrace tailWord_1031074 prefixEnd_1031074 156870089586371600572795 := by
  unfold tailWord_1031074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401589566650616566199069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25070905511068310843197517 9401589566650616566199069)
  ·
    refine ⟨3525596087493981212324651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9401589566650616566199069 3525596087493981212324651)
    ·
      refine ⟨5288394131240971818486977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525596087493981212324651 5288394131240971818486977)
      ·
        refine ⟨3966295598430728863865233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5288394131240971818486977 3966295598430728863865233)
        ·
          refine ⟨2974721698823046647898925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3966295598430728863865233 2974721698823046647898925)
          ·
            refine ⟨1115520637058642492962097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2974721698823046647898925 1115520637058642492962097)
            ·
              refine ⟨836640477793981869721573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115520637058642492962097 836640477793981869721573)
              ·
                refine ⟨156870089586371600572795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836640477793981869721573 156870089586371600572795)
                ·
                  rfl

theorem cell20_1031074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1031074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031074 prefixEnd_1031074 := by exact prefixLift 1031074
  have htrace : WordTrace (prefixWord ++ tailWord_1031074) baseStart_1031074 baseEnd_1031074 := by
    simpa [prefixWord, tailWord_1031074, baseEnd_1031074] using wordTrace_append hprefix tailTrace_1031074
  have hstable : (prefixWord ++ tailWord_1031074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031074).length < 2 ^ (prefixWord ++ tailWord_1031074).sum := by decide
  have hdescent : baseEnd_1031074 < baseStart_1031074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031102 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1031102 : Nat := 118140960795 + 1031102 * 2 ^ 59
def prefixEnd_1031102 : Nat := 4983230072969 + 3 ^ 40 * 1031102 * 2
def baseEnd_1031102 : Nat := 470623048722071148784937

theorem tailTrace_1031102 : CollatzResearch.WordTrace tailWord_1031102 prefixEnd_1031102 470623048722071148784937 := by
  unfold tailWord_1031102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700922438812628380851945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25071586340334018031210373 4700922438812628380851945)
  ·
    refine ⟨3525691829109471285638959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4700922438812628380851945 3525691829109471285638959)
    ·
      refine ⟨5288537743664206928458439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525691829109471285638959 5288537743664206928458439)
      ·
        refine ⟨7932806615496310392687659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5288537743664206928458439 7932806615496310392687659)
        ·
          refine ⟨11899209923244465589031489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7932806615496310392687659 11899209923244465589031489)
          ·
            refine ⟨8924407442433349191773617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11899209923244465589031489 8924407442433349191773617)
            ·
              refine ⟨6693305581825011893830213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8924407442433349191773617 6693305581825011893830213)
              ·
                refine ⟨1254994796592189730093165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6693305581825011893830213 1254994796592189730093165)
                ·
                  refine ⟨470623048722071148784937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254994796592189730093165 470623048722071148784937)
                  ·
                    rfl

theorem cell20_1031102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1031102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031102 prefixEnd_1031102 := by exact prefixLift 1031102
  have htrace : WordTrace (prefixWord ++ tailWord_1031102) baseStart_1031102 baseEnd_1031102 := by
    simpa [prefixWord, tailWord_1031102, baseEnd_1031102] using wordTrace_append hprefix tailTrace_1031102
  have hstable : (prefixWord ++ tailWord_1031102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031102).length < 2 ^ (prefixWord ++ tailWord_1031102).sum := by decide
  have hdescent : baseEnd_1031102 < baseStart_1031102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031116 : List Nat := [2, 2, 1, 4, 1, 1, 4, 5]
def baseStart_1031116 : Nat := 118140960795 + 1031116 * 2 ^ 59
def prefixEnd_1031116 : Nat := 4983230072969 + 3 ^ 40 * 1031116 * 2
def baseEnd_1031116 : Nat := 156876479567849774106071

theorem tailTrace_1031116 : CollatzResearch.WordTrace tailWord_1031116 prefixEnd_1031116 156876479567849774106071 := by
  unfold tailWord_1031116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18803945066225153718912601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25071926754966871625216801 18803945066225153718912601)
  ·
    refine ⟨14102958799668865289184451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18803945066225153718912601 14102958799668865289184451)
    ·
      refine ⟨21154438199503297933776677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14102958799668865289184451 21154438199503297933776677)
      ·
        refine ⟨3966457162406868362583127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21154438199503297933776677 3966457162406868362583127)
        ·
          refine ⟨5949685743610302543874691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966457162406868362583127 5949685743610302543874691)
          ·
            refine ⟨8924528615415453815812037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949685743610302543874691 8924528615415453815812037)
            ·
              refine ⟨1673349115390397590464757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8924528615415453815812037 1673349115390397590464757)
              ·
                refine ⟨156876479567849774106071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673349115390397590464757 156876479567849774106071)
                ·
                  rfl

theorem cell20_1031116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_1031116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031116 prefixEnd_1031116 := by exact prefixLift 1031116
  have htrace : WordTrace (prefixWord ++ tailWord_1031116) baseStart_1031116 baseEnd_1031116 := by
    simpa [prefixWord, tailWord_1031116, baseEnd_1031116] using wordTrace_append hprefix tailTrace_1031116
  have hstable : (prefixWord ++ tailWord_1031116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031116).length < 2 ^ (prefixWord ++ tailWord_1031116).sum := by decide
  have hdescent : baseEnd_1031116 < baseStart_1031116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031119 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 3]
def baseStart_1031119 : Nat := 118140960795 + 1031119 * 2 ^ 59
def prefixEnd_1031119 : Nat := 4983230072969 + 3 ^ 40 * 1031119 * 2
def baseEnd_1031119 : Nat := 470630807985294645218201

theorem tailTrace_1031119 : CollatzResearch.WordTrace tailWord_1031119 prefixEnd_1031119 470630807985294645218201 := by
  unfold tailWord_1031119
  simp only [CollatzResearch.WordTrace]
  refine ⟨37607999551439438950184411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25071999700959625966789607 37607999551439438950184411)
  ·
    refine ⟨56411999327159158425276617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37607999551439438950184411 56411999327159158425276617)
    ·
      refine ⟨42308999495369368818957463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56411999327159158425276617 42308999495369368818957463)
      ·
        refine ⟨63463499243054053228436195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42308999495369368818957463 63463499243054053228436195)
        ·
          refine ⟨95195248864581079842654293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63463499243054053228436195 95195248864581079842654293)
          ·
            refine ⟨1115569322631809529406105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 95195248864581079842654293 1115569322631809529406105)
            ·
              refine ⟨836676991973857147054579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115569322631809529406105 836676991973857147054579)
              ·
                refine ⟨1255015487960785720581869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836676991973857147054579 1255015487960785720581869)
                ·
                  refine ⟨470630807985294645218201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255015487960785720581869 470630807985294645218201)
                  ·
                    rfl

theorem cell20_1031119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_1031119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031119 prefixEnd_1031119 := by exact prefixLift 1031119
  have htrace : WordTrace (prefixWord ++ tailWord_1031119) baseStart_1031119 baseEnd_1031119 := by
    simpa [prefixWord, tailWord_1031119, baseEnd_1031119] using wordTrace_append hprefix tailTrace_1031119
  have hstable : (prefixWord ++ tailWord_1031119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031119).length < 2 ^ (prefixWord ++ tailWord_1031119).sum := by decide
  have hdescent : baseEnd_1031119 < baseStart_1031119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031154 : List Nat := [3, 2, 1, 5, 9]
def baseStart_1031154 : Nat := 118140960795 + 1031154 * 2 ^ 59
def prefixEnd_1031154 : Nat := 4983230072969 + 3 ^ 40 * 1031154 * 2
def baseEnd_1031154 : Nat := 5810454110357902210511

theorem tailTrace_1031154 : CollatzResearch.WordTrace tailWord_1031154 prefixEnd_1031154 5810454110357902210511 := by
  unfold tailWord_1031154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402319026578159981927129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25072850737541759951805677 9402319026578159981927129)
  ·
    refine ⟨7051739269933619986445347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9402319026578159981927129 7051739269933619986445347)
    ·
      refine ⟨10577608904900429979668021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7051739269933619986445347 10577608904900429979668021)
      ·
        refine ⟨991650834834415310593877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10577608904900429979668021 991650834834415310593877)
        ·
          refine ⟨5810454110357902210511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 991650834834415310593877 5810454110357902210511)
          ·
            rfl

theorem cell20_1031154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 9].length) (baseStart_1031154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031154 prefixEnd_1031154 := by exact prefixLift 1031154
  have htrace : WordTrace (prefixWord ++ tailWord_1031154) baseStart_1031154 baseEnd_1031154 := by
    simpa [prefixWord, tailWord_1031154, baseEnd_1031154] using wordTrace_append hprefix tailTrace_1031154
  have hstable : (prefixWord ++ tailWord_1031154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031154).length < 2 ^ (prefixWord ++ tailWord_1031154).sum := by decide
  have hdescent : baseEnd_1031154 < baseStart_1031154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031156 : List Nat := [2, 6, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1031156 : Nat := 118140960795 + 1031156 * 2 ^ 59
def prefixEnd_1031156 : Nat := 4983230072969 + 3 ^ 40 * 1031156 * 2
def baseEnd_1031156 : Nat := 470647695793486960984717

theorem tailTrace_1031156 : CollatzResearch.WordTrace tailWord_1031156 prefixEnd_1031156 470647695793486960984717 := by
  unfold tailWord_1031156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18804674526152697134640661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25072899368203596179520881 18804674526152697134640661)
  ·
    refine ⟨881469118413407678186281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18804674526152697134640661 881469118413407678186281)
    ·
      refine ⟨661101838810055758639711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 881469118413407678186281 661101838810055758639711)
      ·
        refine ⟨991652758215083637959567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661101838810055758639711 991652758215083637959567)
        ·
          refine ⟨1487479137322625456939351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991652758215083637959567 1487479137322625456939351)
          ·
            refine ⟨2231218705983938185409027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487479137322625456939351 2231218705983938185409027)
            ·
              refine ⟨3346828058975907278113541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231218705983938185409027 3346828058975907278113541)
              ·
                refine ⟨627530261057982614646289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3346828058975907278113541 627530261057982614646289)
                ·
                  refine ⟨470647695793486960984717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627530261057982614646289 470647695793486960984717)
                  ·
                    rfl

theorem cell20_1031156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1031156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031156 prefixEnd_1031156 := by exact prefixLift 1031156
  have htrace : WordTrace (prefixWord ++ tailWord_1031156) baseStart_1031156 baseEnd_1031156 := by
    simpa [prefixWord, tailWord_1031156, baseEnd_1031156] using wordTrace_append hprefix tailTrace_1031156
  have hstable : (prefixWord ++ tailWord_1031156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031156).length < 2 ^ (prefixWord ++ tailWord_1031156).sum := by decide
  have hdescent : baseEnd_1031156 < baseStart_1031156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031164 : List Nat := [2, 2, 2, 1, 2, 4, 1, 4, 2]
def baseStart_1031164 : Nat := 118140960795 + 1031164 * 2 ^ 59
def prefixEnd_1031164 : Nat := 4983230072969 + 3 ^ 40 * 1031164 * 2
def baseEnd_1031164 : Nat := 470651347211474488718017

theorem tailTrace_1031164 : CollatzResearch.WordTrace tailWord_1031164 prefixEnd_1031164 470651347211474488718017 := by
  unfold tailWord_1031164
  simp only [CollatzResearch.WordTrace]
  refine ⟨18804820418138205817786273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25073093890850941090381697 18804820418138205817786273)
  ·
    refine ⟨14103615313603654363339705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18804820418138205817786273 14103615313603654363339705)
    ·
      refine ⟨10577711485202740772504779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14103615313603654363339705 10577711485202740772504779)
      ·
        refine ⟨15866567227804111158757169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10577711485202740772504779 15866567227804111158757169)
        ·
          refine ⟨11899925420853083369067877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15866567227804111158757169 11899925420853083369067877)
          ·
            refine ⟨2231236016409953131700227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11899925420853083369067877 2231236016409953131700227)
            ·
              refine ⟨3346854024614929697550341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231236016409953131700227 3346854024614929697550341)
              ·
                refine ⟨627535129615299318290689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3346854024614929697550341 627535129615299318290689)
                ·
                  refine ⟨470651347211474488718017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627535129615299318290689 470651347211474488718017)
                  ·
                    rfl

theorem cell20_1031164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_1031164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031164 prefixEnd_1031164 := by exact prefixLift 1031164
  have htrace : WordTrace (prefixWord ++ tailWord_1031164) baseStart_1031164 baseEnd_1031164 := by
    simpa [prefixWord, tailWord_1031164, baseEnd_1031164] using wordTrace_append hprefix tailTrace_1031164
  have hstable : (prefixWord ++ tailWord_1031164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031164).length < 2 ^ (prefixWord ++ tailWord_1031164).sum := by decide
  have hdescent : baseEnd_1031164 < baseStart_1031164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031178 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_1031178 : Nat := 118140960795 + 1031178 * 2 ^ 59
def prefixEnd_1031178 : Nat := 4983230072969 + 3 ^ 40 * 1031178 * 2
def baseEnd_1031178 : Nat := 470657737192952662251293

theorem tailTrace_1031178 : CollatzResearch.WordTrace tailWord_1031178 prefixEnd_1031178 470657737192952662251293 := by
  unfold tailWord_1031178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402537864556423006645547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25073434305483794684388125 9402537864556423006645547)
  ·
    refine ⟨14103806796834634509968321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9402537864556423006645547 14103806796834634509968321)
    ·
      refine ⟨10577855097625975882476241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14103806796834634509968321 10577855097625975882476241)
      ·
        refine ⟨7933391323219481911857181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10577855097625975882476241 7933391323219481911857181)
        ·
          refine ⟨2975021746207305716946443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7933391323219481911857181 2975021746207305716946443)
          ·
            refine ⟨4462532619310958575419665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975021746207305716946443 4462532619310958575419665)
            ·
              refine ⟨3346899464483218931564749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4462532619310958575419665 3346899464483218931564749)
              ·
                refine ⟨1255087299181207099336781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3346899464483218931564749 1255087299181207099336781)
                ·
                  refine ⟨470657737192952662251293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255087299181207099336781 470657737192952662251293)
                  ·
                    rfl

theorem cell20_1031178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_1031178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031178 prefixEnd_1031178 := by exact prefixLift 1031178
  have htrace : WordTrace (prefixWord ++ tailWord_1031178) baseStart_1031178 baseEnd_1031178 := by
    simpa [prefixWord, tailWord_1031178, baseEnd_1031178] using wordTrace_append hprefix tailTrace_1031178
  have hstable : (prefixWord ++ tailWord_1031178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031178).length < 2 ^ (prefixWord ++ tailWord_1031178).sum := by decide
  have hdescent : baseEnd_1031178 < baseStart_1031178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031202 : List Nat := [3, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1031202 : Nat := 118140960795 + 1031202 * 2 ^ 59
def prefixEnd_1031202 : Nat := 4983230072969 + 3 ^ 40 * 1031202 * 2
def baseEnd_1031202 : Nat := 470668691446915245451195

theorem tailTrace_1031202 : CollatzResearch.WordTrace tailWord_1031202 prefixEnd_1031202 470668691446915245451195 := by
  unfold tailWord_1031202
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402756702534686031363965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25074017873425829416970573 9402756702534686031363965)
  ·
    refine ⟨3526033763450507261761487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9402756702534686031363965 3526033763450507261761487)
    ·
      refine ⟨5289050645175760892642231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3526033763450507261761487 5289050645175760892642231)
      ·
        refine ⟨7933575967763641338963347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5289050645175760892642231 7933575967763641338963347)
        ·
          refine ⟨11900363951645462008445021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7933575967763641338963347 11900363951645462008445021)
          ·
            refine ⟨4462636481867048253166883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11900363951645462008445021 4462636481867048253166883)
            ·
              refine ⟨6693954722800572379750325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462636481867048253166883 6693954722800572379750325)
              ·
                refine ⟨627558255262553660601593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6693954722800572379750325 627558255262553660601593)
                ·
                  refine ⟨470668691446915245451195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627558255262553660601593 470668691446915245451195)
                  ·
                    rfl

theorem cell20_1031202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1031202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031202 prefixEnd_1031202 := by exact prefixLift 1031202
  have htrace : WordTrace (prefixWord ++ tailWord_1031202) baseStart_1031202 baseEnd_1031202 := by
    simpa [prefixWord, tailWord_1031202, baseEnd_1031202] using wordTrace_append hprefix tailTrace_1031202
  have hstable : (prefixWord ++ tailWord_1031202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031202).length < 2 ^ (prefixWord ++ tailWord_1031202).sum := by decide
  have hdescent : baseEnd_1031202 < baseStart_1031202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031237 : List Nat := [1, 3, 1, 1, 1, 3, 2, 5, 3]
def baseStart_1031237 : Nat := 118140960795 + 1031237 * 2 ^ 59
def prefixEnd_1031237 : Nat := 4983230072969 + 3 ^ 40 * 1031237 * 2
def baseEnd_1031237 : Nat := 470684666400610679284385

theorem tailTrace_1031237 : CollatzResearch.WordTrace tailWord_1031237 prefixEnd_1031237 470684666400610679284385 := by
  unfold tailWord_1031237
  simp only [CollatzResearch.WordTrace]
  refine ⟨37612303365011945102979965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25074868910007963401986643 37612303365011945102979965)
  ·
    refine ⟨14104613761879479413617487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37612303365011945102979965 14104613761879479413617487)
    ·
      refine ⟨21156920642819219120426231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14104613761879479413617487 21156920642819219120426231)
      ·
        refine ⟨31735380964228828680639347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21156920642819219120426231 31735380964228828680639347)
        ·
          refine ⟨47603071446343243020959021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31735380964228828680639347 47603071446343243020959021)
          ·
            refine ⟨17851151792378716132859633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47603071446343243020959021 17851151792378716132859633)
            ·
              refine ⟨13388363844284037099644725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17851151792378716132859633 13388363844284037099644725)
              ·
                refine ⟨1255159110401628478091693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13388363844284037099644725 1255159110401628478091693)
                ·
                  refine ⟨470684666400610679284385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255159110401628478091693 470684666400610679284385)
                  ·
                    rfl

theorem cell20_1031237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_1031237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031237 prefixEnd_1031237 := by exact prefixLift 1031237
  have htrace : WordTrace (prefixWord ++ tailWord_1031237) baseStart_1031237 baseEnd_1031237 := by
    simpa [prefixWord, tailWord_1031237, baseEnd_1031237] using wordTrace_append hprefix tailTrace_1031237
  have hstable : (prefixWord ++ tailWord_1031237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031237).length < 2 ^ (prefixWord ++ tailWord_1031237).sum := by decide
  have hdescent : baseEnd_1031237 < baseStart_1031237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031278 : List Nat := [4, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_1031278 : Nat := 118140960795 + 1031278 * 2 ^ 59
def prefixEnd_1031278 : Nat := 4983230072969 + 3 ^ 40 * 1031278 * 2
def baseEnd_1031278 : Nat := 470703379917796758917551

theorem tailTrace_1031278 : CollatzResearch.WordTrace tailWord_1031278 prefixEnd_1031278 470703379917796758917551 := by
  unfold tailWord_1031278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701724844732926138152811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25075865838575606070148325 4701724844732926138152811)
  ·
    refine ⟨7052587267099389207229217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4701724844732926138152811 7052587267099389207229217)
    ·
      refine ⟨5289440450324541905421913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7052587267099389207229217 5289440450324541905421913)
      ·
        refine ⟨3967080337743406429066435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5289440450324541905421913 3967080337743406429066435)
        ·
          refine ⟨5950620506615109643599653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967080337743406429066435 5950620506615109643599653)
          ·
            refine ⟨1115741344990333058174935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5950620506615109643599653 1115741344990333058174935)
            ·
              refine ⟨1673612017485499587262403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115741344990333058174935 1673612017485499587262403)
              ·
                refine ⟨2510418026228249380893605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673612017485499587262403 2510418026228249380893605)
                ·
                  refine ⟨470703379917796758917551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510418026228249380893605 470703379917796758917551)
                  ·
                    rfl

theorem cell20_1031278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_1031278 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031278 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031278 prefixEnd_1031278 := by exact prefixLift 1031278
  have htrace : WordTrace (prefixWord ++ tailWord_1031278) baseStart_1031278 baseEnd_1031278 := by
    simpa [prefixWord, tailWord_1031278, baseEnd_1031278] using wordTrace_append hprefix tailTrace_1031278
  have hstable : (prefixWord ++ tailWord_1031278).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031278).length < 2 ^ (prefixWord ++ tailWord_1031278).sum := by decide
  have hdescent : baseEnd_1031278 < baseStart_1031278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031327 : List Nat := [1, 1, 2, 6, 10]
def baseStart_1031327 : Nat := 118140960795 + 1031327 * 2 ^ 59
def prefixEnd_1031327 : Nat := 4983230072969 + 3 ^ 40 * 1031327 * 2
def baseEnd_1031327 : Nat := 5811428948802103287457

theorem tailTrace_1031327 : CollatzResearch.WordTrace tailWord_1031327 prefixEnd_1031327 5811428948802103287457 := by
  unfold tailWord_1031327
  simp only [CollatzResearch.WordTrace]
  refine ⟨37615585934685890473756235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25077057289790593649170823 37615585934685890473756235)
  ·
    refine ⟨56423378902028835710634353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37615585934685890473756235 56423378902028835710634353)
    ·
      refine ⟨42317534176521626782975765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56423378902028835710634353 42317534176521626782975765)
      ·
        refine ⟨1983634414524451255451989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42317534176521626782975765 1983634414524451255451989)
        ·
          refine ⟨5811428948802103287457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1983634414524451255451989 5811428948802103287457)
          ·
            rfl

theorem cell20_1031327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 10].length) (baseStart_1031327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031327 prefixEnd_1031327 := by exact prefixLift 1031327
  have htrace : WordTrace (prefixWord ++ tailWord_1031327) baseStart_1031327 baseEnd_1031327 := by
    simpa [prefixWord, tailWord_1031327, baseEnd_1031327] using wordTrace_append hprefix tailTrace_1031327
  have hstable : (prefixWord ++ tailWord_1031327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031327).length < 2 ^ (prefixWord ++ tailWord_1031327).sum := by decide
  have hdescent : baseEnd_1031327 < baseStart_1031327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031333 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 2]
def baseStart_1031333 : Nat := 118140960795 + 1031333 * 2 ^ 59
def prefixEnd_1031333 : Nat := 4983230072969 + 3 ^ 40 * 1031333 * 2
def baseEnd_1031333 : Nat := 470728483416461012083993

theorem tailTrace_1031333 : CollatzResearch.WordTrace tailWord_1031333 prefixEnd_1031333 470728483416461012083993 := by
  unfold tailWord_1031333
  simp only [CollatzResearch.WordTrace]
  refine ⟨37615804772664153498474653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25077203181776102332316435 37615804772664153498474653)
  ·
    refine ⟨14105926789749057561927995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37615804772664153498474653 14105926789749057561927995)
    ·
      refine ⟨21158890184623586342891993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14105926789749057561927995 21158890184623586342891993)
      ·
        refine ⟨15869167638467689757168995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21158890184623586342891993 15869167638467689757168995)
        ·
          refine ⟨23803751457701534635753493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15869167638467689757168995 23803751457701534635753493)
          ·
            refine ⟨1115800849579759436050945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23803751457701534635753493 1115800849579759436050945)
            ·
              refine ⟨836850637184819577038209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115800849579759436050945 836850637184819577038209)
              ·
                refine ⟨627637977888614682778657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 836850637184819577038209 627637977888614682778657)
                ·
                  refine ⟨470728483416461012083993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627637977888614682778657 470728483416461012083993)
                  ·
                    rfl

theorem cell20_1031333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 2].length) (baseStart_1031333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031333 prefixEnd_1031333 := by exact prefixLift 1031333
  have htrace : WordTrace (prefixWord ++ tailWord_1031333) baseStart_1031333 baseEnd_1031333 := by
    simpa [prefixWord, tailWord_1031333, baseEnd_1031333] using wordTrace_append hprefix tailTrace_1031333
  have hstable : (prefixWord ++ tailWord_1031333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031333).length < 2 ^ (prefixWord ++ tailWord_1031333).sum := by decide
  have hdescent : baseEnd_1031333 < baseStart_1031333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031351 : List Nat := [1, 1, 3, 1, 4, 1, 1, 5, 3]
def baseStart_1031351 : Nat := 118140960795 + 1031351 * 2 ^ 59
def prefixEnd_1031351 : Nat := 4983230072969 + 3 ^ 40 * 1031351 * 2
def baseEnd_1031351 : Nat := 470736699106932949483919

theorem tailTrace_1031351 : CollatzResearch.WordTrace tailWord_1031351 prefixEnd_1031351 470736699106932949483919 := by
  unfold tailWord_1031351
  simp only [CollatzResearch.WordTrace]
  refine ⟨37616461286598942572629907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25077640857732628381753271 37616461286598942572629907)
  ·
    refine ⟨56424691929898413858944861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37616461286598942572629907 56424691929898413858944861)
    ·
      refine ⟨21159259473711905197104323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56424691929898413858944861 21159259473711905197104323)
      ·
        refine ⟨31738889210567857795656485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21159259473711905197104323 31738889210567857795656485)
        ·
          refine ⟨5951041726981473336685591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31738889210567857795656485 5951041726981473336685591)
          ·
            refine ⟨8926562590472210005028387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5951041726981473336685591 8926562590472210005028387)
            ·
              refine ⟨13389843885708315007542581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8926562590472210005028387 13389843885708315007542581)
              ·
                refine ⟨1255297864285154531957117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13389843885708315007542581 1255297864285154531957117)
                ·
                  refine ⟨470736699106932949483919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255297864285154531957117 470736699106932949483919)
                  ·
                    rfl

theorem cell20_1031351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 5, 3].length) (baseStart_1031351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031351 prefixEnd_1031351 := by exact prefixLift 1031351
  have htrace : WordTrace (prefixWord ++ tailWord_1031351) baseStart_1031351 baseEnd_1031351 := by
    simpa [prefixWord, tailWord_1031351, baseEnd_1031351] using wordTrace_append hprefix tailTrace_1031351
  have hstable : (prefixWord ++ tailWord_1031351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031351).length < 2 ^ (prefixWord ++ tailWord_1031351).sum := by decide
  have hdescent : baseEnd_1031351 < baseStart_1031351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031396 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 4]
def baseStart_1031396 : Nat := 118140960795 + 1031396 * 2 ^ 59
def prefixEnd_1031396 : Nat := 4983230072969 + 3 ^ 40 * 1031396 * 2
def baseEnd_1031396 : Nat := 470757238333112792983735

theorem tailTrace_1031396 : CollatzResearch.WordTrace tailWord_1031396 prefixEnd_1031396 470757238333112792983735 := by
  unfold tailWord_1031396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809051285717957629009021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25078735047623943505345361 18809051285717957629009021)
  ·
    refine ⟨7053394232144234110878383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18809051285717957629009021 7053394232144234110878383)
    ·
      refine ⟨10580091348216351166317575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7053394232144234110878383 10580091348216351166317575)
      ·
        refine ⟨15870137022324526749476363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10580091348216351166317575 15870137022324526749476363)
        ·
          refine ⟨23805205533486790124214545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15870137022324526749476363 23805205533486790124214545)
          ·
            refine ⟨17853904150115092593160909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23805205533486790124214545 17853904150115092593160909)
            ·
              refine ⟨6695214056293159722435341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17853904150115092593160909 6695214056293159722435341)
              ·
                refine ⟨2510705271109934895913253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6695214056293159722435341 2510705271109934895913253)
                ·
                  refine ⟨470757238333112792983735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510705271109934895913253 470757238333112792983735)
                  ·
                    rfl

theorem cell20_1031396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_1031396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031396 prefixEnd_1031396 := by exact prefixLift 1031396
  have htrace : WordTrace (prefixWord ++ tailWord_1031396) baseStart_1031396 baseEnd_1031396 := by
    simpa [prefixWord, tailWord_1031396, baseEnd_1031396] using wordTrace_append hprefix tailTrace_1031396
  have hstable : (prefixWord ++ tailWord_1031396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031396).length < 2 ^ (prefixWord ++ tailWord_1031396).sum := by decide
  have hdescent : baseEnd_1031396 < baseStart_1031396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031412 : List Nat := [2, 6, 1, 2, 1, 2, 2, 4]
def baseStart_1031412 : Nat := 118140960795 + 1031412 * 2 ^ 59
def prefixEnd_1031412 : Nat := 4983230072969 + 3 ^ 40 * 1031412 * 2
def baseEnd_1031412 : Nat := 156921513723029282816779

theorem tailTrace_1031412 : CollatzResearch.WordTrace tailWord_1031412 prefixEnd_1031412 156921513723029282816779 := by
  unfold tailWord_1031412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809343069688974995300245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25079124092918633327066993 18809343069688974995300245)
  ·
    refine ⟨881687956391670702904699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18809343069688974995300245 881687956391670702904699)
    ·
      refine ⟨1322531934587506054357049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 881687956391670702904699 1322531934587506054357049)
      ·
        refine ⟨991898950940629540767787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1322531934587506054357049 991898950940629540767787)
        ·
          refine ⟨1487848426410944311151681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991898950940629540767787 1487848426410944311151681)
          ·
            refine ⟨1115886319808208233363761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487848426410944311151681 1115886319808208233363761)
            ·
              refine ⟨836914739856156175022821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115886319808208233363761 836914739856156175022821)
              ·
                refine ⟨156921513723029282816779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 836914739856156175022821 156921513723029282816779)
                ·
                  rfl

theorem cell20_1031412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_1031412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031412 prefixEnd_1031412 := by exact prefixLift 1031412
  have htrace : WordTrace (prefixWord ++ tailWord_1031412) baseStart_1031412 baseEnd_1031412 := by
    simpa [prefixWord, tailWord_1031412, baseEnd_1031412] using wordTrace_append hprefix tailTrace_1031412
  have hstable : (prefixWord ++ tailWord_1031412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031412).length < 2 ^ (prefixWord ++ tailWord_1031412).sum := by decide
  have hdescent : baseEnd_1031412 < baseStart_1031412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031420 : List Nat := [2, 2, 2, 1, 5, 1, 1, 6]
def baseStart_1031420 : Nat := 118140960795 + 1031420 * 2 ^ 59
def prefixEnd_1031420 : Nat := 4983230072969 + 3 ^ 40 * 1031420 * 2
def baseEnd_1031420 : Nat := 156922730862358458727879

theorem tailTrace_1031420 : CollatzResearch.WordTrace tailWord_1031420 prefixEnd_1031420 156922730862358458727879 := by
  unfold tailWord_1031420
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809488961674483678445857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25079318615565978237927809 18809488961674483678445857)
  ·
    refine ⟨14107116721255862758834393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18809488961674483678445857 14107116721255862758834393)
    ·
      refine ⟨10580337540941897069125795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14107116721255862758834393 10580337540941897069125795)
      ·
        refine ⟨15870506311412845603688693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10580337540941897069125795 15870506311412845603688693)
        ·
          refine ⟨1487859966694954275345815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15870506311412845603688693 1487859966694954275345815)
          ·
            refine ⟨2231789950042431413018723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487859966694954275345815 2231789950042431413018723)
            ·
              refine ⟨3347684925063647119528085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231789950042431413018723 3347684925063647119528085)
              ·
                refine ⟨156922730862358458727879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3347684925063647119528085 156922730862358458727879)
                ·
                  rfl

theorem cell20_1031420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_1031420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031420 prefixEnd_1031420 := by exact prefixLift 1031420
  have htrace : WordTrace (prefixWord ++ tailWord_1031420) baseStart_1031420 baseEnd_1031420 := by
    simpa [prefixWord, tailWord_1031420, baseEnd_1031420] using wordTrace_append hprefix tailTrace_1031420
  have hstable : (prefixWord ++ tailWord_1031420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031420).length < 2 ^ (prefixWord ++ tailWord_1031420).sum := by decide
  have hdescent : baseEnd_1031420 < baseStart_1031420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031426 : List Nat := [3, 4, 1, 1, 3, 2, 1, 3, 2]
def baseStart_1031426 : Nat := 118140960795 + 1031426 * 2 ^ 59
def prefixEnd_1031426 : Nat := 4983230072969 + 3 ^ 40 * 1031426 * 2
def baseEnd_1031426 : Nat := 470770931150566021983613

theorem tailTrace_1031426 : CollatzResearch.WordTrace tailWord_1031426 prefixEnd_1031426 470770931150566021983613 := by
  unfold tailWord_1031426
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404799190331807595402533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25079464507551486921073421 9404799190331807595402533)
  ·
    refine ⟨1763399848187213924137975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9404799190331807595402533 1763399848187213924137975)
    ·
      refine ⟨2645099772280820886206963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763399848187213924137975 2645099772280820886206963)
      ·
        refine ⟨3967649658421231329310445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645099772280820886206963 3967649658421231329310445)
        ·
          refine ⟨1487868621907961748491417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3967649658421231329310445 1487868621907961748491417)
          ·
            refine ⟨1115901466430971311368563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1487868621907961748491417 1115901466430971311368563)
            ·
              refine ⟨1673852199646456967052845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115901466430971311368563 1673852199646456967052845)
              ·
                refine ⟨627694574867421362644817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1673852199646456967052845 627694574867421362644817)
                ·
                  refine ⟨470770931150566021983613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627694574867421362644817 470770931150566021983613)
                  ·
                    rfl

theorem cell20_1031426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_1031426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031426 prefixEnd_1031426 := by exact prefixLift 1031426
  have htrace : WordTrace (prefixWord ++ tailWord_1031426) baseStart_1031426 baseEnd_1031426 := by
    simpa [prefixWord, tailWord_1031426, baseEnd_1031426] using wordTrace_append hprefix tailTrace_1031426
  have hstable : (prefixWord ++ tailWord_1031426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031426).length < 2 ^ (prefixWord ++ tailWord_1031426).sum := by decide
  have hdescent : baseEnd_1031426 < baseStart_1031426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031454 : List Nat := [4, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1031454 : Nat := 118140960795 + 1031454 * 2 ^ 59
def prefixEnd_1031454 : Nat := 4983230072969 + 3 ^ 40 * 1031454 * 2
def baseEnd_1031454 : Nat := 156927903704507456350055

theorem tailTrace_1031454 : CollatzResearch.WordTrace tailWord_1031454 prefixEnd_1031454 156927903704507456350055 := by
  unfold tailWord_1031454
  simp only [CollatzResearch.WordTrace]
  refine ⟨4702527250653223895453677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25080145336817194109086277 4702527250653223895453677)
  ·
    refine ⟨1763447718994958960795129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4702527250653223895453677 1763447718994958960795129)
    ·
      refine ⟨1322585789246219220596347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763447718994958960795129 1322585789246219220596347)
      ·
        refine ⟨1983878683869328830894521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322585789246219220596347 1983878683869328830894521)
        ·
          refine ⟨1487909012901996623170891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983878683869328830894521 1487909012901996623170891)
          ·
            refine ⟨2231863519352994934756337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487909012901996623170891 2231863519352994934756337)
            ·
              refine ⟨1673897639514746201067253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231863519352994934756337 1673897639514746201067253)
              ·
                refine ⟨156927903704507456350055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673897639514746201067253 156927903704507456350055)
                ·
                  rfl

theorem cell20_1031454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1031454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031454 prefixEnd_1031454 := by exact prefixLift 1031454
  have htrace : WordTrace (prefixWord ++ tailWord_1031454) baseStart_1031454 baseEnd_1031454 := by
    simpa [prefixWord, tailWord_1031454, baseEnd_1031454] using wordTrace_append hprefix tailTrace_1031454
  have hstable : (prefixWord ++ tailWord_1031454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031454).length < 2 ^ (prefixWord ++ tailWord_1031454).sum := by decide
  have hdescent : baseEnd_1031454 < baseStart_1031454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031461 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 3]
def baseStart_1031461 : Nat := 118140960795 + 1031461 * 2 ^ 59
def prefixEnd_1031461 : Nat := 4983230072969 + 3 ^ 40 * 1031461 * 2
def baseEnd_1031461 : Nat := 470786906104261455816803

theorem tailTrace_1031461 : CollatzResearch.WordTrace tailWord_1031461 prefixEnd_1031461 470786906104261455816803 := by
  unfold tailWord_1031461
  simp only [CollatzResearch.WordTrace]
  refine ⟨37620473316200431359134237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25080315544133620906089491 37620473316200431359134237)
  ·
    refine ⟨14107677493575161759675339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37620473316200431359134237 14107677493575161759675339)
    ·
      refine ⟨21161516240362742639513009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14107677493575161759675339 21161516240362742639513009)
      ·
        refine ⟨15871137180272056979634757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21161516240362742639513009 15871137180272056979634757)
        ·
          refine ⟨2975838221301010683681517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15871137180272056979634757 2975838221301010683681517)
          ·
            refine ⟨1115939332987879006380569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2975838221301010683681517 1115939332987879006380569)
            ·
              refine ⟨836954499740909254785427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1115939332987879006380569 836954499740909254785427)
              ·
                refine ⟨1255431749611363882178141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 836954499740909254785427 1255431749611363882178141)
                ·
                  refine ⟨470786906104261455816803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255431749611363882178141 470786906104261455816803)
                  ·
                    rfl

theorem cell20_1031461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_1031461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031461 prefixEnd_1031461 := by exact prefixLift 1031461
  have htrace : WordTrace (prefixWord ++ tailWord_1031461) baseStart_1031461 baseEnd_1031461 := by
    simpa [prefixWord, tailWord_1031461, baseEnd_1031461] using wordTrace_append hprefix tailTrace_1031461
  have hstable : (prefixWord ++ tailWord_1031461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031461).length < 2 ^ (prefixWord ++ tailWord_1031461).sum := by decide
  have hdescent : baseEnd_1031461 < baseStart_1031461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031527 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 4]
def baseStart_1031527 : Nat := 118140960795 + 1031527 * 2 ^ 59
def prefixEnd_1031527 : Nat := 4983230072969 + 3 ^ 40 * 1031527 * 2
def baseEnd_1031527 : Nat := 470817030302658559616533

theorem tailTrace_1031527 : CollatzResearch.WordTrace tailWord_1031527 prefixEnd_1031527 470817030302658559616533 := by
  unfold tailWord_1031527
  simp only [CollatzResearch.WordTrace]
  refine ⟨37622880533961324631036835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25081920355974216420691223 37622880533961324631036835)
  ·
    refine ⟨56434320800941986946555253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37622880533961324631036835 56434320800941986946555253)
    ·
      refine ⟨5290717575088311276239555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56434320800941986946555253 5290717575088311276239555)
      ·
        refine ⟨7936076362632466914359333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290717575088311276239555 7936076362632466914359333)
        ·
          refine ⟨1488014317993587546442375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7936076362632466914359333 1488014317993587546442375)
          ·
            refine ⟨2232021476990381319663563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488014317993587546442375 2232021476990381319663563)
            ·
              refine ⟨3348032215485571979495345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232021476990381319663563 3348032215485571979495345)
              ·
                refine ⟨2511024161614178984621509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348032215485571979495345 2511024161614178984621509)
                ·
                  refine ⟨470817030302658559616533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511024161614178984621509 470817030302658559616533)
                  ·
                    rfl

theorem cell20_1031527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 4].length) (baseStart_1031527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031527 prefixEnd_1031527 := by exact prefixLift 1031527
  have htrace : WordTrace (prefixWord ++ tailWord_1031527) baseStart_1031527 baseEnd_1031527 := by
    simpa [prefixWord, tailWord_1031527, baseEnd_1031527] using wordTrace_append hprefix tailTrace_1031527
  have hstable : (prefixWord ++ tailWord_1031527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031527).length < 2 ^ (prefixWord ++ tailWord_1031527).sum := by decide
  have hdescent : baseEnd_1031527 < baseStart_1031527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031554 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_1031554 : Nat := 118140960795 + 1031554 * 2 ^ 59
def prefixEnd_1031554 : Nat := 4983230072969 + 3 ^ 40 * 1031554 * 2
def baseEnd_1031554 : Nat := 470829353838366465716423

theorem tailTrace_1031554 : CollatzResearch.WordTrace tailWord_1031554 prefixEnd_1031554 470829353838366465716423 := by
  unfold tailWord_1031554
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405966326215877060567429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25082576869909005494846477 9405966326215877060567429)
  ·
    refine ⟨1763618686165476948856393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9405966326215877060567429 1763618686165476948856393)
    ·
      refine ⟨1322714014624107711642295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763618686165476948856393 1322714014624107711642295)
      ·
        refine ⟨1984071021936161567463443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322714014624107711642295 1984071021936161567463443)
        ·
          refine ⟨2976106532904242351195165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984071021936161567463443 2976106532904242351195165)
          ·
            refine ⟨1116039949839090881698187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2976106532904242351195165 1116039949839090881698187)
            ·
              refine ⟨1674059924758636322547281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116039949839090881698187 1674059924758636322547281)
              ·
                refine ⟨1255544943568977241910461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674059924758636322547281 1255544943568977241910461)
                ·
                  refine ⟨470829353838366465716423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255544943568977241910461 470829353838366465716423)
                  ·
                    rfl

theorem cell20_1031554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_1031554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031554 prefixEnd_1031554 := by exact prefixLift 1031554
  have htrace : WordTrace (prefixWord ++ tailWord_1031554) baseStart_1031554 baseEnd_1031554 := by
    simpa [prefixWord, tailWord_1031554, baseEnd_1031554] using wordTrace_append hprefix tailTrace_1031554
  have hstable : (prefixWord ++ tailWord_1031554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031554).length < 2 ^ (prefixWord ++ tailWord_1031554).sum := by decide
  have hdescent : baseEnd_1031554 < baseStart_1031554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031555 : List Nat := [1, 1, 1, 3, 5, 2, 7]
def baseStart_1031555 : Nat := 118140960795 + 1031555 * 2 ^ 59
def prefixEnd_1031555 : Nat := 4983230072969 + 3 ^ 40 * 1031555 * 2
def baseEnd_1031555 : Nat := 52314423362846100742565

theorem tailTrace_1031555 : CollatzResearch.WordTrace tailWord_1031555 prefixEnd_1031555 52314423362846100742565 := by
  unfold tailWord_1031555
  simp only [CollatzResearch.WordTrace]
  refine ⟨37623901777859885413056119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25082601185239923608704079 37623901777859885413056119)
  ·
    refine ⟨56435852666789828119584179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37623901777859885413056119 56435852666789828119584179)
    ·
      refine ⟨84653779000184742179376269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56435852666789828119584179 84653779000184742179376269)
      ·
        refine ⟨31745167125069278317266101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84653779000184742179376269 31745167125069278317266101)
        ·
          refine ⟨2976109417975244842243697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31745167125069278317266101 2976109417975244842243697)
          ·
            refine ⟨2232082063481433631682773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2976109417975244842243697 2232082063481433631682773)
            ·
              refine ⟨52314423362846100742565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2232082063481433631682773 52314423362846100742565)
              ·
                rfl

theorem cell20_1031555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 7].length) (baseStart_1031555 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031555 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031555 prefixEnd_1031555 := by exact prefixLift 1031555
  have htrace : WordTrace (prefixWord ++ tailWord_1031555) baseStart_1031555 baseEnd_1031555 := by
    simpa [prefixWord, tailWord_1031555, baseEnd_1031555] using wordTrace_append hprefix tailTrace_1031555
  have hstable : (prefixWord ++ tailWord_1031555).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031555).length < 2 ^ (prefixWord ++ tailWord_1031555).sum := by decide
  have hdescent : baseEnd_1031555 < baseStart_1031555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031569 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_1031569 : Nat := 118140960795 + 1031569 * 2 ^ 59
def prefixEnd_1031569 : Nat := 4983230072969 + 3 ^ 40 * 1031569 * 2
def baseEnd_1031569 : Nat := 470836200247093080216361

theorem tailTrace_1031569 : CollatzResearch.WordTrace tailWord_1031569 prefixEnd_1031569 470836200247093080216361 := by
  unfold tailWord_1031569
  simp only [CollatzResearch.WordTrace]
  refine ⟨37624412399809165804065761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25082941599872777202710507 37624412399809165804065761)
  ·
    refine ⟨28218309299856874353049321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37624412399809165804065761 28218309299856874353049321)
    ·
      refine ⟨21163731974892655764786991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28218309299856874353049321 21163731974892655764786991)
      ·
        refine ⟨31745597962338983647180487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21163731974892655764786991 31745597962338983647180487)
        ·
          refine ⟨47618396943508475470770731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31745597962338983647180487 47618396943508475470770731)
          ·
            refine ⟨71427595415262713206156097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47618396943508475470770731 71427595415262713206156097)
            ·
              refine ⟨53570696561447034904617073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71427595415262713206156097 53570696561447034904617073)
              ·
                refine ⟨40178022421085276178462805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53570696561447034904617073 40178022421085276178462805)
                ·
                  refine ⟨470836200247093080216361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40178022421085276178462805 470836200247093080216361)
                  ·
                    rfl

theorem cell20_1031569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_1031569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031569 prefixEnd_1031569 := by exact prefixLift 1031569
  have htrace : WordTrace (prefixWord ++ tailWord_1031569) baseStart_1031569 baseEnd_1031569 := by
    simpa [prefixWord, tailWord_1031569, baseEnd_1031569] using wordTrace_append hprefix tailTrace_1031569
  have hstable : (prefixWord ++ tailWord_1031569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031569).length < 2 ^ (prefixWord ++ tailWord_1031569).sum := by decide
  have hdescent : baseEnd_1031569 < baseStart_1031569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031620 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 4]
def baseStart_1031620 : Nat := 118140960795 + 1031620 * 2 ^ 59
def prefixEnd_1031620 : Nat := 4983230072969 + 3 ^ 40 * 1031620 * 2
def baseEnd_1031620 : Nat := 470859478036763569516153

theorem tailTrace_1031620 : CollatzResearch.WordTrace tailWord_1031620 prefixEnd_1031620 470859478036763569516153 := by
  unfold tailWord_1031620
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813136261312200757086157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25084181681749601009448209 18813136261312200757086157)
  ·
    refine ⟨7054926097992075283907309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18813136261312200757086157 7054926097992075283907309)
    ·
      refine ⟨2645597286747028231465241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7054926097992075283907309 2645597286747028231465241)
      ·
        refine ⟨1984197965060271173598931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2645597286747028231465241 1984197965060271173598931)
        ·
          refine ⟨2976296947590406760398397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984197965060271173598931 2976296947590406760398397)
          ·
            refine ⟨1116111355346402535149399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2976296947590406760398397 1116111355346402535149399)
            ·
              refine ⟨1674167033019603802724099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116111355346402535149399 1674167033019603802724099)
              ·
                refine ⟨2511250549529405704086149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674167033019603802724099 2511250549529405704086149)
                ·
                  refine ⟨470859478036763569516153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511250549529405704086149 470859478036763569516153)
                  ·
                    rfl

theorem cell20_1031620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_1031620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031620 prefixEnd_1031620 := by exact prefixLift 1031620
  have htrace : WordTrace (prefixWord ++ tailWord_1031620) baseStart_1031620 baseEnd_1031620 := by
    simpa [prefixWord, tailWord_1031620, baseEnd_1031620] using wordTrace_append hprefix tailTrace_1031620
  have hstable : (prefixWord ++ tailWord_1031620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031620).length < 2 ^ (prefixWord ++ tailWord_1031620).sum := by decide
  have hdescent : baseEnd_1031620 < baseStart_1031620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031676 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_1031676 : Nat := 118140960795 + 1031676 * 2 ^ 59
def prefixEnd_1031676 : Nat := 4983230072969 + 3 ^ 40 * 1031676 * 2
def baseEnd_1031676 : Nat := 470885037962676263649257

theorem tailTrace_1031676 : CollatzResearch.WordTrace tailWord_1031676 prefixEnd_1031676 470885037962676263649257 := by
  unfold tailWord_1031676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18814157505210761539105441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25085543340281015385473921 18814157505210761539105441)
  ·
    refine ⟨14110618128908071154329081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18814157505210761539105441 14110618128908071154329081)
    ·
      refine ⟨10582963596681053365746811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14110618128908071154329081 10582963596681053365746811)
      ·
        refine ⟨15874445395021580048620217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10582963596681053365746811 15874445395021580048620217)
        ·
          refine ⟨11905834046266185036465163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15874445395021580048620217 11905834046266185036465163)
          ·
            refine ⟨17858751069399277554697745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11905834046266185036465163 17858751069399277554697745)
            ·
              refine ⟨13394063302049458166023309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17858751069399277554697745 13394063302049458166023309)
              ·
                refine ⟨5022773738268546812258741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13394063302049458166023309 5022773738268546812258741)
                ·
                  refine ⟨470885037962676263649257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022773738268546812258741 470885037962676263649257)
                  ·
                    rfl

theorem cell20_1031676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_1031676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031676 prefixEnd_1031676 := by exact prefixLift 1031676
  have htrace : WordTrace (prefixWord ++ tailWord_1031676) baseStart_1031676 baseEnd_1031676 := by
    simpa [prefixWord, tailWord_1031676, baseEnd_1031676] using wordTrace_append hprefix tailTrace_1031676
  have hstable : (prefixWord ++ tailWord_1031676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031676).length < 2 ^ (prefixWord ++ tailWord_1031676).sum := by decide
  have hdescent : baseEnd_1031676 < baseStart_1031676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031731 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_1031731 : Nat := 118140960795 + 1031731 * 2 ^ 59
def prefixEnd_1031731 : Nat := 4983230072969 + 3 ^ 40 * 1031731 * 2
def baseEnd_1031731 : Nat := 470910141461340516815699

theorem tailTrace_1031731 : CollatzResearch.WordTrace tailWord_1031731 prefixEnd_1031731 470910141461340516815699 := by
  unfold tailWord_1031731
  simp only [CollatzResearch.WordTrace]
  refine ⟨37630321025222267471463047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25086880683481511647642031 37630321025222267471463047)
  ·
    refine ⟨56445481537833401207194571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37630321025222267471463047 56445481537833401207194571)
    ·
      refine ⟨84668222306750101810791857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56445481537833401207194571 84668222306750101810791857)
      ·
        refine ⟨63501166730062576358093893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84668222306750101810791857 63501166730062576358093893)
        ·
          refine ⟨11906468761886733067142605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63501166730062576358093893 11906468761886733067142605)
          ·
            refine ⟨4464925785707524900178477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11906468761886733067142605 4464925785707524900178477)
            ·
              refine ⟨1674347169640321837566929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4464925785707524900178477 1674347169640321837566929)
              ·
                refine ⟨1255760377230241378175197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674347169640321837566929 1255760377230241378175197)
                ·
                  refine ⟨470910141461340516815699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255760377230241378175197 470910141461340516815699)
                  ·
                    rfl

theorem cell20_1031731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_1031731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031731 prefixEnd_1031731 := by exact prefixLift 1031731
  have htrace : WordTrace (prefixWord ++ tailWord_1031731) baseStart_1031731 baseEnd_1031731 := by
    simpa [prefixWord, tailWord_1031731, baseEnd_1031731] using wordTrace_append hprefix tailTrace_1031731
  have hstable : (prefixWord ++ tailWord_1031731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031731).length < 2 ^ (prefixWord ++ tailWord_1031731).sum := by decide
  have hdescent : baseEnd_1031731 < baseStart_1031731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031734 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1031734 : Nat := 118140960795 + 1031734 * 2 ^ 59
def prefixEnd_1031734 : Nat := 4983230072969 + 3 ^ 40 * 1031734 * 2
def baseEnd_1031734 : Nat := 470911510743085839715687

theorem tailTrace_1031734 : CollatzResearch.WordTrace tailWord_1031734 prefixEnd_1031734 470911510743085839715687 := by
  unfold tailWord_1031734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351901902763212436488891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25086953629474265989214837 2351901902763212436488891)
  ·
    refine ⟨3527852854144818654733337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2351901902763212436488891 3527852854144818654733337)
    ·
      refine ⟨2645889640608613991050003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3527852854144818654733337 2645889640608613991050003)
      ·
        refine ⟨3968834460912920986575005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645889640608613991050003 3968834460912920986575005)
        ·
          refine ⟨1488312922842345369965627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3968834460912920986575005 1488312922842345369965627)
          ·
            refine ⟨2232469384263518054948441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488312922842345369965627 2232469384263518054948441)
            ·
              refine ⟨1674352038197638541211331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232469384263518054948441 1674352038197638541211331)
              ·
                refine ⟨2511528057296457811816997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674352038197638541211331 2511528057296457811816997)
                ·
                  refine ⟨470911510743085839715687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511528057296457811816997 470911510743085839715687)
                  ·
                    rfl

theorem cell20_1031734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1031734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031734 prefixEnd_1031734 := by exact prefixLift 1031734
  have htrace : WordTrace (prefixWord ++ tailWord_1031734) baseStart_1031734 baseEnd_1031734 := by
    simpa [prefixWord, tailWord_1031734, baseEnd_1031734] using wordTrace_append hprefix tailTrace_1031734
  have hstable : (prefixWord ++ tailWord_1031734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031734).length < 2 ^ (prefixWord ++ tailWord_1031734).sum := by decide
  have hdescent : baseEnd_1031734 < baseStart_1031734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031738 : List Nat := [3, 1, 1, 1, 3, 2, 4, 1, 4]
def baseStart_1031738 : Nat := 118140960795 + 1031738 * 2 ^ 59
def prefixEnd_1031738 : Nat := 4983230072969 + 3 ^ 40 * 1031738 * 2
def baseEnd_1031738 : Nat := 470913336452079603582337

theorem tailTrace_1031738 : CollatzResearch.WordTrace tailWord_1031738 prefixEnd_1031738 470913336452079603582337 := by
  unfold tailWord_1031738
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407644084049226916741967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25087050890797938444645245 9407644084049226916741967)
  ·
    refine ⟨14111466126073840375112951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9407644084049226916741967 14111466126073840375112951)
    ·
      refine ⟨21167199189110760562669427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14111466126073840375112951 21167199189110760562669427)
      ·
        refine ⟨31750798783666140844004141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167199189110760562669427 31750798783666140844004141)
        ·
          refine ⟨11906549543874802816501553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31750798783666140844004141 11906549543874802816501553)
          ·
            refine ⟨8929912157906102112376165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11906549543874802816501553 8929912157906102112376165)
            ·
              refine ⟨1674358529607394146070531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8929912157906102112376165 1674358529607394146070531)
              ·
                refine ⟨2511537794411091219105797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674358529607394146070531 2511537794411091219105797)
                ·
                  refine ⟨470913336452079603582337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511537794411091219105797 470913336452079603582337)
                  ·
                    rfl

theorem cell20_1031738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_1031738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031738 prefixEnd_1031738 := by exact prefixLift 1031738
  have htrace : WordTrace (prefixWord ++ tailWord_1031738) baseStart_1031738 baseEnd_1031738 := by
    simpa [prefixWord, tailWord_1031738, baseEnd_1031738] using wordTrace_append hprefix tailTrace_1031738
  have hstable : (prefixWord ++ tailWord_1031738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031738).length < 2 ^ (prefixWord ++ tailWord_1031738).sum := by decide
  have hdescent : baseEnd_1031738 < baseStart_1031738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031745 : List Nat := [1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_1031745 : Nat := 118140960795 + 1031745 * 2 ^ 59
def prefixEnd_1031745 : Nat := 4983230072969 + 3 ^ 40 * 1031745 * 2
def baseEnd_1031745 : Nat := 156972177147606230116325

theorem tailTrace_1031745 : CollatzResearch.WordTrace tailWord_1031745 prefixEnd_1031745 156972177147606230116325 := by
  unfold tailWord_1031745
  simp only [CollatzResearch.WordTrace]
  refine ⟨37630831647171547862472689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25087221098114365241648459 37630831647171547862472689)
  ·
    refine ⟨28223123735378660896854517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37630831647171547862472689 28223123735378660896854517)
    ·
      refine ⟨2645917850191749459080111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28223123735378660896854517 2645917850191749459080111)
      ·
        refine ⟨3968876775287624188620167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645917850191749459080111 3968876775287624188620167)
        ·
          refine ⟨5953315162931436282930251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968876775287624188620167 5953315162931436282930251)
          ·
            refine ⟨8929972744397154424395377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953315162931436282930251 8929972744397154424395377)
            ·
              refine ⟨6697479558297865818296533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929972744397154424395377 6697479558297865818296533)
              ·
                refine ⟨156972177147606230116325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6697479558297865818296533 156972177147606230116325)
                ·
                  rfl

theorem cell20_1031745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_1031745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031745 prefixEnd_1031745 := by exact prefixLift 1031745
  have htrace : WordTrace (prefixWord ++ tailWord_1031745) baseStart_1031745 baseEnd_1031745 := by
    simpa [prefixWord, tailWord_1031745, baseEnd_1031745] using wordTrace_append hprefix tailTrace_1031745
  have hstable : (prefixWord ++ tailWord_1031745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031745).length < 2 ^ (prefixWord ++ tailWord_1031745).sum := by decide
  have hdescent : baseEnd_1031745 < baseStart_1031745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031762 : List Nat := [3, 2, 2, 1, 2, 2, 4, 4]
def baseStart_1031762 : Nat := 118140960795 + 1031762 * 2 ^ 59
def prefixEnd_1031762 : Nat := 4983230072969 + 3 ^ 40 * 1031762 * 2
def baseEnd_1031762 : Nat := 156974763568680728927413

theorem tailTrace_1031762 : CollatzResearch.WordTrace tailWord_1031762 prefixEnd_1031762 156974763568680728927413 := by
  unfold tailWord_1031762
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407862922027489941460385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25087634458739973177227693 9407862922027489941460385)
  ·
    refine ⟨7055897191520617456095289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9407862922027489941460385 7055897191520617456095289)
    ·
      refine ⟨5291922893640463092071467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7055897191520617456095289 5291922893640463092071467)
      ·
        refine ⟨7937884340460694638107201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291922893640463092071467 7937884340460694638107201)
        ·
          refine ⟨5953413255345520978580401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7937884340460694638107201 5953413255345520978580401)
          ·
            refine ⟨4465059941509140733935301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5953413255345520978580401 4465059941509140733935301)
            ·
              refine ⟨837198739032963887612869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4465059941509140733935301 837198739032963887612869)
              ·
                refine ⟨156974763568680728927413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837198739032963887612869 156974763568680728927413)
                ·
                  rfl

theorem cell20_1031762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_1031762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031762 prefixEnd_1031762 := by exact prefixLift 1031762
  have htrace : WordTrace (prefixWord ++ tailWord_1031762) baseStart_1031762 baseEnd_1031762 := by
    simpa [prefixWord, tailWord_1031762, baseEnd_1031762] using wordTrace_append hprefix tailTrace_1031762
  have hstable : (prefixWord ++ tailWord_1031762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031762).length < 2 ^ (prefixWord ++ tailWord_1031762).sum := by decide
  have hdescent : baseEnd_1031762 < baseStart_1031762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031772 : List Nat := [2, 2, 4, 1, 2, 1, 3, 3, 2]
def baseStart_1031772 : Nat := 118140960795 + 1031772 * 2 ^ 59
def prefixEnd_1031772 : Nat := 4983230072969 + 3 ^ 40 * 1031772 * 2
def baseEnd_1031772 : Nat := 470928854978526596448865

theorem tailTrace_1031772 : CollatzResearch.WordTrace tailWord_1031772 prefixEnd_1031772 470928854978526596448865 := by
  unfold tailWord_1031772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815908209036865736852785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25087877612049154315803713 18815908209036865736852785)
  ·
    refine ⟨14111931156777649302639589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18815908209036865736852785 14111931156777649302639589)
    ·
      refine ⟨2645987091895809244244923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14111931156777649302639589 2645987091895809244244923)
      ·
        refine ⟨3968980637843713866367385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645987091895809244244923 3968980637843713866367385)
        ·
          refine ⟨2976735478382785399775539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3968980637843713866367385 2976735478382785399775539)
          ·
            refine ⟨4465103217574178099663309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976735478382785399775539 4465103217574178099663309)
            ·
              refine ⟨1674413706590316787373741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4465103217574178099663309 1674413706590316787373741)
              ·
                refine ⟨627905139971368795265153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1674413706590316787373741 627905139971368795265153)
                ·
                  refine ⟨470928854978526596448865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627905139971368795265153 470928854978526596448865)
                  ·
                    rfl

theorem cell20_1031772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_1031772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031772 prefixEnd_1031772 := by exact prefixLift 1031772
  have htrace : WordTrace (prefixWord ++ tailWord_1031772) baseStart_1031772 baseEnd_1031772 := by
    simpa [prefixWord, tailWord_1031772, baseEnd_1031772] using wordTrace_append hprefix tailTrace_1031772
  have hstable : (prefixWord ++ tailWord_1031772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031772).length < 2 ^ (prefixWord ++ tailWord_1031772).sum := by decide
  have hdescent : baseEnd_1031772 < baseStart_1031772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031789 : List Nat := [1, 5, 1, 1, 4, 1, 3, 2, 2]
def baseStart_1031789 : Nat := 118140960795 + 1031789 * 2 ^ 59
def prefixEnd_1031789 : Nat := 4983230072969 + 3 ^ 40 * 1031789 * 2
def baseEnd_1031789 : Nat := 470936614241750092882129

theorem tailTrace_1031789 : CollatzResearch.WordTrace tailWord_1031789 prefixEnd_1031789 470936614241750092882129 := by
  unfold tailWord_1031789
  simp only [CollatzResearch.WordTrace]
  refine ⟨37632436459012143377074421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25088290972674762251382947 37632436459012143377074421)
  ·
    refine ⟨3528040918032388441600727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37632436459012143377074421 3528040918032388441600727)
    ·
      refine ⟨5292061377048582662401091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3528040918032388441600727 5292061377048582662401091)
      ·
        refine ⟨7938092065572873993601637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292061377048582662401091 7938092065572873993601637)
        ·
          refine ⟨1488392262294913873800307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7938092065572873993601637 1488392262294913873800307)
          ·
            refine ⟨2232588393442370810700461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488392262294913873800307 2232588393442370810700461)
            ·
              refine ⟨837220647540889054012673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2232588393442370810700461 837220647540889054012673)
              ·
                refine ⟨627915485655666790509505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837220647540889054012673 627915485655666790509505)
                ·
                  refine ⟨470936614241750092882129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627915485655666790509505 470936614241750092882129)
                  ·
                    rfl

theorem cell20_1031789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_1031789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031789 prefixEnd_1031789 := by exact prefixLift 1031789
  have htrace : WordTrace (prefixWord ++ tailWord_1031789) baseStart_1031789 baseEnd_1031789 := by
    simpa [prefixWord, tailWord_1031789, baseEnd_1031789] using wordTrace_append hprefix tailTrace_1031789
  have hstable : (prefixWord ++ tailWord_1031789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031789).length < 2 ^ (prefixWord ++ tailWord_1031789).sum := by decide
  have hdescent : baseEnd_1031789 < baseStart_1031789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031876 : List Nat := [2, 3, 3, 1, 1, 1, 5, 4]
def baseStart_1031876 : Nat := 118140960795 + 1031876 * 2 ^ 59
def prefixEnd_1031876 : Nat := 4983230072969 + 3 ^ 40 * 1031876 * 2
def baseEnd_1031876 : Nat := 156992107804121485660591

theorem tailTrace_1031876 : CollatzResearch.WordTrace tailWord_1031876 prefixEnd_1031876 156992107804121485660591 := by
  unfold tailWord_1031876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18817804804848478617745741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25090406406464638156994321 18817804804848478617745741)
  ·
    refine ⟨7056676801818179481654653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18817804804848478617745741 7056676801818179481654653)
    ·
      refine ⟨2646253800681817305620495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7056676801818179481654653 2646253800681817305620495)
      ·
        refine ⟨3969380701022725958430743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646253800681817305620495 3969380701022725958430743)
        ·
          refine ⟨5954071051534088937646115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969380701022725958430743 5954071051534088937646115)
          ·
            refine ⟨8931106577301133406469173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954071051534088937646115 8931106577301133406469173)
            ·
              refine ⟨837291241621981256856485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8931106577301133406469173 837291241621981256856485)
              ·
                refine ⟨156992107804121485660591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837291241621981256856485 156992107804121485660591)
                ·
                  rfl

theorem cell20_1031876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 4].length) (baseStart_1031876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031876 prefixEnd_1031876 := by exact prefixLift 1031876
  have htrace : WordTrace (prefixWord ++ tailWord_1031876) baseStart_1031876 baseEnd_1031876 := by
    simpa [prefixWord, tailWord_1031876, baseEnd_1031876] using wordTrace_append hprefix tailTrace_1031876
  have hstable : (prefixWord ++ tailWord_1031876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031876).length < 2 ^ (prefixWord ++ tailWord_1031876).sum := by decide
  have hdescent : baseEnd_1031876 < baseStart_1031876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031900 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 5]
def baseStart_1031900 : Nat := 118140960795 + 1031900 * 2 ^ 59
def prefixEnd_1031900 : Nat := 4983230072969 + 3 ^ 40 * 1031900 * 2
def baseEnd_1031900 : Nat := 470987277666327040181675

theorem tailTrace_1031900 : CollatzResearch.WordTrace tailWord_1031900 prefixEnd_1031900 470987277666327040181675 := by
  unfold tailWord_1031900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818242480805004667182577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25090989974406672889576769 18818242480805004667182577)
  ·
    refine ⟨14113681860603753500386933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18818242480805004667182577 14113681860603753500386933)
    ·
      refine ⟨1323157674431601890661275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14113681860603753500386933 1323157674431601890661275)
      ·
        refine ⟨1984736511647402835991913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323157674431601890661275 1984736511647402835991913)
        ·
          refine ⟨1488552383735552126993935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984736511647402835991913 1488552383735552126993935)
          ·
            refine ⟨2232828575603328190490903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488552383735552126993935 2232828575603328190490903)
            ·
              refine ⟨3349242863404992285736355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232828575603328190490903 3349242863404992285736355)
              ·
                refine ⟨5023864295107488428604533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3349242863404992285736355 5023864295107488428604533)
                ·
                  refine ⟨470987277666327040181675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5023864295107488428604533 470987277666327040181675)
                  ·
                    rfl

theorem cell20_1031900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_1031900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031900 prefixEnd_1031900 := by exact prefixLift 1031900
  have htrace : WordTrace (prefixWord ++ tailWord_1031900) baseStart_1031900 baseEnd_1031900 := by
    simpa [prefixWord, tailWord_1031900, baseEnd_1031900] using wordTrace_append hprefix tailTrace_1031900
  have hstable : (prefixWord ++ tailWord_1031900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031900).length < 2 ^ (prefixWord ++ tailWord_1031900).sum := by decide
  have hdescent : baseEnd_1031900 < baseStart_1031900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031907 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 4]
def baseStart_1031907 : Nat := 118140960795 + 1031907 * 2 ^ 59
def prefixEnd_1031907 : Nat := 4983230072969 + 3 ^ 40 * 1031907 * 2
def baseEnd_1031907 : Nat := 470990472657066126948313

theorem tailTrace_1031907 : CollatzResearch.WordTrace tailWord_1031907 prefixEnd_1031907 470990472657066126948313 := by
  unfold tailWord_1031907
  simp only [CollatzResearch.WordTrace]
  refine ⟨37636740272584649529869975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25091160181723099686579983 37636740272584649529869975)
  ·
    refine ⟨56455110408876974294804963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37636740272584649529869975 56455110408876974294804963)
    ·
      refine ⟨84682665613315461442207445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56455110408876974294804963 84682665613315461442207445)
      ·
        refine ⟨1984749975312081127551737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84682665613315461442207445 1984749975312081127551737)
        ·
          refine ⟨1488562481484060845663803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984749975312081127551737 1488562481484060845663803)
          ·
            refine ⟨2232843722226091268495705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488562481484060845663803 2232843722226091268495705)
            ·
              refine ⟨1674632791669568451371779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232843722226091268495705 1674632791669568451371779)
              ·
                refine ⟨2511949187504352677057669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674632791669568451371779 2511949187504352677057669)
                ·
                  refine ⟨470990472657066126948313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511949187504352677057669 470990472657066126948313)
                  ·
                    rfl

theorem cell20_1031907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 4].length) (baseStart_1031907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031907 prefixEnd_1031907 := by exact prefixLift 1031907
  have htrace : WordTrace (prefixWord ++ tailWord_1031907) baseStart_1031907 baseEnd_1031907 := by
    simpa [prefixWord, tailWord_1031907, baseEnd_1031907] using wordTrace_append hprefix tailTrace_1031907
  have hstable : (prefixWord ++ tailWord_1031907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031907).length < 2 ^ (prefixWord ++ tailWord_1031907).sum := by decide
  have hdescent : baseEnd_1031907 < baseStart_1031907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031924 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1031924 : Nat := 118140960795 + 1031924 * 2 ^ 59
def prefixEnd_1031924 : Nat := 4983230072969 + 3 ^ 40 * 1031924 * 2
def baseEnd_1031924 : Nat := 470998231920289623381577

theorem tailTrace_1031924 : CollatzResearch.WordTrace tailWord_1031924 prefixEnd_1031924 470998231920289623381577 := by
  unfold tailWord_1031924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18818680156761530716619413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25091573542348707622159217 18818680156761530716619413)
  ·
    refine ⟨882125632348196752341535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18818680156761530716619413 882125632348196752341535)
    ·
      refine ⟨1323188448522295128512303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 882125632348196752341535 1323188448522295128512303)
      ·
        refine ⟨1984782672783442692768455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1323188448522295128512303 1984782672783442692768455)
        ·
          refine ⟨2977174009175164039152683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984782672783442692768455 2977174009175164039152683)
          ·
            refine ⟨4465761013762746058729025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977174009175164039152683 4465761013762746058729025)
            ·
              refine ⟨3349320760322059544046769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465761013762746058729025 3349320760322059544046769)
              ·
                refine ⟨2511990570241544658035077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349320760322059544046769 2511990570241544658035077)
                ·
                  refine ⟨470998231920289623381577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511990570241544658035077 470998231920289623381577)
                  ·
                    rfl

theorem cell20_1031924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1031924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031924 prefixEnd_1031924 := by exact prefixLift 1031924
  have htrace : WordTrace (prefixWord ++ tailWord_1031924) baseStart_1031924 baseEnd_1031924 := by
    simpa [prefixWord, tailWord_1031924, baseEnd_1031924] using wordTrace_append hprefix tailTrace_1031924
  have hstable : (prefixWord ++ tailWord_1031924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031924).length < 2 ^ (prefixWord ++ tailWord_1031924).sum := by decide
  have hdescent : baseEnd_1031924 < baseStart_1031924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031935 : List Nat := [1, 1, 2, 2, 1, 3, 6, 4]
def baseStart_1031935 : Nat := 118140960795 + 1031935 * 2 ^ 59
def prefixEnd_1031935 : Nat := 4983230072969 + 3 ^ 40 * 1031935 * 2
def baseEnd_1031935 : Nat := 157001084206674158004955

theorem tailTrace_1031935 : CollatzResearch.WordTrace tailWord_1031935 prefixEnd_1031935 157001084206674158004955 := by
  unfold tailWord_1031935
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637761516483210311889259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25091841010988806874592839 37637761516483210311889259)
  ·
    refine ⟨56456642274724815467833889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37637761516483210311889259 56456642274724815467833889)
    ·
      refine ⟨42342481706043611600875417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56456642274724815467833889 42342481706043611600875417)
      ·
        refine ⟨31756861279532708700656563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42342481706043611600875417 31756861279532708700656563)
        ·
          refine ⟨47635291919299063050984845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31756861279532708700656563 47635291919299063050984845)
          ·
            refine ⟨17863234469737148644119317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47635291919299063050984845 17863234469737148644119317)
            ·
              refine ⟨837339115768928842693093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17863234469737148644119317 837339115768928842693093)
              ·
                refine ⟨157001084206674158004955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837339115768928842693093 157001084206674158004955)
                ·
                  rfl

theorem cell20_1031935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 6, 4].length) (baseStart_1031935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031935 prefixEnd_1031935 := by exact prefixLift 1031935
  have htrace : WordTrace (prefixWord ++ tailWord_1031935) baseStart_1031935 baseEnd_1031935 := by
    simpa [prefixWord, tailWord_1031935, baseEnd_1031935] using wordTrace_append hprefix tailTrace_1031935
  have hstable : (prefixWord ++ tailWord_1031935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031935).length < 2 ^ (prefixWord ++ tailWord_1031935).sum := by decide
  have hdescent : baseEnd_1031935 < baseStart_1031935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031962 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_1031962 : Nat := 118140960795 + 1031962 * 2 ^ 59
def prefixEnd_1031962 : Nat := 4983230072969 + 3 ^ 40 * 1031962 * 2
def baseEnd_1031962 : Nat := 471015576155730380114755

theorem tailTrace_1031962 : CollatzResearch.WordTrace tailWord_1031962 prefixEnd_1031962 471015576155730380114755 := by
  unfold tailWord_1031962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409686571846348480780535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25092497524923595948748093 9409686571846348480780535)
  ·
    refine ⟨14114529857769522721170803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9409686571846348480780535 14114529857769522721170803)
    ·
      refine ⟨21171794786654284081756205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114529857769522721170803 21171794786654284081756205)
      ·
        refine ⟨7939423044995356530658577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21171794786654284081756205 7939423044995356530658577)
        ·
          refine ⟨5954567283746517397993933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939423044995356530658577 5954567283746517397993933)
          ·
            refine ⟨2232962731404944024247725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5954567283746517397993933 2232962731404944024247725)
            ·
              refine ⟨837361024276854009092897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2232962731404944024247725 837361024276854009092897)
              ·
                refine ⟨628020768207640506819673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837361024276854009092897 628020768207640506819673)
                ·
                  refine ⟨471015576155730380114755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628020768207640506819673 471015576155730380114755)
                  ·
                    rfl

theorem cell20_1031962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_1031962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031962 prefixEnd_1031962 := by exact prefixLift 1031962
  have htrace : WordTrace (prefixWord ++ tailWord_1031962) baseStart_1031962 baseEnd_1031962 := by
    simpa [prefixWord, tailWord_1031962, baseEnd_1031962] using wordTrace_append hprefix tailTrace_1031962
  have hstable : (prefixWord ++ tailWord_1031962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031962).length < 2 ^ (prefixWord ++ tailWord_1031962).sum := by decide
  have hdescent : baseEnd_1031962 < baseStart_1031962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031973 : List Nat := [1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_1031973 : Nat := 118140960795 + 1031973 * 2 ^ 59
def prefixEnd_1031973 : Nat := 4983230072969 + 3 ^ 40 * 1031973 * 2
def baseEnd_1031973 : Nat := 157006865618487743582681

theorem tailTrace_1031973 : CollatzResearch.WordTrace tailWord_1031973 prefixEnd_1031973 157006865618487743582681 := by
  unfold tailWord_1031973
  simp only [CollatzResearch.WordTrace]
  refine ⟨37639147490345542801772573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25092764993563695201181715 37639147490345542801772573)
  ·
    refine ⟨14114680308879578550664715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37639147490345542801772573 14114680308879578550664715)
    ·
      refine ⟨21172020463319367825997073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14114680308879578550664715 21172020463319367825997073)
      ·
        refine ⟨15879015347489525869497805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21172020463319367825997073 15879015347489525869497805)
        ·
          refine ⟨5954630755308572201061677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15879015347489525869497805 5954630755308572201061677)
          ·
            refine ⟨2232986533240714575398129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5954630755308572201061677 2232986533240714575398129)
            ·
              refine ⟨1674739899930535931548597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232986533240714575398129 1674739899930535931548597)
              ·
                refine ⟨157006865618487743582681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1674739899930535931548597 157006865618487743582681)
                ·
                  rfl

theorem cell20_1031973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_1031973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031973 prefixEnd_1031973 := by exact prefixLift 1031973
  have htrace : WordTrace (prefixWord ++ tailWord_1031973) baseStart_1031973 baseEnd_1031973 := by
    simpa [prefixWord, tailWord_1031973, baseEnd_1031973] using wordTrace_append hprefix tailTrace_1031973
  have hstable : (prefixWord ++ tailWord_1031973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031973).length < 2 ^ (prefixWord ++ tailWord_1031973).sum := by decide
  have hdescent : baseEnd_1031973 < baseStart_1031973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031976 : List Nat := [2, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_1031976 : Nat := 118140960795 + 1031976 * 2 ^ 59
def prefixEnd_1031976 : Nat := 4983230072969 + 3 ^ 40 * 1031976 * 2
def baseEnd_1031976 : Nat := 471021966137208553648031

theorem tailTrace_1031976 : CollatzResearch.WordTrace tailWord_1031976 prefixEnd_1031976 471021966137208553648031 := by
  unfold tailWord_1031976
  simp only [CollatzResearch.WordTrace]
  refine ⟨18819628454667337157065891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25092837939556449542754521 18819628454667337157065891)
  ·
    refine ⟨28229442682001005735598837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18819628454667337157065891 28229442682001005735598837)
    ·
      refine ⟨2646510251437594287712391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28229442682001005735598837 2646510251437594287712391)
      ·
        refine ⟨3969765377156391431568587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646510251437594287712391 3969765377156391431568587)
        ·
          refine ⟨5954648065734587147352881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969765377156391431568587 5954648065734587147352881)
          ·
            refine ⟨4465986049300940360514661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5954648065734587147352881 4465986049300940360514661)
            ·
              refine ⟨837372384243926317596499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4465986049300940360514661 837372384243926317596499)
              ·
                refine ⟨1256058576365889476394749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837372384243926317596499 1256058576365889476394749)
                ·
                  refine ⟨471021966137208553648031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256058576365889476394749 471021966137208553648031)
                  ·
                    rfl

theorem cell20_1031976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_1031976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031976 prefixEnd_1031976 := by exact prefixLift 1031976
  have htrace : WordTrace (prefixWord ++ tailWord_1031976) baseStart_1031976 baseEnd_1031976 := by
    simpa [prefixWord, tailWord_1031976, baseEnd_1031976] using wordTrace_append hprefix tailTrace_1031976
  have hstable : (prefixWord ++ tailWord_1031976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031976).length < 2 ^ (prefixWord ++ tailWord_1031976).sum := by decide
  have hdescent : baseEnd_1031976 < baseStart_1031976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1031990 : List Nat := [5, 1, 2, 2, 1, 1, 2, 6]
def baseStart_1031990 : Nat := 118140960795 + 1031990 * 2 ^ 59
def prefixEnd_1031990 : Nat := 4983230072969 + 3 ^ 40 * 1031990 * 2
def baseEnd_1031990 : Nat := 157009452039562242393769

theorem tailTrace_1031990 : CollatzResearch.WordTrace tailWord_1031990 prefixEnd_1031990 157009452039562242393769 := by
  unfold tailWord_1031990
  simp only [CollatzResearch.WordTrace]
  refine ⟨2352485470705247169071339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25093178354189303136760949 2352485470705247169071339)
  ·
    refine ⟨3528728206057870753607009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2352485470705247169071339 3528728206057870753607009)
    ·
      refine ⟨2646546154543403065205257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3528728206057870753607009 2646546154543403065205257)
      ·
        refine ⟨1984909615907552298903943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646546154543403065205257 1984909615907552298903943)
        ·
          refine ⟨2977364423861328448355915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984909615907552298903943 2977364423861328448355915)
          ·
            refine ⟨4466046635791992672533873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977364423861328448355915 4466046635791992672533873)
            ·
              refine ⟨3349534976843994504400405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4466046635791992672533873 3349534976843994504400405)
              ·
                refine ⟨157009452039562242393769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3349534976843994504400405 157009452039562242393769)
                ·
                  rfl

theorem cell20_1031990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_1031990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1031990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1031990 prefixEnd_1031990 := by exact prefixLift 1031990
  have htrace : WordTrace (prefixWord ++ tailWord_1031990) baseStart_1031990 baseEnd_1031990 := by
    simpa [prefixWord, tailWord_1031990, baseEnd_1031990] using wordTrace_append hprefix tailTrace_1031990
  have hstable : (prefixWord ++ tailWord_1031990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1031990).length < 2 ^ (prefixWord ++ tailWord_1031990).sum := by decide
  have hdescent : baseEnd_1031990 < baseStart_1031990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1031990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032021 : List Nat := [1, 3, 2, 2, 2, 3, 1, 4, 2]
def baseStart_1032021 : Nat := 118140960795 + 1032021 * 2 ^ 59
def prefixEnd_1032021 : Nat := 4983230072969 + 3 ^ 40 * 1032021 * 2
def baseEnd_1032021 : Nat := 471042505363388397147847

theorem tailTrace_1032021 : CollatzResearch.WordTrace tailWord_1032021 prefixEnd_1032021 471042505363388397147847 := by
  unfold tailWord_1032021
  simp only [CollatzResearch.WordTrace]
  refine ⟨37640898194171646999519917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25093932129447764666346611 37640898194171646999519917)
  ·
    refine ⟨14115336822814367624819969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37640898194171646999519917 14115336822814367624819969)
    ·
      refine ⟨10586502617110775718614977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14115336822814367624819969 10586502617110775718614977)
      ·
        refine ⟨7939876962833081788961233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10586502617110775718614977 7939876962833081788961233)
        ·
          refine ⟨5954907722124811341720925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939876962833081788961233 5954907722124811341720925)
          ·
            refine ⟨2233090395796804253145347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5954907722124811341720925 2233090395796804253145347)
            ·
              refine ⟨3349635593695206379718021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233090395796804253145347 3349635593695206379718021)
              ·
                refine ⟨628056673817851196197129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3349635593695206379718021 628056673817851196197129)
                ·
                  refine ⟨471042505363388397147847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628056673817851196197129 471042505363388397147847)
                  ·
                    rfl

theorem cell20_1032021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_1032021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032021 prefixEnd_1032021 := by exact prefixLift 1032021
  have htrace : WordTrace (prefixWord ++ tailWord_1032021) baseStart_1032021 baseEnd_1032021 := by
    simpa [prefixWord, tailWord_1032021, baseEnd_1032021] using wordTrace_append hprefix tailTrace_1032021
  have hstable : (prefixWord ++ tailWord_1032021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032021).length < 2 ^ (prefixWord ++ tailWord_1032021).sum := by decide
  have hdescent : baseEnd_1032021 < baseStart_1032021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032025 : List Nat := [1, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_1032025 : Nat := 118140960795 + 1032025 * 2 ^ 59
def prefixEnd_1032025 : Nat := 4983230072969 + 3 ^ 40 * 1032025 * 2
def baseEnd_1032025 : Nat := 471044331072382161014497

theorem tailTrace_1032025 : CollatzResearch.WordTrace tailWord_1032025 prefixEnd_1032025 471044331072382161014497 := by
  unfold tailWord_1032025
  simp only [CollatzResearch.WordTrace]
  refine ⟨37641044086157155682665529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25094029390771437121777019 37641044086157155682665529)
  ·
    refine ⟨28230783064617866761999147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37641044086157155682665529 28230783064617866761999147)
    ·
      refine ⟨42346174596926800142998721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28230783064617866761999147 42346174596926800142998721)
      ·
        refine ⟨31759630947695100107249041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42346174596926800142998721 31759630947695100107249041)
        ·
          refine ⟨23819723210771325080436781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31759630947695100107249041 23819723210771325080436781)
          ·
            refine ⟨8932396204039246905163793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23819723210771325080436781 8932396204039246905163793)
            ·
              refine ⟨6699297153029435178872845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8932396204039246905163793 6699297153029435178872845)
              ·
                refine ⟨2512236432386038192077317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6699297153029435178872845 2512236432386038192077317)
                ·
                  refine ⟨471044331072382161014497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2512236432386038192077317 471044331072382161014497)
                  ·
                    rfl

theorem cell20_1032025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_1032025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032025 prefixEnd_1032025 := by exact prefixLift 1032025
  have htrace : WordTrace (prefixWord ++ tailWord_1032025) baseStart_1032025 baseEnd_1032025 := by
    simpa [prefixWord, tailWord_1032025, baseEnd_1032025] using wordTrace_append hprefix tailTrace_1032025
  have hstable : (prefixWord ++ tailWord_1032025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032025).length < 2 ^ (prefixWord ++ tailWord_1032025).sum := by decide
  have hdescent : baseEnd_1032025 < baseStart_1032025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032049 : List Nat := [1, 2, 2, 2, 1, 3, 5, 4]
def baseStart_1032049 : Nat := 118140960795 + 1032049 * 2 ^ 59
def prefixEnd_1032049 : Nat := 4983230072969 + 3 ^ 40 * 1032049 * 2
def baseEnd_1032049 : Nat := 157018428442114914738133

theorem tailTrace_1032049 : CollatzResearch.WordTrace tailWord_1032049 prefixEnd_1032049 157018428442114914738133 := by
  unfold tailWord_1032049
  simp only [CollatzResearch.WordTrace]
  refine ⟨37641919438070207781539201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25094612958713471854359467 37641919438070207781539201)
  ·
    refine ⟨28231439578552655836154401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37641919438070207781539201 28231439578552655836154401)
    ·
      refine ⟨21173579683914491877115801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28231439578552655836154401 21173579683914491877115801)
      ·
        refine ⟨15880184762935868907836851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21173579683914491877115801 15880184762935868907836851)
        ·
          refine ⟨23820277144403803361755277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15880184762935868907836851 23820277144403803361755277)
          ·
            refine ⟨8932603929151426260658229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23820277144403803361755277 8932603929151426260658229)
            ·
              refine ⟨837431618357946211936709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8932603929151426260658229 837431618357946211936709)
              ·
                refine ⟨157018428442114914738133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837431618357946211936709 157018428442114914738133)
                ·
                  rfl

theorem cell20_1032049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 5, 4].length) (baseStart_1032049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032049 prefixEnd_1032049 := by exact prefixLift 1032049
  have htrace : WordTrace (prefixWord ++ tailWord_1032049) baseStart_1032049 baseEnd_1032049 := by
    simpa [prefixWord, tailWord_1032049, baseEnd_1032049] using wordTrace_append hprefix tailTrace_1032049
  have hstable : (prefixWord ++ tailWord_1032049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032049).length < 2 ^ (prefixWord ++ tailWord_1032049).sum := by decide
  have hdescent : baseEnd_1032049 < baseStart_1032049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032090 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_1032090 : Nat := 118140960795 + 1032090 * 2 ^ 59
def prefixEnd_1032090 : Nat := 4983230072969 + 3 ^ 40 * 1032090 * 2
def baseEnd_1032090 : Nat := 471073998843530823847565

theorem tailTrace_1032090 : CollatzResearch.WordTrace tailWord_1032090 prefixEnd_1032090 471073998843530823847565 := by
  unfold tailWord_1032090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9410853707730417945945431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25095609887281114522521149 9410853707730417945945431)
  ·
    refine ⟨14116280561595626918918147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9410853707730417945945431 14116280561595626918918147)
    ·
      refine ⟨21174420842393440378377221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14116280561595626918918147 21174420842393440378377221)
      ·
        refine ⟨3970203907948770070945729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21174420842393440378377221 3970203907948770070945729)
        ·
          refine ⟨2977652930961577553209297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3970203907948770070945729 2977652930961577553209297)
          ·
            refine ⟨2233239698221183164906973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977652930961577553209297 2233239698221183164906973)
            ·
              refine ⟨837464886832943686840115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2233239698221183164906973 837464886832943686840115)
              ·
                refine ⟨1256197330249415530260173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837464886832943686840115 1256197330249415530260173)
                ·
                  refine ⟨471073998843530823847565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256197330249415530260173 471073998843530823847565)
                  ·
                    rfl

theorem cell20_1032090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_1032090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032090 prefixEnd_1032090 := by exact prefixLift 1032090
  have htrace : WordTrace (prefixWord ++ tailWord_1032090) baseStart_1032090 baseEnd_1032090 := by
    simpa [prefixWord, tailWord_1032090, baseEnd_1032090] using wordTrace_append hprefix tailTrace_1032090
  have hstable : (prefixWord ++ tailWord_1032090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032090).length < 2 ^ (prefixWord ++ tailWord_1032090).sum := by decide
  have hdescent : baseEnd_1032090 < baseStart_1032090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032115 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_1032115 : Nat := 118140960795 + 1032115 * 2 ^ 59
def prefixEnd_1032115 : Nat := 4983230072969 + 3 ^ 40 * 1032115 * 2
def baseEnd_1032115 : Nat := 471085409524741848014129

theorem tailTrace_1032115 : CollatzResearch.WordTrace tailWord_1032115 prefixEnd_1032115 471085409524741848014129 := by
  unfold tailWord_1032115
  simp only [CollatzResearch.WordTrace]
  refine ⟨37644326655831101053441799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25096217770554067368961199 37644326655831101053441799)
  ·
    refine ⟨56466489983746651580162699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37644326655831101053441799 56466489983746651580162699)
    ·
      refine ⟨84699734975619977370244049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56466489983746651580162699 84699734975619977370244049)
      ·
        refine ⟨63524801231714983027683037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84699734975619977370244049 63524801231714983027683037)
        ·
          refine ⟨23821800461893118635381139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63524801231714983027683037 23821800461893118635381139)
          ·
            refine ⟨35732700692839677953071709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23821800461893118635381139 35732700692839677953071709)
            ·
              refine ⟨13399762759814879232401891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35732700692839677953071709 13399762759814879232401891)
              ·
                refine ⟨20099644139722318848602837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13399762759814879232401891 20099644139722318848602837)
                ·
                  refine ⟨471085409524741848014129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20099644139722318848602837 471085409524741848014129)
                  ·
                    rfl

theorem cell20_1032115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_1032115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032115 prefixEnd_1032115 := by exact prefixLift 1032115
  have htrace : WordTrace (prefixWord ++ tailWord_1032115) baseStart_1032115 baseEnd_1032115 := by
    simpa [prefixWord, tailWord_1032115, baseEnd_1032115] using wordTrace_append hprefix tailTrace_1032115
  have hstable : (prefixWord ++ tailWord_1032115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032115).length < 2 ^ (prefixWord ++ tailWord_1032115).sum := by decide
  have hdescent : baseEnd_1032115 < baseStart_1032115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032125 : List Nat := [1, 4, 1, 2, 3, 3, 6]
def baseStart_1032125 : Nat := 118140960795 + 1032125 * 2 ^ 59
def prefixEnd_1032125 : Nat := 4983230072969 + 3 ^ 40 * 1032125 * 2
def baseEnd_1032125 : Nat := 52343330421914028631195

theorem tailTrace_1032125 : CollatzResearch.WordTrace tailWord_1032125 prefixEnd_1032125 52343330421914028631195 := by
  unfold tailWord_1032125
  simp only [CollatzResearch.WordTrace]
  refine ⟨37644691385794872761305829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25096460923863248507537219 37644691385794872761305829)
  ·
    refine ⟨7058379634836538642744843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37644691385794872761305829 7058379634836538642744843)
    ·
      refine ⟨10587569452254807964117265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058379634836538642744843 10587569452254807964117265)
      ·
        refine ⟨7940677089191105973087949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10587569452254807964117265 7940677089191105973087949)
        ·
          refine ⟨2977753908446664739907981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7940677089191105973087949 2977753908446664739907981)
          ·
            refine ⟨1116657715667499277465493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2977753908446664739907981 1116657715667499277465493)
            ·
              refine ⟨52343330421914028631195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1116657715667499277465493 52343330421914028631195)
              ·
                rfl

theorem cell20_1032125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 6].length) (baseStart_1032125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032125 prefixEnd_1032125 := by exact prefixLift 1032125
  have htrace : WordTrace (prefixWord ++ tailWord_1032125) baseStart_1032125 baseEnd_1032125 := by
    simpa [prefixWord, tailWord_1032125, baseEnd_1032125] using wordTrace_append hprefix tailTrace_1032125
  have hstable : (prefixWord ++ tailWord_1032125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032125).length < 2 ^ (prefixWord ++ tailWord_1032125).sum := by decide
  have hdescent : baseEnd_1032125 < baseStart_1032125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032149 : List Nat := [1, 3, 2, 3, 2, 2, 1, 3, 3]
def baseStart_1032149 : Nat := 118140960795 + 1032149 * 2 ^ 59
def prefixEnd_1032149 : Nat := 4983230072969 + 3 ^ 40 * 1032149 * 2
def baseEnd_1032149 : Nat := 471100928051188840880657

theorem tailTrace_1032149 : CollatzResearch.WordTrace tailWord_1032149 prefixEnd_1032149 471100928051188840880657 := by
  unfold tailWord_1032149
  simp only [CollatzResearch.WordTrace]
  refine ⟨37645566737707924860179501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25097044491805283240119667 37645566737707924860179501)
  ·
    refine ⟨14117087526640471822567313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37645566737707924860179501 14117087526640471822567313)
    ·
      refine ⟨10587815644980353866925485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14117087526640471822567313 10587815644980353866925485)
      ·
        refine ⟨3970430866867632700097057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10587815644980353866925485 3970430866867632700097057)
        ·
          refine ⟨2977823150150724525072793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3970430866867632700097057 2977823150150724525072793)
          ·
            refine ⟨2233367362613043393804595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977823150150724525072793 2233367362613043393804595)
            ·
              refine ⟨3350051043919565090706893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233367362613043393804595 3350051043919565090706893)
              ·
                refine ⟨1256269141469836909015085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350051043919565090706893 1256269141469836909015085)
                ·
                  refine ⟨471100928051188840880657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256269141469836909015085 471100928051188840880657)
                  ·
                    rfl

theorem cell20_1032149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_1032149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032149 prefixEnd_1032149 := by exact prefixLift 1032149
  have htrace : WordTrace (prefixWord ++ tailWord_1032149) baseStart_1032149 baseEnd_1032149 := by
    simpa [prefixWord, tailWord_1032149, baseEnd_1032149] using wordTrace_append hprefix tailTrace_1032149
  have hstable : (prefixWord ++ tailWord_1032149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032149).length < 2 ^ (prefixWord ++ tailWord_1032149).sum := by decide
  have hdescent : baseEnd_1032149 < baseStart_1032149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032180 : List Nat := [2, 6, 2, 10]
def baseStart_1032180 : Nat := 118140960795 + 1032180 * 2 ^ 59
def prefixEnd_1032180 : Nat := 4983230072969 + 3 ^ 40 * 1032180 * 2
def baseEnd_1032180 : Nat := 1938745174057162596079

theorem tailTrace_1032180 : CollatzResearch.WordTrace tailWord_1032180 prefixEnd_1032180 1938745174057162596079 := by
  unfold tailWord_1032180
  simp only [CollatzResearch.WordTrace]
  refine ⟨18823348700297808577278997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25097798267063744769705329 18823348700297808577278997)
  ·
    refine ⟨882344470326459777059953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18823348700297808577278997 882344470326459777059953)
    ·
      refine ⟨661758352744844832794965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 882344470326459777059953 661758352744844832794965)
      ·
        refine ⟨1938745174057162596079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 661758352744844832794965 1938745174057162596079)
        ·
          rfl

theorem cell20_1032180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 10].length) (baseStart_1032180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032180 prefixEnd_1032180 := by exact prefixLift 1032180
  have htrace : WordTrace (prefixWord ++ tailWord_1032180) baseStart_1032180 baseEnd_1032180 := by
    simpa [prefixWord, tailWord_1032180, baseEnd_1032180] using wordTrace_append hprefix tailTrace_1032180
  have hstable : (prefixWord ++ tailWord_1032180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032180).length < 2 ^ (prefixWord ++ tailWord_1032180).sum := by decide
  have hdescent : baseEnd_1032180 < baseStart_1032180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032190 : List Nat := [4, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1032190 : Nat := 118140960795 + 1032190 * 2 ^ 59
def prefixEnd_1032190 : Nat := 4983230072969 + 3 ^ 40 * 1032190 * 2
def baseEnd_1032190 : Nat := 471119641568374920513823

theorem tailTrace_1032190 : CollatzResearch.WordTrace tailWord_1032190 prefixEnd_1032190 471119641568374920513823 := by
  unfold tailWord_1032190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4705882766319923607802753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25098041420372925908281349 4705882766319923607802753)
  ·
    refine ⟨3529412074739942705852065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4705882766319923607802753 3529412074739942705852065)
    ·
      refine ⟨2647059056054957029389049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3529412074739942705852065 2647059056054957029389049)
      ·
        refine ⟨1985294292041217772041787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647059056054957029389049 1985294292041217772041787)
        ·
          refine ⟨2977941438061826658062681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985294292041217772041787 2977941438061826658062681)
          ·
            refine ⟨2233456078546369993547011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977941438061826658062681 2233456078546369993547011)
            ·
              refine ⟨3350184117819554990320517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233456078546369993547011 3350184117819554990320517)
              ·
                refine ⟨628159522091166560685097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3350184117819554990320517 628159522091166560685097)
                ·
                  refine ⟨471119641568374920513823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628159522091166560685097 471119641568374920513823)
                  ·
                    rfl

theorem cell20_1032190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1032190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032190 prefixEnd_1032190 := by exact prefixLift 1032190
  have htrace : WordTrace (prefixWord ++ tailWord_1032190) baseStart_1032190 baseEnd_1032190 := by
    simpa [prefixWord, tailWord_1032190, baseEnd_1032190] using wordTrace_append hprefix tailTrace_1032190
  have hstable : (prefixWord ++ tailWord_1032190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032190).length < 2 ^ (prefixWord ++ tailWord_1032190).sum := by decide
  have hdescent : baseEnd_1032190 < baseStart_1032190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032191 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_1032191 : Nat := 118140960795 + 1032191 * 2 ^ 59
def prefixEnd_1032191 : Nat := 4983230072969 + 3 ^ 40 * 1032191 * 2
def baseEnd_1032191 : Nat := 471120097995623361480485

theorem tailTrace_1032191 : CollatzResearch.WordTrace tailWord_1032191 prefixEnd_1032191 471120097995623361480485 := by
  unfold tailWord_1032191
  simp only [CollatzResearch.WordTrace]
  refine ⟨37647098603555766033208427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25098065735703844022138951 37647098603555766033208427)
  ·
    refine ⟨56470647905333649049812641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37647098603555766033208427 56470647905333649049812641)
    ·
      refine ⟨42352985929000236787359481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56470647905333649049812641 42352985929000236787359481)
      ·
        refine ⟨31764739446750177590519611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42352985929000236787359481 31764739446750177590519611)
        ·
          refine ⟨47647109170125266385779417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31764739446750177590519611 47647109170125266385779417)
          ·
            refine ⟨35735331877593949789334563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47647109170125266385779417 35735331877593949789334563)
            ·
              refine ⟨53602997816390924684001845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35735331877593949789334563 53602997816390924684001845)
              ·
                refine ⟨5025281045286649189125173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53602997816390924684001845 5025281045286649189125173)
                ·
                  refine ⟨471120097995623361480485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025281045286649189125173 471120097995623361480485)
                  ·
                    rfl

theorem cell20_1032191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_1032191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032191 prefixEnd_1032191 := by exact prefixLift 1032191
  have htrace : WordTrace (prefixWord ++ tailWord_1032191) baseStart_1032191 baseEnd_1032191 := by
    simpa [prefixWord, tailWord_1032191, baseEnd_1032191] using wordTrace_append hprefix tailTrace_1032191
  have hstable : (prefixWord ++ tailWord_1032191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032191).length < 2 ^ (prefixWord ++ tailWord_1032191).sum := by decide
  have hdescent : baseEnd_1032191 < baseStart_1032191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032228 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 2]
def baseStart_1032228 : Nat := 118140960795 + 1032228 * 2 ^ 59
def prefixEnd_1032228 : Nat := 4983230072969 + 3 ^ 40 * 1032228 * 2
def baseEnd_1032228 : Nat := 471136985803815677247001

theorem tailTrace_1032228 : CollatzResearch.WordTrace tailWord_1032228 prefixEnd_1032228 471136985803815677247001 := by
  unfold tailWord_1032228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18824224052210860676152669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25098965402947814234870225 18824224052210860676152669)
  ·
    refine ⟨7059084019579072753557251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18824224052210860676152669 7059084019579072753557251)
    ·
      refine ⟨10588626029368609130335877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7059084019579072753557251 10588626029368609130335877)
      ·
        refine ⟨1985367380506614211937977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10588626029368609130335877 1985367380506614211937977)
        ·
          refine ⟨1489025535379960658953483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985367380506614211937977 1489025535379960658953483)
          ·
            refine ⟨2233538303069940988430225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489025535379960658953483 2233538303069940988430225)
            ·
              refine ⟨1675153727302455741322669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233538303069940988430225 1675153727302455741322669)
              ·
                refine ⟨628182647738420902996001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1675153727302455741322669 628182647738420902996001)
                ·
                  refine ⟨471136985803815677247001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628182647738420902996001 471136985803815677247001)
                  ·
                    rfl

theorem cell20_1032228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_1032228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032228 prefixEnd_1032228 := by exact prefixLift 1032228
  have htrace : WordTrace (prefixWord ++ tailWord_1032228) baseStart_1032228 baseEnd_1032228 := by
    simpa [prefixWord, tailWord_1032228, baseEnd_1032228] using wordTrace_append hprefix tailTrace_1032228
  have hstable : (prefixWord ++ tailWord_1032228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032228).length < 2 ^ (prefixWord ++ tailWord_1032228).sum := by decide
  have hdescent : baseEnd_1032228 < baseStart_1032228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032263 : List Nat := [1, 1, 4, 1, 3, 1, 5, 1, 3]
def baseStart_1032263 : Nat := 118140960795 + 1032263 * 2 ^ 59
def prefixEnd_1032263 : Nat := 4983230072969 + 3 ^ 40 * 1032263 * 2
def baseEnd_1032263 : Nat := 471152960757511111080191

theorem tailTrace_1032263 : CollatzResearch.WordTrace tailWord_1032263 prefixEnd_1032263 471152960757511111080191 := by
  unfold tailWord_1032263
  simp only [CollatzResearch.WordTrace]
  refine ⟨37649724659294922329829443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25099816439529948219886295 37649724659294922329829443)
  ·
    refine ⟨56474586988942383494744165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37649724659294922329829443 56474586988942383494744165)
    ·
      refine ⟨10588985060426696905264531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56474586988942383494744165 10588985060426696905264531)
      ·
        refine ⟨15883477590640045357896797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10588985060426696905264531 15883477590640045357896797)
        ·
          refine ⟨5956304096490017009211299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15883477590640045357896797 5956304096490017009211299)
          ·
            refine ⟨8934456144735025513816949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5956304096490017009211299 8934456144735025513816949)
            ·
              refine ⟨837605263568908641920339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8934456144735025513816949 837605263568908641920339)
              ·
                refine ⟨1256407895353362962880509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837605263568908641920339 1256407895353362962880509)
                ·
                  refine ⟨471152960757511111080191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256407895353362962880509 471152960757511111080191)
                  ·
                    rfl

theorem cell20_1032263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 5, 1, 3].length) (baseStart_1032263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032263 prefixEnd_1032263 := by exact prefixLift 1032263
  have htrace : WordTrace (prefixWord ++ tailWord_1032263) baseStart_1032263 baseEnd_1032263 := by
    simpa [prefixWord, tailWord_1032263, baseEnd_1032263] using wordTrace_append hprefix tailTrace_1032263
  have hstable : (prefixWord ++ tailWord_1032263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032263).length < 2 ^ (prefixWord ++ tailWord_1032263).sum := by decide
  have hdescent : baseEnd_1032263 < baseStart_1032263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032277 : List Nat := [1, 3, 2, 2, 1, 3, 4, 4]
def baseStart_1032277 : Nat := 118140960795 + 1032277 * 2 ^ 59
def prefixEnd_1032277 : Nat := 4983230072969 + 3 ^ 40 * 1032277 * 2
def baseEnd_1032277 : Nat := 157053116912996428204489

theorem tailTrace_1032277 : CollatzResearch.WordTrace tailWord_1032277 prefixEnd_1032277 157053116912996428204489 := by
  unfold tailWord_1032277
  simp only [CollatzResearch.WordTrace]
  refine ⟨37650235281244202720839085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25100156854162801813892723 37650235281244202720839085)
  ·
    refine ⟨14118838230466576020314657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37650235281244202720839085 14118838230466576020314657)
    ·
      refine ⟨10589128672849932015235993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14118838230466576020314657 10589128672849932015235993)
      ·
        refine ⟨7941846504637449011426995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10589128672849932015235993 7941846504637449011426995)
        ·
          refine ⟨11912769756956173517140493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941846504637449011426995 11912769756956173517140493)
          ·
            refine ⟨4467288658858565068927685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11912769756956173517140493 4467288658858565068927685)
            ·
              refine ⟨837616623535980950423941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4467288658858565068927685 837616623535980950423941)
              ·
                refine ⟨157053116912996428204489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837616623535980950423941 157053116912996428204489)
                ·
                  rfl

theorem cell20_1032277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 4].length) (baseStart_1032277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032277 prefixEnd_1032277 := by exact prefixLift 1032277
  have htrace : WordTrace (prefixWord ++ tailWord_1032277) baseStart_1032277 baseEnd_1032277 := by
    simpa [prefixWord, tailWord_1032277, baseEnd_1032277] using wordTrace_append hprefix tailTrace_1032277
  have hstable : (prefixWord ++ tailWord_1032277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032277).length < 2 ^ (prefixWord ++ tailWord_1032277).sum := by decide
  have hdescent : baseEnd_1032277 < baseStart_1032277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032284 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_1032284 : Nat := 118140960795 + 1032284 * 2 ^ 59
def prefixEnd_1032284 : Nat := 4983230072969 + 3 ^ 40 * 1032284 * 2
def baseEnd_1032284 : Nat := 471162545729728371380105

theorem tailTrace_1032284 : CollatzResearch.WordTrace tailWord_1032284 prefixEnd_1032284 471162545729728371380105 := by
  unfold tailWord_1032284
  simp only [CollatzResearch.WordTrace]
  refine ⟨18825245296109421458171953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25100327061479228610895937 18825245296109421458171953)
  ·
    refine ⟨14118933972082066093628965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18825245296109421458171953 14118933972082066093628965)
    ·
      refine ⟨2647300119765387392555431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14118933972082066093628965 2647300119765387392555431)
      ·
        refine ⟨3970950179648081088833147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647300119765387392555431 3970950179648081088833147)
        ·
          refine ⟨5956425269472121633249721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3970950179648081088833147 5956425269472121633249721)
          ·
            refine ⟨4467318952104091224937291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5956425269472121633249721 4467318952104091224937291)
            ·
              refine ⟨6700978428156136837405937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467318952104091224937291 6700978428156136837405937)
              ·
                refine ⟨5025733821117102628054453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6700978428156136837405937 5025733821117102628054453)
                ·
                  refine ⟨471162545729728371380105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025733821117102628054453 471162545729728371380105)
                  ·
                    rfl

theorem cell20_1032284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_1032284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032284 prefixEnd_1032284 := by exact prefixLift 1032284
  have htrace : WordTrace (prefixWord ++ tailWord_1032284) baseStart_1032284 baseEnd_1032284 := by
    simpa [prefixWord, tailWord_1032284, baseEnd_1032284] using wordTrace_append hprefix tailTrace_1032284
  have hstable : (prefixWord ++ tailWord_1032284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032284).length < 2 ^ (prefixWord ++ tailWord_1032284).sum := by decide
  have hdescent : baseEnd_1032284 < baseStart_1032284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032305 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_1032305 : Nat := 118140960795 + 1032305 * 2 ^ 59
def prefixEnd_1032305 : Nat := 4983230072969 + 3 ^ 40 * 1032305 * 2
def baseEnd_1032305 : Nat := 471172130701945631680019

theorem tailTrace_1032305 : CollatzResearch.WordTrace tailWord_1032305 prefixEnd_1032305 471172130701945631680019 := by
  unfold tailWord_1032305
  simp only [CollatzResearch.WordTrace]
  refine ⟨37651256525142763502858369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25100837683428509001905579 37651256525142763502858369)
  ·
    refine ⟨28238442393857072627143777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37651256525142763502858369 28238442393857072627143777)
    ·
      refine ⟨21178831795392804470357833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28238442393857072627143777 21178831795392804470357833)
      ·
        refine ⟨15884123846544603352768375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21178831795392804470357833 15884123846544603352768375)
        ·
          refine ⟨23826185769816905029152563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15884123846544603352768375 23826185769816905029152563)
          ·
            refine ⟨35739278654725357543728845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23826185769816905029152563 35739278654725357543728845)
            ·
              refine ⟨13402229495522009078898317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35739278654725357543728845 13402229495522009078898317)
              ·
                refine ⟨5025836060820753404586869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13402229495522009078898317 5025836060820753404586869)
                ·
                  refine ⟨471172130701945631680019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025836060820753404586869 471172130701945631680019)
                  ·
                    rfl

theorem cell20_1032305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_1032305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032305 prefixEnd_1032305 := by exact prefixLift 1032305
  have htrace : WordTrace (prefixWord ++ tailWord_1032305) baseStart_1032305 baseEnd_1032305 := by
    simpa [prefixWord, tailWord_1032305, baseEnd_1032305] using wordTrace_append hprefix tailTrace_1032305
  have hstable : (prefixWord ++ tailWord_1032305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032305).length < 2 ^ (prefixWord ++ tailWord_1032305).sum := by decide
  have hdescent : baseEnd_1032305 < baseStart_1032305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032359 : List Nat := [1, 1, 6, 2, 2, 2, 2, 2, 2]
def baseStart_1032359 : Nat := 118140960795 + 1032359 * 2 ^ 59
def prefixEnd_1032359 : Nat := 4983230072969 + 3 ^ 40 * 1032359 * 2
def baseEnd_1032359 : Nat := 471196777773361443879799

theorem tailTrace_1032359 : CollatzResearch.WordTrace tailWord_1032359 prefixEnd_1032359 471196777773361443879799 := by
  unfold tailWord_1032359
  simp only [CollatzResearch.WordTrace]
  refine ⟨37653226066947130725324131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25102150711298087150216087 37653226066947130725324131)
  ·
    refine ⟨56479839100420696087986197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37653226066947130725324131 56479839100420696087986197)
    ·
      refine ⟨2647492457832220129124353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56479839100420696087986197 2647492457832220129124353)
      ·
        refine ⟨1985619343374165096843265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647492457832220129124353 1985619343374165096843265)
        ·
          refine ⟨1489214507530623822632449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985619343374165096843265 1489214507530623822632449)
          ·
            refine ⟨1116910880647967866974337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489214507530623822632449 1116910880647967866974337)
            ·
              refine ⟨837683160485975900230753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1116910880647967866974337 837683160485975900230753)
              ·
                refine ⟨628262370364481925173065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837683160485975900230753 628262370364481925173065)
                ·
                  refine ⟨471196777773361443879799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628262370364481925173065 471196777773361443879799)
                  ·
                    rfl

theorem cell20_1032359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2, 2].length) (baseStart_1032359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032359 prefixEnd_1032359 := by exact prefixLift 1032359
  have htrace : WordTrace (prefixWord ++ tailWord_1032359) baseStart_1032359 baseEnd_1032359 := by
    simpa [prefixWord, tailWord_1032359, baseEnd_1032359] using wordTrace_append hprefix tailTrace_1032359
  have hstable : (prefixWord ++ tailWord_1032359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032359).length < 2 ^ (prefixWord ++ tailWord_1032359).sum := by decide
  have hdescent : baseEnd_1032359 < baseStart_1032359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032366 : List Nat := [4, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1032366 : Nat := 118140960795 + 1032366 * 2 ^ 59
def prefixEnd_1032366 : Nat := 4983230072969 + 3 ^ 40 * 1032366 * 2
def baseEnd_1032366 : Nat := 157066657588033510215479

theorem tailTrace_1032366 : CollatzResearch.WordTrace tailWord_1032366 prefixEnd_1032366 157066657588033510215479 := by
  unfold tailWord_1032366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706685172240221365103619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25102320918614513947219301 4706685172240221365103619)
  ·
    refine ⟨7060027758360332047655429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4706685172240221365103619 7060027758360332047655429)
    ·
      refine ⟨1323755204692562258935393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7060027758360332047655429 1323755204692562258935393)
      ·
        refine ⟨992816403519421694201545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1323755204692562258935393 992816403519421694201545)
        ·
          refine ⟨744612302639566270651159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992816403519421694201545 744612302639566270651159)
          ·
            refine ⟨1116918453959349405976739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744612302639566270651159 1116918453959349405976739)
            ·
              refine ⟨1675377680939024108965109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116918453959349405976739 1675377680939024108965109)
              ·
                refine ⟨157066657588033510215479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1675377680939024108965109 157066657588033510215479)
                ·
                  rfl

theorem cell20_1032366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1032366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032366 prefixEnd_1032366 := by exact prefixLift 1032366
  have htrace : WordTrace (prefixWord ++ tailWord_1032366) baseStart_1032366 baseEnd_1032366 := by
    simpa [prefixWord, tailWord_1032366, baseEnd_1032366] using wordTrace_append hprefix tailTrace_1032366
  have hstable : (prefixWord ++ tailWord_1032366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032366).length < 2 ^ (prefixWord ++ tailWord_1032366).sum := by decide
  have hdescent : baseEnd_1032366 < baseStart_1032366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032381 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1032381 : Nat := 118140960795 + 1032381 * 2 ^ 59
def prefixEnd_1032381 : Nat := 4983230072969 + 3 ^ 40 * 1032381 * 2
def baseEnd_1032381 : Nat := 471206819172827145146375

theorem tailTrace_1032381 : CollatzResearch.WordTrace tailWord_1032381 prefixEnd_1032381 471206819172827145146375 := by
  unfold tailWord_1032381
  simp only [CollatzResearch.WordTrace]
  refine ⟨37654028472867428482624997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25102685648578285655083331 37654028472867428482624997)
  ·
    refine ⟨7060130338662642840492187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37654028472867428482624997 7060130338662642840492187)
    ·
      refine ⟨10590195507993964260738281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7060130338662642840492187 10590195507993964260738281)
      ·
        refine ⟨7942646630995473195553711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10590195507993964260738281 7942646630995473195553711)
        ·
          refine ⟨11913969946493209793330567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7942646630995473195553711 11913969946493209793330567)
          ·
            refine ⟨17870954919739814689995851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11913969946493209793330567 17870954919739814689995851)
            ·
              refine ⟨26806432379609722034993777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17870954919739814689995851 26806432379609722034993777)
              ·
                refine ⟨20104824284707291526245333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26806432379609722034993777 20104824284707291526245333)
                ·
                  refine ⟨471206819172827145146375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20104824284707291526245333 471206819172827145146375)
                  ·
                    rfl

theorem cell20_1032381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1032381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032381 prefixEnd_1032381 := by exact prefixLift 1032381
  have htrace : WordTrace (prefixWord ++ tailWord_1032381) baseStart_1032381 baseEnd_1032381 := by
    simpa [prefixWord, tailWord_1032381, baseEnd_1032381] using wordTrace_append hprefix tailTrace_1032381
  have hstable : (prefixWord ++ tailWord_1032381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032381).length < 2 ^ (prefixWord ++ tailWord_1032381).sum := by decide
  have hdescent : baseEnd_1032381 < baseStart_1032381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032457 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_1032457 : Nat := 118140960795 + 1032457 * 2 ^ 59
def prefixEnd_1032457 : Nat := 4983230072969 + 3 ^ 40 * 1032457 * 2
def baseEnd_1032457 : Nat := 471241507643708658612731

theorem tailTrace_1032457 : CollatzResearch.WordTrace tailWord_1032457 prefixEnd_1032457 471241507643708658612731 := by
  unfold tailWord_1032457
  simp only [CollatzResearch.WordTrace]
  refine ⟨37656800420592093462391625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25104533613728062308261083 37656800420592093462391625)
  ·
    refine ⟨28242600315444070096793719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37656800420592093462391625 28242600315444070096793719)
    ·
      refine ⟨42363900473166105145190579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28242600315444070096793719 42363900473166105145190579)
      ·
        refine ⟨63545850709749157717785869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42363900473166105145190579 63545850709749157717785869)
        ·
          refine ⟨23829694016155934144169701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63545850709749157717785869 23829694016155934144169701)
          ·
            refine ⟨4468067628029237652031819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23829694016155934144169701 4468067628029237652031819)
            ·
              refine ⟨6702101442043856478047729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468067628029237652031819 6702101442043856478047729)
              ·
                refine ⟨5026576081532892358535797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6702101442043856478047729 5026576081532892358535797)
                ·
                  refine ⟨471241507643708658612731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5026576081532892358535797 471241507643708658612731)
                  ·
                    rfl

theorem cell20_1032457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_1032457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032457 prefixEnd_1032457 := by exact prefixLift 1032457
  have htrace : WordTrace (prefixWord ++ tailWord_1032457) baseStart_1032457 baseEnd_1032457 := by
    simpa [prefixWord, tailWord_1032457, baseEnd_1032457] using wordTrace_append hprefix tailTrace_1032457
  have hstable : (prefixWord ++ tailWord_1032457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032457).length < 2 ^ (prefixWord ++ tailWord_1032457).sum := by decide
  have hdescent : baseEnd_1032457 < baseStart_1032457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032477 : List Nat := [1, 4, 2, 3, 2, 2, 1, 1, 4]
def baseStart_1032477 : Nat := 118140960795 + 1032477 * 2 ^ 59
def prefixEnd_1032477 : Nat := 4983230072969 + 3 ^ 40 * 1032477 * 2
def baseEnd_1032477 : Nat := 471250636188677477945983

theorem tailTrace_1032477 : CollatzResearch.WordTrace tailWord_1032477 prefixEnd_1032477 471250636188677477945983 := by
  unfold tailWord_1032477
  simp only [CollatzResearch.WordTrace]
  refine ⟨37657529880519636878119685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25105019920346424585413123 37657529880519636878119685)
  ·
    refine ⟨7060786852597431914647441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37657529880519636878119685 7060786852597431914647441)
    ·
      refine ⟨5295590139448073935985581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7060786852597431914647441 5295590139448073935985581)
      ·
        refine ⟨1985846302293027725994593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5295590139448073935985581 1985846302293027725994593)
        ·
          refine ⟨1489384726719770794495945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1985846302293027725994593 1489384726719770794495945)
          ·
            refine ⟨1117038545039828095871959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1489384726719770794495945 1117038545039828095871959)
            ·
              refine ⟨1675557817559742143807939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117038545039828095871959 1675557817559742143807939)
              ·
                refine ⟨2513336726339613215711909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675557817559742143807939 2513336726339613215711909)
                ·
                  refine ⟨471250636188677477945983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513336726339613215711909 471250636188677477945983)
                  ·
                    rfl

theorem cell20_1032477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_1032477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032477 prefixEnd_1032477 := by exact prefixLift 1032477
  have htrace : WordTrace (prefixWord ++ tailWord_1032477) baseStart_1032477 baseEnd_1032477 := by
    simpa [prefixWord, tailWord_1032477, baseEnd_1032477] using wordTrace_append hprefix tailTrace_1032477
  have hstable : (prefixWord ++ tailWord_1032477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032477).length < 2 ^ (prefixWord ++ tailWord_1032477).sum := by decide
  have hdescent : baseEnd_1032477 < baseStart_1032477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032481 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_1032481 : Nat := 118140960795 + 1032481 * 2 ^ 59
def prefixEnd_1032481 : Nat := 4983230072969 + 3 ^ 40 * 1032481 * 2
def baseEnd_1032481 : Nat := 471252461897671241812633

theorem tailTrace_1032481 : CollatzResearch.WordTrace tailWord_1032481 prefixEnd_1032481 471252461897671241812633 := by
  unfold tailWord_1032481
  simp only [CollatzResearch.WordTrace]
  refine ⟨37657675772505145561265297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25105117181670097040843531 37657675772505145561265297)
  ·
    refine ⟨28243256829378859170948973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37657675772505145561265297 28243256829378859170948973)
    ·
      refine ⟨10591221311017072189105865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28243256829378859170948973 10591221311017072189105865)
      ·
        refine ⟨7943415983262804141829399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10591221311017072189105865 7943415983262804141829399)
        ·
          refine ⟨11915123974894206212744099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943415983262804141829399 11915123974894206212744099)
          ·
            refine ⟨17872685962341309319116149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11915123974894206212744099 17872685962341309319116149)
            ·
              refine ⟨1675564308969497748667139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17872685962341309319116149 1675564308969497748667139)
              ·
                refine ⟨2513346463454246623000709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675564308969497748667139 2513346463454246623000709)
                ·
                  refine ⟨471252461897671241812633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513346463454246623000709 471252461897671241812633)
                  ·
                    rfl

theorem cell20_1032481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_1032481 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032481 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032481 prefixEnd_1032481 := by exact prefixLift 1032481
  have htrace : WordTrace (prefixWord ++ tailWord_1032481) baseStart_1032481 baseEnd_1032481 := by
    simpa [prefixWord, tailWord_1032481, baseEnd_1032481] using wordTrace_append hprefix tailTrace_1032481
  have hstable : (prefixWord ++ tailWord_1032481).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032481).length < 2 ^ (prefixWord ++ tailWord_1032481).sum := by decide
  have hdescent : baseEnd_1032481 < baseStart_1032481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032487 : List Nat := [1, 1, 8, 1, 1, 1, 1, 3, 3]
def baseStart_1032487 : Nat := 118140960795 + 1032487 * 2 ^ 59
def prefixEnd_1032487 : Nat := 4983230072969 + 3 ^ 40 * 1032487 * 2
def baseEnd_1032487 : Nat := 471255200461161887612609

theorem tailTrace_1032487 : CollatzResearch.WordTrace tailWord_1032487 prefixEnd_1032487 471255200461161887612609 := by
  unfold tailWord_1032487
  simp only [CollatzResearch.WordTrace]
  refine ⟨37657894610483408585983715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25105263073655605723989143 37657894610483408585983715)
  ·
    refine ⟨56486841915725112878975573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37657894610483408585983715 56486841915725112878975573)
    ·
      refine ⟨661955178699903666550495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 56486841915725112878975573 661955178699903666550495)
      ·
        refine ⟨992932768049855499825743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661955178699903666550495 992932768049855499825743)
        ·
          refine ⟨1489399152074783249738615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992932768049855499825743 1489399152074783249738615)
          ·
            refine ⟨2234098728112174874607923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489399152074783249738615 2234098728112174874607923)
            ·
              refine ⟨3351148092168262311911885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234098728112174874607923 3351148092168262311911885)
              ·
                refine ⟨1256680534563098366966957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3351148092168262311911885 1256680534563098366966957)
                ·
                  refine ⟨471255200461161887612609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256680534563098366966957 471255200461161887612609)
                  ·
                    rfl

theorem cell20_1032487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 3, 3].length) (baseStart_1032487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032487 prefixEnd_1032487 := by exact prefixLift 1032487
  have htrace : WordTrace (prefixWord ++ tailWord_1032487) baseStart_1032487 baseEnd_1032487 := by
    simpa [prefixWord, tailWord_1032487, baseEnd_1032487] using wordTrace_append hprefix tailTrace_1032487
  have hstable : (prefixWord ++ tailWord_1032487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032487).length < 2 ^ (prefixWord ++ tailWord_1032487).sum := by decide
  have hdescent : baseEnd_1032487 < baseStart_1032487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032532 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1032532 : Nat := 118140960795 + 1032532 * 2 ^ 59
def prefixEnd_1032532 : Nat := 4983230072969 + 3 ^ 40 * 1032532 * 2
def baseEnd_1032532 : Nat := 471275739687341731112425

theorem tailTrace_1032532 : CollatzResearch.WordTrace tailWord_1032532 prefixEnd_1032532 471275739687341731112425 := by
  unfold tailWord_1032532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18829767947660190635685925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25106357263546920847581233 18829767947660190635685925)
  ·
    refine ⟨3530581490186285744191111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18829767947660190635685925 3530581490186285744191111)
    ·
      refine ⟨5295872235279428616286667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3530581490186285744191111 5295872235279428616286667)
      ·
        refine ⟨7943808352919142924430001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295872235279428616286667 7943808352919142924430001)
        ·
          refine ⟨5957856264689357193322501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7943808352919142924430001 5957856264689357193322501)
          ·
            refine ⟨1117098049629254473747969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5957856264689357193322501 1117098049629254473747969)
            ·
              refine ⟨837823537221940855310977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117098049629254473747969 837823537221940855310977)
              ·
                refine ⟨628367652916455641483233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837823537221940855310977 628367652916455641483233)
                ·
                  refine ⟨471275739687341731112425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628367652916455641483233 471275739687341731112425)
                  ·
                    rfl

theorem cell20_1032532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1032532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032532 prefixEnd_1032532 := by exact prefixLift 1032532
  have htrace : WordTrace (prefixWord ++ tailWord_1032532) baseStart_1032532 baseEnd_1032532 := by
    simpa [prefixWord, tailWord_1032532, baseEnd_1032532] using wordTrace_append hprefix tailTrace_1032532
  have hstable : (prefixWord ++ tailWord_1032532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032532).length < 2 ^ (prefixWord ++ tailWord_1032532).sum := by decide
  have hdescent : baseEnd_1032532 < baseStart_1032532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032557 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1032557 : Nat := 118140960795 + 1032557 * 2 ^ 59
def prefixEnd_1032557 : Nat := 4983230072969 + 3 ^ 40 * 1032557 * 2
def baseEnd_1032557 : Nat := 471287150368552755278989

theorem tailTrace_1032557 : CollatzResearch.WordTrace tailWord_1032557 prefixEnd_1032557 471287150368552755278989 := by
  unfold tailWord_1032557
  simp only [CollatzResearch.WordTrace]
  refine ⟨37660447720229810541031925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25106965146819873694021283 37660447720229810541031925)
  ·
    refine ⟨3530666973771544738221743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37660447720229810541031925 3530666973771544738221743)
    ·
      refine ⟨5296000460657317107332615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3530666973771544738221743 5296000460657317107332615)
      ·
        refine ⟨7944000690985975660998923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296000460657317107332615 7944000690985975660998923)
        ·
          refine ⟨11916001036478963491498385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7944000690985975660998923 11916001036478963491498385)
          ·
            refine ⟨8937000777359222618623789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11916001036478963491498385 8937000777359222618623789)
            ·
              refine ⟨3351375291509708481983921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8937000777359222618623789 3351375291509708481983921)
              ·
                refine ⟨2513531468632281361487941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351375291509708481983921 2513531468632281361487941)
                ·
                  refine ⟨471287150368552755278989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513531468632281361487941 471287150368552755278989)
                  ·
                    rfl

theorem cell20_1032557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1032557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032557 prefixEnd_1032557 := by exact prefixLift 1032557
  have htrace : WordTrace (prefixWord ++ tailWord_1032557) baseStart_1032557 baseEnd_1032557 := by
    simpa [prefixWord, tailWord_1032557, baseEnd_1032557] using wordTrace_append hprefix tailTrace_1032557
  have hstable : (prefixWord ++ tailWord_1032557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032557).length < 2 ^ (prefixWord ++ tailWord_1032557).sum := by decide
  have hdescent : baseEnd_1032557 < baseStart_1032557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032588 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_1032588 : Nat := 118140960795 + 1032588 * 2 ^ 59
def prefixEnd_1032588 : Nat := 4983230072969 + 3 ^ 40 * 1032588 * 2
def baseEnd_1032588 : Nat := 471301299613254425245529

theorem tailTrace_1032588 : CollatzResearch.WordTrace tailWord_1032588 prefixEnd_1032588 471301299613254425245529 := by
  unfold tailWord_1032588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18830789191558751417705209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25107718922078335223606945 18830789191558751417705209)
  ·
    refine ⟨14123091893669063563278907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18830789191558751417705209 14123091893669063563278907)
    ·
      refine ⟨21184637840503595344918361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14123091893669063563278907 21184637840503595344918361)
      ·
        refine ⟨15888478380377696508688771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21184637840503595344918361 15888478380377696508688771)
        ·
          refine ⟨23832717570566544763033157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15888478380377696508688771 23832717570566544763033157)
          ·
            refine ⟨4468634544481227143068717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23832717570566544763033157 4468634544481227143068717)
            ·
              refine ⟨1675737954180460178650769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4468634544481227143068717 1675737954180460178650769)
              ·
                refine ⟨1256803465635345133988077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675737954180460178650769 1256803465635345133988077)
                ·
                  refine ⟨471301299613254425245529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256803465635345133988077 471301299613254425245529)
                  ·
                    rfl

theorem cell20_1032588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_1032588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032588 prefixEnd_1032588 := by exact prefixLift 1032588
  have htrace : WordTrace (prefixWord ++ tailWord_1032588) baseStart_1032588 baseEnd_1032588 := by
    simpa [prefixWord, tailWord_1032588, baseEnd_1032588] using wordTrace_append hprefix tailTrace_1032588
  have hstable : (prefixWord ++ tailWord_1032588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032588).length < 2 ^ (prefixWord ++ tailWord_1032588).sum := by decide
  have hdescent : baseEnd_1032588 < baseStart_1032588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032647 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_1032647 : Nat := 118140960795 + 1032647 * 2 ^ 59
def prefixEnd_1032647 : Nat := 4983230072969 + 3 ^ 40 * 1032647 * 2
def baseEnd_1032647 : Nat := 471328228820912442278621

theorem tailTrace_1032647 : CollatzResearch.WordTrace tailWord_1032647 prefixEnd_1032647 471328228820912442278621 := by
  unfold tailWord_1032647
  simp only [CollatzResearch.WordTrace]
  refine ⟨37663730289903755911808195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25109153526602503941205463 37663730289903755911808195)
  ·
    refine ⟨56495595434855633867712293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37663730289903755911808195 56495595434855633867712293)
    ·
      refine ⟨10592924144035431350196055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56495595434855633867712293 10592924144035431350196055)
      ·
        refine ⟨15889386216053147025294083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10592924144035431350196055 15889386216053147025294083)
        ·
          refine ⟨23834079324079720537941125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15889386216053147025294083 23834079324079720537941125)
          ·
            refine ⟨4468889873264947600863961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23834079324079720537941125 4468889873264947600863961)
            ·
              refine ⟨3351667404948710700647971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4468889873264947600863961 3351667404948710700647971)
              ·
                refine ⟨5027501107423066050971957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3351667404948710700647971 5027501107423066050971957)
                ·
                  refine ⟨471328228820912442278621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5027501107423066050971957 471328228820912442278621)
                  ·
                    rfl

theorem cell20_1032647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_1032647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032647 prefixEnd_1032647 := by exact prefixLift 1032647
  have htrace : WordTrace (prefixWord ++ tailWord_1032647) baseStart_1032647 baseEnd_1032647 := by
    simpa [prefixWord, tailWord_1032647, baseEnd_1032647] using wordTrace_append hprefix tailTrace_1032647
  have hstable : (prefixWord ++ tailWord_1032647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032647).length < 2 ^ (prefixWord ++ tailWord_1032647).sum := by decide
  have hdescent : baseEnd_1032647 < baseStart_1032647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032660 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1032660 : Nat := 118140960795 + 1032660 * 2 ^ 59
def prefixEnd_1032660 : Nat := 4983230072969 + 3 ^ 40 * 1032660 * 2
def baseEnd_1032660 : Nat := 471334162375142174845235

theorem tailTrace_1032660 : CollatzResearch.WordTrace tailWord_1032660 prefixEnd_1032660 471334162375142174845235 := by
  unfold tailWord_1032660
  simp only [CollatzResearch.WordTrace]
  refine ⟨18832102219428329566015717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25109469625904439421354289 18832102219428329566015717)
  ·
    refine ⟨3531019166142811793627947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18832102219428329566015717 3531019166142811793627947)
    ·
      refine ⟨5296528749214217690441921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3531019166142811793627947 5296528749214217690441921)
      ·
        refine ⟨3972396561910663267831441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5296528749214217690441921 3972396561910663267831441)
        ·
          refine ⟨2979297421432997450873581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972396561910663267831441 2979297421432997450873581)
          ·
            refine ⟨1117236533037374044077593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2979297421432997450873581 1117236533037374044077593)
            ·
              refine ⟨837927399778030533058195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117236533037374044077593 837927399778030533058195)
              ·
                refine ⟨1256891099667045799587293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837927399778030533058195 1256891099667045799587293)
                ·
                  refine ⟨471334162375142174845235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256891099667045799587293 471334162375142174845235)
                  ·
                    rfl

theorem cell20_1032660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1032660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032660 prefixEnd_1032660 := by exact prefixLift 1032660
  have htrace : WordTrace (prefixWord ++ tailWord_1032660) baseStart_1032660 baseEnd_1032660 := by
    simpa [prefixWord, tailWord_1032660, baseEnd_1032660] using wordTrace_append hprefix tailTrace_1032660
  have hstable : (prefixWord ++ tailWord_1032660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032660).length < 2 ^ (prefixWord ++ tailWord_1032660).sum := by decide
  have hdescent : baseEnd_1032660 < baseStart_1032660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032705 : List Nat := [1, 2, 4, 1, 3, 1, 4, 2, 2]
def baseStart_1032705 : Nat := 118140960795 + 1032705 * 2 ^ 59
def prefixEnd_1032705 : Nat := 4983230072969 + 3 ^ 40 * 1032705 * 2
def baseEnd_1032705 : Nat := 471354701601322018345051

theorem tailTrace_1032705 : CollatzResearch.WordTrace tailWord_1032705 prefixEnd_1032705 471354701601322018345051 := by
  unfold tailWord_1032705
  simp only [CollatzResearch.WordTrace]
  refine ⟨37665845723693631817419569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25110563815795754544946379 37665845723693631817419569)
  ·
    refine ⟨28249384292770223863064677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37665845723693631817419569 28249384292770223863064677)
    ·
      refine ⟨5296759554894416974324627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28249384292770223863064677 5296759554894416974324627)
      ·
        refine ⟨7945139332341625461486941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5296759554894416974324627 7945139332341625461486941)
        ·
          refine ⟨2979427249628109548057603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7945139332341625461486941 2979427249628109548057603)
          ·
            refine ⟨4469140874442164322086405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979427249628109548057603 4469140874442164322086405)
            ·
              refine ⟨837963913957905810391201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4469140874442164322086405 837963913957905810391201)
              ·
                refine ⟨628472935468429357793401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837963913957905810391201 628472935468429357793401)
                ·
                  refine ⟨471354701601322018345051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628472935468429357793401 471354701601322018345051)
                  ·
                    rfl

theorem cell20_1032705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_1032705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032705 prefixEnd_1032705 := by exact prefixLift 1032705
  have htrace : WordTrace (prefixWord ++ tailWord_1032705) baseStart_1032705 baseEnd_1032705 := by
    simpa [prefixWord, tailWord_1032705, baseEnd_1032705] using wordTrace_append hprefix tailTrace_1032705
  have hstable : (prefixWord ++ tailWord_1032705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032705).length < 2 ^ (prefixWord ++ tailWord_1032705).sum := by decide
  have hdescent : baseEnd_1032705 < baseStart_1032705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032716 : List Nat := [2, 2, 1, 2, 4, 1, 3, 5]
def baseStart_1032716 : Nat := 118140960795 + 1032716 * 2 ^ 59
def prefixEnd_1032716 : Nat := 4983230072969 + 3 ^ 40 * 1032716 * 2
def baseEnd_1032716 : Nat := 157119907433684956326113

theorem tailTrace_1032716 : CollatzResearch.WordTrace tailWord_1032716 prefixEnd_1032716 157119907433684956326113 := by
  unfold tailWord_1032716
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833123463326890348035001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25110831284435853797380001 18833123463326890348035001)
  ·
    refine ⟨14124842597495167761026251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18833123463326890348035001 14124842597495167761026251)
    ·
      refine ⟨21187263896242751641539377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14124842597495167761026251 21187263896242751641539377)
      ·
        refine ⟨15890447922182063731154533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21187263896242751641539377 15890447922182063731154533)
        ·
          refine ⟨2979458985409136949591475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15890447922182063731154533 2979458985409136949591475)
          ·
            refine ⟨4469188478113705424387213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979458985409136949591475 4469188478113705424387213)
            ·
              refine ⟨1675945679292639534145205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4469188478113705424387213 1675945679292639534145205)
              ·
                refine ⟨157119907433684956326113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1675945679292639534145205 157119907433684956326113)
                ·
                  rfl

theorem cell20_1032716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_1032716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032716 prefixEnd_1032716 := by exact prefixLift 1032716
  have htrace : WordTrace (prefixWord ++ tailWord_1032716) baseStart_1032716 baseEnd_1032716 := by
    simpa [prefixWord, tailWord_1032716, baseEnd_1032716] using wordTrace_append hprefix tailTrace_1032716
  have hstable : (prefixWord ++ tailWord_1032716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032716).length < 2 ^ (prefixWord ++ tailWord_1032716).sum := by decide
  have hdescent : baseEnd_1032716 < baseStart_1032716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032723 : List Nat := [1, 1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_1032723 : Nat := 118140960795 + 1032723 * 2 ^ 59
def prefixEnd_1032723 : Nat := 4983230072969 + 3 ^ 40 * 1032723 * 2
def baseEnd_1032723 : Nat := 471362917291793955744977

theorem tailTrace_1032723 : CollatzResearch.WordTrace tailWord_1032723 prefixEnd_1032723 471362917291793955744977 := by
  unfold tailWord_1032723
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666502237628420891574823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25111001491752280594383215 37666502237628420891574823)
  ·
    refine ⟨56499753356442631337362235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37666502237628420891574823 56499753356442631337362235)
    ·
      refine ⟨84749630034663947006043353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56499753356442631337362235 84749630034663947006043353)
      ·
        refine ⟨63562222525997960254532515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84749630034663947006043353 63562222525997960254532515)
        ·
          refine ⟨95343333788996940381798773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63562222525997960254532515 95343333788996940381798773)
          ·
            refine ⟨8938437542718463160793635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95343333788996940381798773 8938437542718463160793635)
            ·
              refine ⟨13407656314077694741190453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8938437542718463160793635 13407656314077694741190453)
              ·
                refine ⟨1256967779444783881986605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13407656314077694741190453 1256967779444783881986605)
                ·
                  refine ⟨471362917291793955744977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256967779444783881986605 471362917291793955744977)
                  ·
                    rfl

theorem cell20_1032723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_1032723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032723 prefixEnd_1032723 := by exact prefixLift 1032723
  have htrace : WordTrace (prefixWord ++ tailWord_1032723) baseStart_1032723 baseEnd_1032723 := by
    simpa [prefixWord, tailWord_1032723, baseEnd_1032723] using wordTrace_append hprefix tailTrace_1032723
  have hstable : (prefixWord ++ tailWord_1032723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032723).length < 2 ^ (prefixWord ++ tailWord_1032723).sum := by decide
  have hdescent : baseEnd_1032723 < baseStart_1032723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032730 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_1032730 : Nat := 118140960795 + 1032730 * 2 ^ 59
def prefixEnd_1032730 : Nat := 4983230072969 + 3 ^ 40 * 1032730 * 2
def baseEnd_1032730 : Nat := 471366112282533042511615

theorem tailTrace_1032730 : CollatzResearch.WordTrace tailWord_1032730 prefixEnd_1032730 471366112282533042511615 := by
  unfold tailWord_1032730
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416689387150765271769911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25111171699068707391386429 9416689387150765271769911)
  ·
    refine ⟨14125034080726147907654867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9416689387150765271769911 14125034080726147907654867)
    ·
      refine ⟨21187551121089221861482301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14125034080726147907654867 21187551121089221861482301)
      ·
        refine ⟨7945331670408458198055863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21187551121089221861482301 7945331670408458198055863)
        ·
          refine ⟨11917997505612687297083795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7945331670408458198055863 11917997505612687297083795)
          ·
            refine ⟨17876996258419030945625693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11917997505612687297083795 17876996258419030945625693)
            ·
              refine ⟨6703873596907136604609635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17876996258419030945625693 6703873596907136604609635)
              ·
                refine ⟨10055810395360704906914453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703873596907136604609635 10055810395360704906914453)
                ·
                  refine ⟨471366112282533042511615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10055810395360704906914453 471366112282533042511615)
                  ·
                    rfl

theorem cell20_1032730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_1032730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032730 prefixEnd_1032730 := by exact prefixLift 1032730
  have htrace : WordTrace (prefixWord ++ tailWord_1032730) baseStart_1032730 baseEnd_1032730 := by
    simpa [prefixWord, tailWord_1032730, baseEnd_1032730] using wordTrace_append hprefix tailTrace_1032730
  have hstable : (prefixWord ++ tailWord_1032730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032730).length < 2 ^ (prefixWord ++ tailWord_1032730).sum := by decide
  have hdescent : baseEnd_1032730 < baseStart_1032730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032733 : List Nat := [1, 4, 2, 2, 1, 3, 3, 4]
def baseStart_1032733 : Nat := 118140960795 + 1032733 * 2 ^ 59
def prefixEnd_1032733 : Nat := 4983230072969 + 3 ^ 40 * 1032733 * 2
def baseEnd_1032733 : Nat := 157122493854759455137201

theorem tailTrace_1032733 : CollatzResearch.WordTrace tailWord_1032733 prefixEnd_1032733 157122493854759455137201 := by
  unfold tailWord_1032733
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666866967592192599438853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25111244645061461732959235 37666866967592192599438853)
  ·
    refine ⟨7062537556423536112394785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37666866967592192599438853 7062537556423536112394785)
    ·
      refine ⟨5296903167317652084296089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7062537556423536112394785 5296903167317652084296089)
      ·
        refine ⟨3972677375488239063222067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5296903167317652084296089 3972677375488239063222067)
        ·
          refine ⟨5959016063232358594833101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972677375488239063222067 5959016063232358594833101)
          ·
            refine ⟨2234631023712134473062413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5959016063232358594833101 2234631023712134473062413)
            ·
              refine ⟨837986633892050427398405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2234631023712134473062413 837986633892050427398405)
              ·
                refine ⟨157122493854759455137201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 837986633892050427398405 157122493854759455137201)
                ·
                  rfl

theorem cell20_1032733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 4].length) (baseStart_1032733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032733 prefixEnd_1032733 := by exact prefixLift 1032733
  have htrace : WordTrace (prefixWord ++ tailWord_1032733) baseStart_1032733 baseEnd_1032733 := by
    simpa [prefixWord, tailWord_1032733, baseEnd_1032733] using wordTrace_append hprefix tailTrace_1032733
  have hstable : (prefixWord ++ tailWord_1032733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032733).length < 2 ^ (prefixWord ++ tailWord_1032733).sum := by decide
  have hdescent : baseEnd_1032733 < baseStart_1032733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032761 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_1032761 : Nat := 118140960795 + 1032761 * 2 ^ 59
def prefixEnd_1032761 : Nat := 4983230072969 + 3 ^ 40 * 1032761 * 2
def baseEnd_1032761 : Nat := 471380261527234712478155

theorem tailTrace_1032761 : CollatzResearch.WordTrace tailWord_1032761 prefixEnd_1032761 471380261527234712478155 := by
  unfold tailWord_1032761
  simp only [CollatzResearch.WordTrace]
  refine ⟨37667888211490753381458137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25111925474327168920972091 37667888211490753381458137)
  ·
    refine ⟨28250916158618065036093603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37667888211490753381458137 28250916158618065036093603)
    ·
      refine ⟨42376374237927097554140405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28250916158618065036093603 42376374237927097554140405)
      ·
        refine ⟨3972785084805665395700663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42376374237927097554140405 3972785084805665395700663)
        ·
          refine ⟨5959177627208498093550995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972785084805665395700663 5959177627208498093550995)
          ·
            refine ⟨8938766440812747140326493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5959177627208498093550995 8938766440812747140326493)
            ·
              refine ⟨3352037415304780177622435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8938766440812747140326493 3352037415304780177622435)
              ·
                refine ⟨5028056122957170266433653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352037415304780177622435 5028056122957170266433653)
                ·
                  refine ⟨471380261527234712478155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5028056122957170266433653 471380261527234712478155)
                  ·
                    rfl

theorem cell20_1032761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_1032761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032761 prefixEnd_1032761 := by exact prefixLift 1032761
  have htrace : WordTrace (prefixWord ++ tailWord_1032761) baseStart_1032761 baseEnd_1032761 := by
    simpa [prefixWord, tailWord_1032761, baseEnd_1032761] using wordTrace_append hprefix tailTrace_1032761
  have hstable : (prefixWord ++ tailWord_1032761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032761).length < 2 ^ (prefixWord ++ tailWord_1032761).sum := by decide
  have hdescent : baseEnd_1032761 < baseStart_1032761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032764 : List Nat := [2, 2, 2, 2, 3, 1, 2, 4, 2]
def baseStart_1032764 : Nat := 118140960795 + 1032764 * 2 ^ 59
def prefixEnd_1032764 : Nat := 4983230072969 + 3 ^ 40 * 1032764 * 2
def baseEnd_1032764 : Nat := 471381630808980035378143

theorem tailTrace_1032764 : CollatzResearch.WordTrace tailWord_1032764 prefixEnd_1032764 471381630808980035378143 := by
  unfold tailWord_1032764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833998815239942446908673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25111998420319923262544897 18833998815239942446908673)
  ·
    refine ⟨14125499111429956835181505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18833998815239942446908673 14125499111429956835181505)
    ·
      refine ⟨10594124333572467626386129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14125499111429956835181505 10594124333572467626386129)
      ·
        refine ⟨7945593250179350719789597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10594124333572467626386129 7945593250179350719789597)
        ·
          refine ⟨2979597468817256519921099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7945593250179350719789597 2979597468817256519921099)
          ·
            refine ⟨4469396203225884779881649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979597468817256519921099 4469396203225884779881649)
            ·
              refine ⟨3352047152419413584911237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4469396203225884779881649 3352047152419413584911237)
              ·
                refine ⟨628508841078640047170857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3352047152419413584911237 628508841078640047170857)
                ·
                  refine ⟨471381630808980035378143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628508841078640047170857 471381630808980035378143)
                  ·
                    rfl

theorem cell20_1032764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_1032764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032764 prefixEnd_1032764 := by exact prefixLift 1032764
  have htrace : WordTrace (prefixWord ++ tailWord_1032764) baseStart_1032764 baseEnd_1032764 := by
    simpa [prefixWord, tailWord_1032764, baseEnd_1032764] using wordTrace_append hprefix tailTrace_1032764
  have hstable : (prefixWord ++ tailWord_1032764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032764).length < 2 ^ (prefixWord ++ tailWord_1032764).sum := by decide
  have hdescent : baseEnd_1032764 < baseStart_1032764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032768 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_1032768 : Nat := 118140960795 + 1032768 * 2 ^ 59
def prefixEnd_1032768 : Nat := 4983230072969 + 3 ^ 40 * 1032768 * 2
def baseEnd_1032768 : Nat := 471383456517973799244793

theorem tailTrace_1032768 : CollatzResearch.WordTrace tailWord_1032768 prefixEnd_1032768 471383456517973799244793 := by
  unfold tailWord_1032768
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834071761232696788481479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25112095681643595717975305 18834071761232696788481479)
  ·
    refine ⟨28251107641849045182722219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18834071761232696788481479 28251107641849045182722219)
    ·
      refine ⟨42376661462773567774083329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28251107641849045182722219 42376661462773567774083329)
      ·
        refine ⟨31782496097080175830562497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42376661462773567774083329 31782496097080175830562497)
        ·
          refine ⟨23836872072810131872921873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31782496097080175830562497 23836872072810131872921873)
          ·
            refine ⟨17877654054607598904691405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23836872072810131872921873 17877654054607598904691405)
            ·
              refine ⟨6704120270477849589259277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17877654054607598904691405 6704120270477849589259277)
              ·
                refine ⟨2514045101429193595972229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6704120270477849589259277 2514045101429193595972229)
                ·
                  refine ⟨471383456517973799244793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2514045101429193595972229 471383456517973799244793)
                  ·
                    rfl

theorem cell20_1032768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_1032768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032768 prefixEnd_1032768 := by exact prefixLift 1032768
  have htrace : WordTrace (prefixWord ++ tailWord_1032768) baseStart_1032768 baseEnd_1032768 := by
    simpa [prefixWord, tailWord_1032768, baseEnd_1032768] using wordTrace_append hprefix tailTrace_1032768
  have hstable : (prefixWord ++ tailWord_1032768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032768).length < 2 ^ (prefixWord ++ tailWord_1032768).sum := by decide
  have hdescent : baseEnd_1032768 < baseStart_1032768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032792 : List Nat := [2, 1, 2, 2, 1, 2, 6, 4]
def baseStart_1032792 : Nat := 118140960795 + 1032792 * 2 ^ 59
def prefixEnd_1032792 : Nat := 4983230072969 + 3 ^ 40 * 1032792 * 2
def baseEnd_1032792 : Nat := 157131470257312127481565

theorem tailTrace_1032792 : CollatzResearch.WordTrace tailWord_1032792 prefixEnd_1032792 157131470257312127481565 := by
  unfold tailWord_1032792
  simp only [CollatzResearch.WordTrace]
  refine ⟨18834509437189222837918315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25112679249585630450557753 18834509437189222837918315)
  ·
    refine ⟨28251764155783834256877473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18834509437189222837918315 28251764155783834256877473)
    ·
      refine ⟨21188823116837875692658105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28251764155783834256877473 21188823116837875692658105)
      ·
        refine ⟨15891617337628406769493579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21188823116837875692658105 15891617337628406769493579)
        ·
          refine ⟨23837426006442610154240369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15891617337628406769493579 23837426006442610154240369)
          ·
            refine ⟨17878069504831957615680277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23837426006442610154240369 17878069504831957615680277)
            ·
              refine ⟨838034508038998013235013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17878069504831957615680277 838034508038998013235013)
              ·
                refine ⟨157131470257312127481565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838034508038998013235013 157131470257312127481565)
                ·
                  rfl

theorem cell20_1032792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_1032792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032792 prefixEnd_1032792 := by exact prefixLift 1032792
  have htrace : WordTrace (prefixWord ++ tailWord_1032792) baseStart_1032792 baseEnd_1032792 := by
    simpa [prefixWord, tailWord_1032792, baseEnd_1032792] using wordTrace_append hprefix tailTrace_1032792
  have hstable : (prefixWord ++ tailWord_1032792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032792).length < 2 ^ (prefixWord ++ tailWord_1032792).sum := by decide
  have hdescent : baseEnd_1032792 < baseStart_1032792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032823 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 2]
def baseStart_1032823 : Nat := 118140960795 + 1032823 * 2 ^ 59
def prefixEnd_1032823 : Nat := 4983230072969 + 3 ^ 40 * 1032823 * 2
def baseEnd_1032823 : Nat := 471408560016638052411235

theorem tailTrace_1032823 : CollatzResearch.WordTrace tailWord_1032823 prefixEnd_1032823 471408560016638052411235 := by
  unfold tailWord_1032823
  simp only [CollatzResearch.WordTrace]
  refine ⟨37670149537266137970215123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25113433024844091980143415 37670149537266137970215123)
  ·
    refine ⟨56505224305899206955322685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37670149537266137970215123 56505224305899206955322685)
    ·
      refine ⟨21189459114712202608246007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56505224305899206955322685 21189459114712202608246007)
      ·
        refine ⟨31784188672068303912369011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21189459114712202608246007 31784188672068303912369011)
        ·
          refine ⟨47676283008102455868553517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31784188672068303912369011 47676283008102455868553517)
          ·
            refine ⟨17878606128038420950707569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47676283008102455868553517 17878606128038420950707569)
            ·
              refine ⟨13408954596028815713030677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17878606128038420950707569 13408954596028815713030677)
              ·
                refine ⟨628544746688850736548313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13408954596028815713030677 628544746688850736548313)
                ·
                  refine ⟨471408560016638052411235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628544746688850736548313 471408560016638052411235)
                  ·
                    rfl

theorem cell20_1032823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 2].length) (baseStart_1032823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032823 prefixEnd_1032823 := by exact prefixLift 1032823
  have htrace : WordTrace (prefixWord ++ tailWord_1032823) baseStart_1032823 baseEnd_1032823 := by
    simpa [prefixWord, tailWord_1032823, baseEnd_1032823] using wordTrace_append hprefix tailTrace_1032823
  have hstable : (prefixWord ++ tailWord_1032823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032823).length < 2 ^ (prefixWord ++ tailWord_1032823).sum := by decide
  have hdescent : baseEnd_1032823 < baseStart_1032823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032874 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_1032874 : Nat := 118140960795 + 1032874 * 2 ^ 59
def prefixEnd_1032874 : Nat := 4983230072969 + 3 ^ 40 * 1032874 * 2
def baseEnd_1032874 : Nat := 471431837806308541711027

theorem tailTrace_1032874 : CollatzResearch.WordTrace tailWord_1032874 prefixEnd_1032874 471431837806308541711027 := by
  unfold tailWord_1032874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418002415020343420080419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25114673106720915786881117 9418002415020343420080419)
  ·
    refine ⟨14127003622530515130120629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9418002415020343420080419 14127003622530515130120629)
    ·
      refine ⟨1324406589612235793448809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14127003622530515130120629 1324406589612235793448809)
      ·
        refine ⟨993304942209176845086607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1324406589612235793448809 993304942209176845086607)
        ·
          refine ⟨1489957413313765267629911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993304942209176845086607 1489957413313765267629911)
          ·
            refine ⟨2234936119970647901444867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489957413313765267629911 2234936119970647901444867)
            ·
              refine ⟨3352404179955971852167301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234936119970647901444867 3352404179955971852167301)
              ·
                refine ⟨628575783741744722281369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3352404179955971852167301 628575783741744722281369)
                ·
                  refine ⟨471431837806308541711027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628575783741744722281369 471431837806308541711027)
                  ·
                    rfl

theorem cell20_1032874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_1032874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032874 prefixEnd_1032874 := by exact prefixLift 1032874
  have htrace : WordTrace (prefixWord ++ tailWord_1032874) baseStart_1032874 baseEnd_1032874 := by
    simpa [prefixWord, tailWord_1032874, baseEnd_1032874] using wordTrace_append hprefix tailTrace_1032874
  have hstable : (prefixWord ++ tailWord_1032874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032874).length < 2 ^ (prefixWord ++ tailWord_1032874).sum := by decide
  have hdescent : baseEnd_1032874 < baseStart_1032874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032882 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_1032882 : Nat := 118140960795 + 1032882 * 2 ^ 59
def prefixEnd_1032882 : Nat := 4983230072969 + 3 ^ 40 * 1032882 * 2
def baseEnd_1032882 : Nat := 471435489224296069444327

theorem tailTrace_1032882 : CollatzResearch.WordTrace tailWord_1032882 prefixEnd_1032882 471435489224296069444327 := by
  unfold tailWord_1032882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418075361013097761653225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25114867629368260697741933 9418075361013097761653225)
  ·
    refine ⟨7063556520759823321239919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9418075361013097761653225 7063556520759823321239919)
    ·
      refine ⟨10595334781139734981859879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7063556520759823321239919 10595334781139734981859879)
      ·
        refine ⟨15893002171709602472789819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10595334781139734981859879 15893002171709602472789819)
        ·
          refine ⟨23839503257564403709184729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15893002171709602472789819 23839503257564403709184729)
          ·
            refine ⟨17879627443173302781888547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23839503257564403709184729 17879627443173302781888547)
            ·
              refine ⟨26819441164759954172832821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17879627443173302781888547 26819441164759954172832821)
              ·
                refine ⟨2514322609196245703703077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26819441164759954172832821 2514322609196245703703077)
                ·
                  refine ⟨471435489224296069444327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2514322609196245703703077 471435489224296069444327)
                  ·
                    rfl

theorem cell20_1032882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_1032882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032882 prefixEnd_1032882 := by exact prefixLift 1032882
  have htrace : WordTrace (prefixWord ++ tailWord_1032882) baseStart_1032882 baseEnd_1032882 := by
    simpa [prefixWord, tailWord_1032882, baseEnd_1032882] using wordTrace_append hprefix tailTrace_1032882
  have hstable : (prefixWord ++ tailWord_1032882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032882).length < 2 ^ (prefixWord ++ tailWord_1032882).sum := by decide
  have hdescent : baseEnd_1032882 < baseStart_1032882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032885 : List Nat := [1, 3, 3, 3, 1, 3, 1, 5]
def baseStart_1032885 : Nat := 118140960795 + 1032885 * 2 ^ 59
def prefixEnd_1032885 : Nat := 4983230072969 + 3 ^ 40 * 1032885 * 2
def baseEnd_1032885 : Nat := 157145619502013797448105

theorem tailTrace_1032885 : CollatzResearch.WordTrace tailWord_1032885 prefixEnd_1032885 157145619502013797448105 := by
  unfold tailWord_1032885
  simp only [CollatzResearch.WordTrace]
  refine ⟨37672410863041522558972109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25114940575361015039314739 37672410863041522558972109)
  ·
    refine ⟨14127154073640570959614541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37672410863041522558972109 14127154073640570959614541)
    ·
      refine ⟨5297682777615214109855453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14127154073640570959614541 5297682777615214109855453)
      ·
        refine ⟨1986631041605705291195795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5297682777615214109855453 1986631041605705291195795)
        ·
          refine ⟨2979946562408557936793693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986631041605705291195795 2979946562408557936793693)
          ·
            refine ⟨1117479960903209226297635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2979946562408557936793693 1117479960903209226297635)
            ·
              refine ⟨1676219941354813839446453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117479960903209226297635 1676219941354813839446453)
              ·
                refine ⟨157145619502013797448105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1676219941354813839446453 157145619502013797448105)
                ·
                  rfl

theorem cell20_1032885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_1032885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032885 prefixEnd_1032885 := by exact prefixLift 1032885
  have htrace : WordTrace (prefixWord ++ tailWord_1032885) baseStart_1032885 baseEnd_1032885 := by
    simpa [prefixWord, tailWord_1032885, baseEnd_1032885] using wordTrace_append hprefix tailTrace_1032885
  have hstable : (prefixWord ++ tailWord_1032885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032885).length < 2 ^ (prefixWord ++ tailWord_1032885).sum := by decide
  have hdescent : baseEnd_1032885 < baseStart_1032885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032927 : List Nat := [1, 1, 2, 3, 2, 4, 7]
def baseStart_1032927 : Nat := 118140960795 + 1032927 * 2 ^ 59
def prefixEnd_1032927 : Nat := 4983230072969 + 3 ^ 40 * 1032927 * 2
def baseEnd_1032927 : Nat := 52384003161163990327127

theorem tailTrace_1032927 : CollatzResearch.WordTrace tailWord_1032927 prefixEnd_1032927 52384003161163990327127 := by
  unfold tailWord_1032927
  simp only [CollatzResearch.WordTrace]
  refine ⟨37673942728889363732001035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25115961819259575821334023 37673942728889363732001035)
  ·
    refine ⟨56510914093334045598001553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37673942728889363732001035 56510914093334045598001553)
    ·
      refine ⟨42383185570000534198501165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56510914093334045598001553 42383185570000534198501165)
      ·
        refine ⟨15893694588750200324437937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42383185570000534198501165 15893694588750200324437937)
        ·
          refine ⟨11920270941562650243328453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15893694588750200324437937 11920270941562650243328453)
          ·
            refine ⟨2235050801542996920624085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11920270941562650243328453 2235050801542996920624085)
            ·
              refine ⟨52384003161163990327127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2235050801542996920624085 52384003161163990327127)
              ·
                rfl

theorem cell20_1032927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_1032927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032927 prefixEnd_1032927 := by exact prefixLift 1032927
  have htrace : WordTrace (prefixWord ++ tailWord_1032927) baseStart_1032927 baseEnd_1032927 := by
    simpa [prefixWord, tailWord_1032927, baseEnd_1032927] using wordTrace_append hprefix tailTrace_1032927
  have hstable : (prefixWord ++ tailWord_1032927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032927).length < 2 ^ (prefixWord ++ tailWord_1032927).sum := by decide
  have hdescent : baseEnd_1032927 < baseStart_1032927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032937 : List Nat := [1, 2, 1, 1, 1, 2, 6, 4, 2]
def baseStart_1032937 : Nat := 118140960795 + 1032937 * 2 ^ 59
def prefixEnd_1032937 : Nat := 4983230072969 + 3 ^ 40 * 1032937 * 2
def baseEnd_1032937 : Nat := 471460592722960322610769

theorem tailTrace_1032937 : CollatzResearch.WordTrace tailWord_1032937 prefixEnd_1032937 471460592722960322610769 := by
  unfold tailWord_1032937
  simp only [CollatzResearch.WordTrace]
  refine ⟨37674307458853135439865065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25116204972568756959910043 37674307458853135439865065)
  ·
    refine ⟨28255730594139851579898799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37674307458853135439865065 28255730594139851579898799)
    ·
      refine ⟨42383595891209777369848199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28255730594139851579898799 42383595891209777369848199)
      ·
        refine ⟨63575393836814666054772299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42383595891209777369848199 63575393836814666054772299)
        ·
          refine ⟨95363090755221999082158449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63575393836814666054772299 95363090755221999082158449)
          ·
            refine ⟨71522318066416499311618837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95363090755221999082158449 71522318066416499311618837)
            ·
              refine ⟨3352608659363273405232133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71522318066416499311618837 3352608659363273405232133)
              ·
                refine ⟨628614123630613763481025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3352608659363273405232133 628614123630613763481025)
                ·
                  refine ⟨471460592722960322610769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628614123630613763481025 471460592722960322610769)
                  ·
                    rfl

theorem cell20_1032937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_1032937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032937 prefixEnd_1032937 := by exact prefixLift 1032937
  have htrace : WordTrace (prefixWord ++ tailWord_1032937) baseStart_1032937 baseEnd_1032937 := by
    simpa [prefixWord, tailWord_1032937, baseEnd_1032937] using wordTrace_append hprefix tailTrace_1032937
  have hstable : (prefixWord ++ tailWord_1032937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032937).length < 2 ^ (prefixWord ++ tailWord_1032937).sum := by decide
  have hdescent : baseEnd_1032937 < baseStart_1032937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1032978 : List Nat := [3, 2, 4, 1, 3, 1, 6]
def baseStart_1032978 : Nat := 118140960795 + 1032978 * 2 ^ 59
def prefixEnd_1032978 : Nat := 4983230072969 + 3 ^ 40 * 1032978 * 2
def baseEnd_1032978 : Nat := 52386589582238489138215

theorem tailTrace_1032978 : CollatzResearch.WordTrace tailWord_1032978 prefixEnd_1032978 52386589582238489138215 := by
  unfold tailWord_1032978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418950712926149860526897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25117201901136399628071725 9418950712926149860526897)
  ·
    refine ⟨7064213034694612395395173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9418950712926149860526897 7064213034694612395395173)
    ·
      refine ⟨1324539944005239824136595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7064213034694612395395173 1324539944005239824136595)
      ·
        refine ⟨1986809916007859736204893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324539944005239824136595 1986809916007859736204893)
        ·
          refine ⟨745053718502947401076835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1986809916007859736204893 745053718502947401076835)
          ·
            refine ⟨1117580577754421101615253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745053718502947401076835 1117580577754421101615253)
            ·
              refine ⟨52386589582238489138215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1117580577754421101615253 52386589582238489138215)
              ·
                rfl

theorem cell20_1032978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 6].length) (baseStart_1032978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1032978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1032978 prefixEnd_1032978 := by exact prefixLift 1032978
  have htrace : WordTrace (prefixWord ++ tailWord_1032978) baseStart_1032978 baseEnd_1032978 := by
    simpa [prefixWord, tailWord_1032978, baseEnd_1032978] using wordTrace_append hprefix tailTrace_1032978
  have hstable : (prefixWord ++ tailWord_1032978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1032978).length < 2 ^ (prefixWord ++ tailWord_1032978).sum := by decide
  have hdescent : baseEnd_1032978 < baseStart_1032978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1032978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033037 : List Nat := [1, 6, 1, 2, 3, 7]
def baseStart_1033037 : Nat := 118140960795 + 1033037 * 2 ^ 59
def prefixEnd_1033037 : Nat := 4983230072969 + 3 ^ 40 * 1033037 * 2
def baseEnd_1033037 : Nat := 17463193905474237751001

theorem tailTrace_1033037 : CollatzResearch.WordTrace tailWord_1033037 prefixEnd_1033037 17463193905474237751001 := by
  unfold tailWord_1033037
  simp only [CollatzResearch.WordTrace]
  refine ⟨37677954758490852518505365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25118636505660568345670243 37677954758490852518505365)
  ·
    refine ⟨1766154129304258711804939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37677954758490852518505365 1766154129304258711804939)
    ·
      refine ⟨2649231193956388067707409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1766154129304258711804939 2649231193956388067707409)
      ·
        refine ⟨1986923395467291050780557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2649231193956388067707409 1986923395467291050780557)
        ·
          refine ⟨745096273300234144042709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1986923395467291050780557 745096273300234144042709)
          ·
            refine ⟨17463193905474237751001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 745096273300234144042709 17463193905474237751001)
            ·
              rfl

theorem cell20_1033037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 7].length) (baseStart_1033037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033037 prefixEnd_1033037 := by exact prefixLift 1033037
  have htrace : WordTrace (prefixWord ++ tailWord_1033037) baseStart_1033037 baseEnd_1033037 := by
    simpa [prefixWord, tailWord_1033037, baseEnd_1033037] using wordTrace_append hprefix tailTrace_1033037
  have hstable : (prefixWord ++ tailWord_1033037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033037).length < 2 ^ (prefixWord ++ tailWord_1033037).sum := by decide
  have hdescent : baseEnd_1033037 < baseStart_1033037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033041 : List Nat := [1, 2, 2, 1, 6, 8]
def baseStart_1033041 : Nat := 118140960795 + 1033041 * 2 ^ 59
def prefixEnd_1033041 : Nat := 4983230072969 + 3 ^ 40 * 1033041 * 2
def baseEnd_1033041 : Nat := 17463261524325858634951

theorem tailTrace_1033041 : CollatzResearch.WordTrace tailWord_1033041 prefixEnd_1033041 17463261524325858634951 := by
  unfold tailWord_1033041
  simp only [CollatzResearch.WordTrace]
  refine ⟨37678100650476361201650977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25118733766984240801100651 37678100650476361201650977)
  ·
    refine ⟨28258575487857270901238233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37678100650476361201650977 28258575487857270901238233)
    ·
      refine ⟨21193931615892953175928675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28258575487857270901238233 21193931615892953175928675)
      ·
        refine ⟨31790897423839429763893013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21193931615892953175928675 31790897423839429763893013)
        ·
          refine ⟨1490198316742473270182485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31790897423839429763893013 1490198316742473270182485)
          ·
            refine ⟨17463261524325858634951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1490198316742473270182485 17463261524325858634951)
            ·
              rfl

theorem cell20_1033041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 8].length) (baseStart_1033041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033041 prefixEnd_1033041 := by exact prefixLift 1033041
  have htrace : WordTrace (prefixWord ++ tailWord_1033041) baseStart_1033041 baseEnd_1033041 := by
    simpa [prefixWord, tailWord_1033041, baseEnd_1033041] using wordTrace_append hprefix tailTrace_1033041
  have hstable : (prefixWord ++ tailWord_1033041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033041).length < 2 ^ (prefixWord ++ tailWord_1033041).sum := by decide
  have hdescent : baseEnd_1033041 < baseStart_1033041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033047 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 2]
def baseStart_1033047 : Nat := 118140960795 + 1033047 * 2 ^ 59
def prefixEnd_1033047 : Nat := 4983230072969 + 3 ^ 40 * 1033047 * 2
def baseEnd_1033047 : Nat := 471510799720288828943653

theorem tailTrace_1033047 : CollatzResearch.WordTrace tailWord_1033047 prefixEnd_1033047 471510799720288828943653 := by
  unfold tailWord_1033047
  simp only [CollatzResearch.WordTrace]
  refine ⟨37678319488454624226369395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25118879658969749484246263 37678319488454624226369395)
  ·
    refine ⟨56517479232681936339554093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37678319488454624226369395 56517479232681936339554093)
    ·
      refine ⟨21194054712255726127332785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56517479232681936339554093 21194054712255726127332785)
      ·
        refine ⟨15895541034191794595499589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21194054712255726127332785 15895541034191794595499589)
        ·
          refine ⟨2980413943910961486656173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15895541034191794595499589 2980413943910961486656173)
          ·
            refine ⟨1117655228966610557496065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2980413943910961486656173 1117655228966610557496065)
            ·
              refine ⟨838241421724957918122049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1117655228966610557496065 838241421724957918122049)
              ·
                refine ⟨628681066293718438591537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838241421724957918122049 628681066293718438591537)
                ·
                  refine ⟨471510799720288828943653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628681066293718438591537 471510799720288828943653)
                  ·
                    rfl

theorem cell20_1033047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 2].length) (baseStart_1033047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033047 prefixEnd_1033047 := by exact prefixLift 1033047
  have htrace : WordTrace (prefixWord ++ tailWord_1033047) baseStart_1033047 baseEnd_1033047 := by
    simpa [prefixWord, tailWord_1033047, baseEnd_1033047] using wordTrace_append hprefix tailTrace_1033047
  have hstable : (prefixWord ++ tailWord_1033047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033047).length < 2 ^ (prefixWord ++ tailWord_1033047).sum := by decide
  have hdescent : baseEnd_1033047 < baseStart_1033047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033048 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_1033048 : Nat := 118140960795 + 1033048 * 2 ^ 59
def prefixEnd_1033048 : Nat := 4983230072969 + 3 ^ 40 * 1033048 * 2
def baseEnd_1033048 : Nat := 471511256147537269910315

theorem tailTrace_1033048 : CollatzResearch.WordTrace tailWord_1033048 prefixEnd_1033048 471511256147537269910315 := by
  unfold tailWord_1033048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18839177980725500698577899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25118903974300667598103865 18839177980725500698577899)
  ·
    refine ⟨28258766971088251047866849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18839177980725500698577899 28258766971088251047866849)
    ·
      refine ⟨21194075228316188285900137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28258766971088251047866849 21194075228316188285900137)
      ·
        refine ⟨15895556421237141214425103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21194075228316188285900137 15895556421237141214425103)
        ·
          refine ⟨23843334631855711821637655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15895556421237141214425103 23843334631855711821637655)
          ·
            refine ⟨35765001947783567732456483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23843334631855711821637655 35765001947783567732456483)
            ·
              refine ⟨53647502921675351598684725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35765001947783567732456483 53647502921675351598684725)
              ·
                refine ⟨5029453398907064212376693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53647502921675351598684725 5029453398907064212376693)
                ·
                  refine ⟨471511256147537269910315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5029453398907064212376693 471511256147537269910315)
                  ·
                    rfl

theorem cell20_1033048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_1033048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033048 prefixEnd_1033048 := by exact prefixLift 1033048
  have htrace : WordTrace (prefixWord ++ tailWord_1033048) baseStart_1033048 baseEnd_1033048 := by
    simpa [prefixWord, tailWord_1033048, baseEnd_1033048] using wordTrace_append hprefix tailTrace_1033048
  have hstable : (prefixWord ++ tailWord_1033048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033048).length < 2 ^ (prefixWord ++ tailWord_1033048).sum := by decide
  have hdescent : baseEnd_1033048 < baseStart_1033048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033106 : List Nat := [3, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1033106 : Nat := 118140960795 + 1033106 * 2 ^ 59
def prefixEnd_1033106 : Nat := 4983230072969 + 3 ^ 40 * 1033106 * 2
def baseEnd_1033106 : Nat := 471537728927946845976745

theorem tailTrace_1033106 : CollatzResearch.WordTrace tailWord_1033106 prefixEnd_1033106 471537728927946845976745 := by
  unfold tailWord_1033106
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420117848810219325691793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25120314263493918201844781 9420117848810219325691793)
  ·
    refine ⟨7065088386607664494268845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9420117848810219325691793 7065088386607664494268845)
    ·
      refine ⟨2649408144977874185350817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7065088386607664494268845 2649408144977874185350817)
      ·
        refine ⟨1987056108733405639013113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2649408144977874185350817 1987056108733405639013113)
        ·
          refine ⟨1490292081550054229259835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1987056108733405639013113 1490292081550054229259835)
          ·
            refine ⟨2235438122325081343889753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490292081550054229259835 2235438122325081343889753)
            ·
              refine ⟨1676578591743811007917315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235438122325081343889753 1676578591743811007917315)
              ·
                refine ⟨2514867887615716511875973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676578591743811007917315 2514867887615716511875973)
                ·
                  refine ⟨471537728927946845976745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2514867887615716511875973 471537728927946845976745)
                  ·
                    rfl

theorem cell20_1033106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1033106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033106 prefixEnd_1033106 := by exact prefixLift 1033106
  have htrace : WordTrace (prefixWord ++ tailWord_1033106) baseStart_1033106 baseEnd_1033106 := by
    simpa [prefixWord, tailWord_1033106, baseEnd_1033106] using wordTrace_append hprefix tailTrace_1033106
  have hstable : (prefixWord ++ tailWord_1033106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033106).length < 2 ^ (prefixWord ++ tailWord_1033106).sum := by decide
  have hdescent : baseEnd_1033106 < baseStart_1033106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033117 : List Nat := [1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_1033117 : Nat := 118140960795 + 1033117 * 2 ^ 59
def prefixEnd_1033117 : Nat := 4983230072969 + 3 ^ 40 * 1033117 * 2
def baseEnd_1033117 : Nat := 157180916542559898870011

theorem tailTrace_1033117 : CollatzResearch.WordTrace tailWord_1033117 prefixEnd_1033117 157180916542559898870011 := by
  unfold tailWord_1033117
  simp only [CollatzResearch.WordTrace]
  refine ⟨37680872598201026181417605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25120581732134017454278403 37680872598201026181417605)
  ·
    refine ⟨7065163612162692409015801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37680872598201026181417605 7065163612162692409015801)
    ·
      refine ⟨5298872709122019306761851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7065163612162692409015801 5298872709122019306761851)
      ·
        refine ⟨7948309063683028960142777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298872709122019306761851 7948309063683028960142777)
        ·
          refine ⟨5961231797762271720107083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7948309063683028960142777 5961231797762271720107083)
          ·
            refine ⟨8941847696643407580160625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961231797762271720107083 8941847696643407580160625)
            ·
              refine ⟨6706385772482555685120469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8941847696643407580160625 6706385772482555685120469)
              ·
                refine ⟨157180916542559898870011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6706385772482555685120469 157180916542559898870011)
                ·
                  rfl

theorem cell20_1033117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_1033117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033117 prefixEnd_1033117 := by exact prefixLift 1033117
  have htrace : WordTrace (prefixWord ++ tailWord_1033117) baseStart_1033117 baseEnd_1033117 := by
    simpa [prefixWord, tailWord_1033117, baseEnd_1033117] using wordTrace_append hprefix tailTrace_1033117
  have hstable : (prefixWord ++ tailWord_1033117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033117).length < 2 ^ (prefixWord ++ tailWord_1033117).sum := by decide
  have hdescent : baseEnd_1033117 < baseStart_1033117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033140 : List Nat := [2, 5, 2, 1, 1, 3, 1, 3, 2]
def baseStart_1033140 : Nat := 118140960795 + 1033140 * 2 ^ 59
def prefixEnd_1033140 : Nat := 4983230072969 + 3 ^ 40 * 1033140 * 2
def baseEnd_1033140 : Nat := 471553247454393838843273

theorem tailTrace_1033140 : CollatzResearch.WordTrace tailWord_1033140 prefixEnd_1033140 471553247454393838843273 := by
  unfold tailWord_1033140
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840855738558850554752437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25121140984745134073003249 18840855738558850554752437)
  ·
    refine ⟨1766330225489892239508041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18840855738558850554752437 1766330225489892239508041)
    ·
      refine ⟨1324747669117419179631031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1766330225489892239508041 1324747669117419179631031)
      ·
        refine ⟨1987121503676128769446547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324747669117419179631031 1987121503676128769446547)
        ·
          refine ⟨2980682255514193154169821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987121503676128769446547 2980682255514193154169821)
          ·
            refine ⟨1117755845817822432813683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2980682255514193154169821 1117755845817822432813683)
            ·
              refine ⟨1676633768726733649220525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117755845817822432813683 1676633768726733649220525)
              ·
                refine ⟨628737663272525118457697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676633768726733649220525 628737663272525118457697)
                ·
                  refine ⟨471553247454393838843273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628737663272525118457697 471553247454393838843273)
                  ·
                    rfl

theorem cell20_1033140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_1033140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033140 prefixEnd_1033140 := by exact prefixLift 1033140
  have htrace : WordTrace (prefixWord ++ tailWord_1033140) baseStart_1033140 baseEnd_1033140 := by
    simpa [prefixWord, tailWord_1033140, baseEnd_1033140] using wordTrace_append hprefix tailTrace_1033140
  have hstable : (prefixWord ++ tailWord_1033140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033140).length < 2 ^ (prefixWord ++ tailWord_1033140).sum := by decide
  have hdescent : baseEnd_1033140 < baseStart_1033140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033144 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 2]
def baseStart_1033144 : Nat := 118140960795 + 1033144 * 2 ^ 59
def prefixEnd_1033144 : Nat := 4983230072969 + 3 ^ 40 * 1033144 * 2
def baseEnd_1033144 : Nat := 471555073163387602709923

theorem tailTrace_1033144 : CollatzResearch.WordTrace tailWord_1033144 prefixEnd_1033144 471555073163387602709923 := by
  unfold tailWord_1033144
  simp only [CollatzResearch.WordTrace]
  refine ⟨18840928684551604896325243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25121238246068806528433657 18840928684551604896325243)
  ·
    refine ⟨28261393026827407344487865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18840928684551604896325243 28261393026827407344487865)
    ·
      refine ⟨21196044770120555508365899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28261393026827407344487865 21196044770120555508365899)
      ·
        refine ⟨31794067155180833262548849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21196044770120555508365899 31794067155180833262548849)
        ·
          refine ⟨23845550366385624946911637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31794067155180833262548849 23845550366385624946911637)
          ·
            refine ⟨1117760173424326169386483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23845550366385624946911637 1117760173424326169386483)
            ·
              refine ⟨1676640260136489254079725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117760173424326169386483 1676640260136489254079725)
              ·
                refine ⟨628740097551183470279897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676640260136489254079725 628740097551183470279897)
                ·
                  refine ⟨471555073163387602709923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628740097551183470279897 471555073163387602709923)
                  ·
                    rfl

theorem cell20_1033144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_1033144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033144 prefixEnd_1033144 := by exact prefixLift 1033144
  have htrace : WordTrace (prefixWord ++ tailWord_1033144) baseStart_1033144 baseEnd_1033144 := by
    simpa [prefixWord, tailWord_1033144, baseEnd_1033144] using wordTrace_append hprefix tailTrace_1033144
  have hstable : (prefixWord ++ tailWord_1033144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033144).length < 2 ^ (prefixWord ++ tailWord_1033144).sum := by decide
  have hdescent : baseEnd_1033144 < baseStart_1033144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033172 : List Nat := [2, 4, 1, 2, 1, 3, 2, 5]
def baseStart_1033172 : Nat := 118140960795 + 1033172 * 2 ^ 59
def prefixEnd_1033172 : Nat := 4983230072969 + 3 ^ 40 * 1033172 * 2
def baseEnd_1033172 : Nat := 157189284375447983258825

theorem tailTrace_1033172 : CollatzResearch.WordTrace tailWord_1033172 prefixEnd_1033172 157189284375447983258825 := by
  unfold tailWord_1033172
  simp only [CollatzResearch.WordTrace]
  refine ⟨18841439306500885287334885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25121919075334513716446513 18841439306500885287334885)
  ·
    refine ⟨3532769869968915991375291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18841439306500885287334885 3532769869968915991375291)
    ·
      refine ⟨5299154804953373987062937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532769869968915991375291 5299154804953373987062937)
      ·
        refine ⟨3974366103715030490297203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5299154804953373987062937 3974366103715030490297203)
        ·
          refine ⟨5961549155572545735445805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974366103715030490297203 5961549155572545735445805)
          ·
            refine ⟨2235580933339704650792177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5961549155572545735445805 2235580933339704650792177)
            ·
              refine ⟨1676685700004778488094133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235580933339704650792177 1676685700004778488094133)
              ·
                refine ⟨157189284375447983258825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1676685700004778488094133 157189284375447983258825)
                ·
                  rfl

theorem cell20_1033172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 5].length) (baseStart_1033172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033172 prefixEnd_1033172 := by exact prefixLift 1033172
  have htrace : WordTrace (prefixWord ++ tailWord_1033172) baseStart_1033172 baseEnd_1033172 := by
    simpa [prefixWord, tailWord_1033172, baseEnd_1033172] using wordTrace_append hprefix tailTrace_1033172
  have hstable : (prefixWord ++ tailWord_1033172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033172).length < 2 ^ (prefixWord ++ tailWord_1033172).sum := by decide
  have hdescent : baseEnd_1033172 < baseStart_1033172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033217 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 3]
def baseStart_1033217 : Nat := 118140960795 + 1033217 * 2 ^ 59
def prefixEnd_1033217 : Nat := 4983230072969 + 3 ^ 40 * 1033217 * 2
def baseEnd_1033217 : Nat := 471588392352523793276291

theorem tailTrace_1033217 : CollatzResearch.WordTrace tailWord_1033217 prefixEnd_1033217 471588392352523793276291 := by
  unfold tailWord_1033217
  simp only [CollatzResearch.WordTrace]
  refine ⟨37684519897838743260057905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25123013265225828840038603 37684519897838743260057905)
  ·
    refine ⟨28263389923379057445043429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37684519897838743260057905 28263389923379057445043429)
    ·
      refine ⟨5299385610633573270945643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28263389923379057445043429 5299385610633573270945643)
      ·
        refine ⟨7949078415950359906418465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299385610633573270945643 7949078415950359906418465)
        ·
          refine ⟨5961808811962769929813849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7949078415950359906418465 5961808811962769929813849)
          ·
            refine ⟨4471356608972077447360387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5961808811962769929813849 4471356608972077447360387)
            ·
              refine ⟨6707034913458116171040581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471356608972077447360387 6707034913458116171040581)
              ·
                refine ⟨1257569046273396782070109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6707034913458116171040581 1257569046273396782070109)
                ·
                  refine ⟨471588392352523793276291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257569046273396782070109 471588392352523793276291)
                  ·
                    rfl

theorem cell20_1033217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 3].length) (baseStart_1033217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033217 prefixEnd_1033217 := by exact prefixLift 1033217
  have htrace : WordTrace (prefixWord ++ tailWord_1033217) baseStart_1033217 baseEnd_1033217 := by
    simpa [prefixWord, tailWord_1033217, baseEnd_1033217] using wordTrace_append hprefix tailTrace_1033217
  have hstable : (prefixWord ++ tailWord_1033217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033217).length < 2 ^ (prefixWord ++ tailWord_1033217).sum := by decide
  have hdescent : baseEnd_1033217 < baseStart_1033217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033262 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1033262 : Nat := 118140960795 + 1033262 * 2 ^ 59
def prefixEnd_1033262 : Nat := 4983230072969 + 3 ^ 40 * 1033262 * 2
def baseEnd_1033262 : Nat := 471608931578703636776107

theorem tailTrace_1033262 : CollatzResearch.WordTrace tailWord_1033262 prefixEnd_1033262 471608931578703636776107 := by
  unfold tailWord_1033262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4710770147834464493180755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25124107455117143963630693 4710770147834464493180755)
  ·
    refine ⟨7066155221751696739771133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4710770147834464493180755 7066155221751696739771133)
    ·
      refine ⟨2649808208156886277414175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7066155221751696739771133 2649808208156886277414175)
      ·
        refine ⟨3974712312235329416121263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2649808208156886277414175 3974712312235329416121263)
        ·
          refine ⟨5962068468352994124181895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3974712312235329416121263 5962068468352994124181895)
          ·
            refine ⟨8943102702529491186272843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5962068468352994124181895 8943102702529491186272843)
            ·
              refine ⟨13414654053794236779409265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8943102702529491186272843 13414654053794236779409265)
              ·
                refine ⟨10060990540345677584556949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13414654053794236779409265 10060990540345677584556949)
                ·
                  refine ⟨471608931578703636776107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10060990540345677584556949 471608931578703636776107)
                  ·
                    rfl

theorem cell20_1033262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1033262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033262 prefixEnd_1033262 := by exact prefixLift 1033262
  have htrace : WordTrace (prefixWord ++ tailWord_1033262) baseStart_1033262 baseEnd_1033262 := by
    simpa [prefixWord, tailWord_1033262, baseEnd_1033262] using wordTrace_append hprefix tailTrace_1033262
  have hstable : (prefixWord ++ tailWord_1033262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033262).length < 2 ^ (prefixWord ++ tailWord_1033262).sum := by decide
  have hdescent : baseEnd_1033262 < baseStart_1033262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033272 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 3]
def baseStart_1033272 : Nat := 118140960795 + 1033272 * 2 ^ 59
def prefixEnd_1033272 : Nat := 4983230072969 + 3 ^ 40 * 1033272 * 2
def baseEnd_1033272 : Nat := 471613495851188046442733

theorem tailTrace_1033272 : CollatzResearch.WordTrace tailWord_1033272 prefixEnd_1033272 471613495851188046442733 := by
  unfold tailWord_1033272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843262956319743826655035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25124350608426325102206713 18843262956319743826655035)
  ·
    refine ⟨28264894434479615739982553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18843262956319743826655035 28264894434479615739982553)
    ·
      refine ⟨21198670825859711804986915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28264894434479615739982553 21198670825859711804986915)
      ·
        refine ⟨31798006238789567707480373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21198670825859711804986915 31798006238789567707480373)
        ·
          refine ⟨2981063084886521972576285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31798006238789567707480373 2981063084886521972576285)
          ·
            refine ⟨1117898656832445739716107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2981063084886521972576285 1117898656832445739716107)
            ·
              refine ⟨1676847985248668609574161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117898656832445739716107 1676847985248668609574161)
              ·
                refine ⟨1257635988936501457180621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676847985248668609574161 1257635988936501457180621)
                ·
                  refine ⟨471613495851188046442733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257635988936501457180621 471613495851188046442733)
                  ·
                    rfl

theorem cell20_1033272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_1033272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033272 prefixEnd_1033272 := by exact prefixLift 1033272
  have htrace : WordTrace (prefixWord ++ tailWord_1033272) baseStart_1033272 baseEnd_1033272 := by
    simpa [prefixWord, tailWord_1033272, baseEnd_1033272] using wordTrace_append hprefix tailTrace_1033272
  have hstable : (prefixWord ++ tailWord_1033272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033272).length < 2 ^ (prefixWord ++ tailWord_1033272).sum := by decide
  have hdescent : baseEnd_1033272 < baseStart_1033272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033300 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_1033300 : Nat := 118140960795 + 1033300 * 2 ^ 59
def prefixEnd_1033300 : Nat := 4983230072969 + 3 ^ 40 * 1033300 * 2
def baseEnd_1033300 : Nat := 471626275814144393509285

theorem tailTrace_1033300 : CollatzResearch.WordTrace tailWord_1033300 prefixEnd_1033300 471626275814144393509285 := by
  unfold tailWord_1033300
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843773578269024217664677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25125031437692032290219569 18843773578269024217664677)
  ·
    refine ⟨3533207545925442040812127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18843773578269024217664677 3533207545925442040812127)
    ·
      refine ⟨5299811318888163061218191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3533207545925442040812127 5299811318888163061218191)
      ·
        refine ⟨7949716978332244591827287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5299811318888163061218191 7949716978332244591827287)
        ·
          refine ⟨11924575467498366887740931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7949716978332244591827287 11924575467498366887740931)
          ·
            refine ⟨17886863201247550331611397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924575467498366887740931 17886863201247550331611397)
            ·
              refine ⟨3353786850233915687177137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17886863201247550331611397 3353786850233915687177137)
              ·
                refine ⟨2515340137675436765382853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353786850233915687177137 2515340137675436765382853)
                ·
                  refine ⟨471626275814144393509285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515340137675436765382853 471626275814144393509285)
                  ·
                    rfl

theorem cell20_1033300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_1033300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033300 prefixEnd_1033300 := by exact prefixLift 1033300
  have htrace : WordTrace (prefixWord ++ tailWord_1033300) baseStart_1033300 baseEnd_1033300 := by
    simpa [prefixWord, tailWord_1033300, baseEnd_1033300] using wordTrace_append hprefix tailTrace_1033300
  have hstable : (prefixWord ++ tailWord_1033300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033300).length < 2 ^ (prefixWord ++ tailWord_1033300).sum := by decide
  have hdescent : baseEnd_1033300 < baseStart_1033300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033345 : List Nat := [1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_1033345 : Nat := 118140960795 + 1033345 * 2 ^ 59
def prefixEnd_1033345 : Nat := 4983230072969 + 3 ^ 40 * 1033345 * 2
def baseEnd_1033345 : Nat := 157215605013441412336367

theorem tailTrace_1033345 : CollatzResearch.WordTrace tailWord_1033345 prefixEnd_1033345 157215605013441412336367 := by
  unfold tailWord_1033345
  simp only [CollatzResearch.WordTrace]
  refine ⟨37689188441375021120717489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25126125627583347413811659 37689188441375021120717489)
  ·
    refine ⟨28266891331031265840538117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37689188441375021120717489 28266891331031265840538117)
    ·
      refine ⟨5300042124568362345100897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28266891331031265840538117 5300042124568362345100897)
      ·
        refine ⟨3975031593426271758825673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5300042124568362345100897 3975031593426271758825673)
        ·
          refine ⟨2981273695069703819119255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3975031593426271758825673 2981273695069703819119255)
          ·
            refine ⟨4471910542604555728678883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981273695069703819119255 4471910542604555728678883)
            ·
              refine ⟨6707865813906833593018325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471910542604555728678883 6707865813906833593018325)
              ·
                refine ⟨157215605013441412336367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6707865813906833593018325 157215605013441412336367)
                ·
                  rfl

theorem cell20_1033345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_1033345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033345 prefixEnd_1033345 := by exact prefixLift 1033345
  have htrace : WordTrace (prefixWord ++ tailWord_1033345) baseStart_1033345 baseEnd_1033345 := by
    simpa [prefixWord, tailWord_1033345, baseEnd_1033345] using wordTrace_append hprefix tailTrace_1033345
  have hstable : (prefixWord ++ tailWord_1033345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033345).length < 2 ^ (prefixWord ++ tailWord_1033345).sum := by decide
  have hdescent : baseEnd_1033345 < baseStart_1033345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033348 : List Nat := [2, 3, 2, 1, 2, 2, 4, 1, 3]
def baseStart_1033348 : Nat := 118140960795 + 1033348 * 2 ^ 59
def prefixEnd_1033348 : Nat := 4983230072969 + 3 ^ 40 * 1033348 * 2
def baseEnd_1033348 : Nat := 471648184322069559909089

theorem tailTrace_1033348 : CollatzResearch.WordTrace tailWord_1033348 prefixEnd_1033348 471648184322069559909089 := by
  unfold tailWord_1033348
  simp only [CollatzResearch.WordTrace]
  refine ⟨18844648930182076316538349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25126198573576101755384465 18844648930182076316538349)
  ·
    refine ⟨7066743348818278618701881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18844648930182076316538349 7066743348818278618701881)
    ·
      refine ⟨5300057511613708964026411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7066743348818278618701881 5300057511613708964026411)
      ·
        refine ⟨7950086267420563446039617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5300057511613708964026411 7950086267420563446039617)
        ·
          refine ⟨5962564700565422584529713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7950086267420563446039617 5962564700565422584529713)
          ·
            refine ⟨4471923525424066938397285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5962564700565422584529713 4471923525424066938397285)
            ·
              refine ⟨838485661017012550949491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4471923525424066938397285 838485661017012550949491)
              ·
                refine ⟨1257728491525518826424237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838485661017012550949491 1257728491525518826424237)
                ·
                  refine ⟨471648184322069559909089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257728491525518826424237 471648184322069559909089)
                  ·
                    rfl

theorem cell20_1033348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_1033348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033348 prefixEnd_1033348 := by exact prefixLift 1033348
  have htrace : WordTrace (prefixWord ++ tailWord_1033348) baseStart_1033348 baseEnd_1033348 := by
    simpa [prefixWord, tailWord_1033348, baseEnd_1033348] using wordTrace_append hprefix tailTrace_1033348
  have hstable : (prefixWord ++ tailWord_1033348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033348).length < 2 ^ (prefixWord ++ tailWord_1033348).sum := by decide
  have hdescent : baseEnd_1033348 < baseStart_1033348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033383 : List Nat := [1, 1, 6, 2, 1, 9]
def baseStart_1033383 : Nat := 118140960795 + 1033383 * 2 ^ 59
def prefixEnd_1033383 : Nat := 4983230072969 + 3 ^ 40 * 1033383 * 2
def baseEnd_1033383 : Nat := 17469042936139444212677

theorem tailTrace_1033383 : CollatzResearch.WordTrace tailWord_1033383 prefixEnd_1033383 17469042936139444212677 := by
  unfold tailWord_1033383
  simp only [CollatzResearch.WordTrace]
  refine ⟨37690574415237353610600803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25127049610158235740400535 37690574415237353610600803)
  ·
    refine ⟨56535861622856030415901205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37690574415237353610600803 56535861622856030415901205)
    ·
      refine ⟨2650118513571376425745369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 56535861622856030415901205 2650118513571376425745369)
      ·
        refine ⟨1987588885178532319309027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650118513571376425745369 1987588885178532319309027)
        ·
          refine ⟨2981383327767798478963541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987588885178532319309027 2981383327767798478963541)
          ·
            refine ⟨17469042936139444212677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2981383327767798478963541 17469042936139444212677)
            ·
              rfl

theorem cell20_1033383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 9].length) (baseStart_1033383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033383 prefixEnd_1033383 := by exact prefixLift 1033383
  have htrace : WordTrace (prefixWord ++ tailWord_1033383) baseStart_1033383 baseEnd_1033383 := by
    simpa [prefixWord, tailWord_1033383, baseEnd_1033383] using wordTrace_append hprefix tailTrace_1033383
  have hstable : (prefixWord ++ tailWord_1033383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033383).length < 2 ^ (prefixWord ++ tailWord_1033383).sum := by decide
  have hdescent : baseEnd_1033383 < baseStart_1033383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033386 : List Nat := [3, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_1033386 : Nat := 118140960795 + 1033386 * 2 ^ 59
def prefixEnd_1033386 : Nat := 4983230072969 + 3 ^ 40 * 1033386 * 2
def baseEnd_1033386 : Nat := 471665528557510316642267

theorem tailTrace_1033386 : CollatzResearch.WordTrace tailWord_1033386 prefixEnd_1033386 471665528557510316642267 := by
  unfold tailWord_1033386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422670958556621280740003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25127122556150990081973341 9422670958556621280740003)
  ·
    refine ⟨14134006437834931921110005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9422670958556621280740003 14134006437834931921110005)
    ·
      refine ⟨1325063103547024867604063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14134006437834931921110005 1325063103547024867604063)
      ·
        refine ⟨1987594655320537301406095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325063103547024867604063 1987594655320537301406095)
        ·
          refine ⟨2981391982980805952109143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987594655320537301406095 2981391982980805952109143)
          ·
            refine ⟨4472087974471208928163715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981391982980805952109143 4472087974471208928163715)
            ·
              refine ⟨6708131961706813392245573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4472087974471208928163715 6708131961706813392245573)
              ·
                refine ⟨1257774742820027511046045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6708131961706813392245573 1257774742820027511046045)
                ·
                  refine ⟨471665528557510316642267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257774742820027511046045 471665528557510316642267)
                  ·
                    rfl

theorem cell20_1033386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_1033386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033386 prefixEnd_1033386 := by exact prefixLift 1033386
  have htrace : WordTrace (prefixWord ++ tailWord_1033386) baseStart_1033386 baseEnd_1033386 := by
    simpa [prefixWord, tailWord_1033386, baseEnd_1033386] using wordTrace_append hprefix tailTrace_1033386
  have hstable : (prefixWord ++ tailWord_1033386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033386).length < 2 ^ (prefixWord ++ tailWord_1033386).sum := by decide
  have hdescent : baseEnd_1033386 < baseStart_1033386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033445 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 5]
def baseStart_1033445 : Nat := 118140960795 + 1033445 * 2 ^ 59
def prefixEnd_1033445 : Nat := 4983230072969 + 3 ^ 40 * 1033445 * 2
def baseEnd_1033445 : Nat := 471692457765168333675359

theorem tailTrace_1033445 : CollatzResearch.WordTrace tailWord_1033445 prefixEnd_1033445 471692457765168333675359 := by
  unfold tailWord_1033445
  simp only [CollatzResearch.WordTrace]
  refine ⟨37692835741012738199357789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25128557160675158799571859 37692835741012738199357789)
  ·
    refine ⟨14134813402879776824759171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37692835741012738199357789 14134813402879776824759171)
    ·
      refine ⟨21202220104319665237138757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14134813402879776824759171 21202220104319665237138757)
      ·
        refine ⟨3975416269559937231963517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21202220104319665237138757 3975416269559937231963517)
        ·
          refine ⟨1490781101084976461986319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3975416269559937231963517 1490781101084976461986319)
          ·
            refine ⟨2236171651627464692979479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490781101084976461986319 2236171651627464692979479)
            ·
              refine ⟨3354257477441197039469219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236171651627464692979479 3354257477441197039469219)
              ·
                refine ⟨5031386216161795559203829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354257477441197039469219 5031386216161795559203829)
                ·
                  refine ⟨471692457765168333675359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5031386216161795559203829 471692457765168333675359)
                  ·
                    rfl

theorem cell20_1033445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_1033445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033445 prefixEnd_1033445 := by exact prefixLift 1033445
  have htrace : WordTrace (prefixWord ++ tailWord_1033445) baseStart_1033445 baseEnd_1033445 := by
    simpa [prefixWord, tailWord_1033445, baseEnd_1033445] using wordTrace_append hprefix tailTrace_1033445
  have hstable : (prefixWord ++ tailWord_1033445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033445).length < 2 ^ (prefixWord ++ tailWord_1033445).sum := by decide
  have hdescent : baseEnd_1033445 < baseStart_1033445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033452 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_1033452 : Nat := 118140960795 + 1033452 * 2 ^ 59
def prefixEnd_1033452 : Nat := 4983230072969 + 3 ^ 40 * 1033452 * 2
def baseEnd_1033452 : Nat := 471695652755907420441997

theorem tailTrace_1033452 : CollatzResearch.WordTrace tailWord_1033452 prefixEnd_1033452 471695652755907420441997 := by
  unfold tailWord_1033452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18846545525993689197431305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25128727367991585596575073 18846545525993689197431305)
  ·
    refine ⟨14134909144495266898073479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18846545525993689197431305 14134909144495266898073479)
    ·
      refine ⟨21202363716742900347110219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14134909144495266898073479 21202363716742900347110219)
      ·
        refine ⟨31803545575114350520665329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21202363716742900347110219 31803545575114350520665329)
        ·
          refine ⟨23852659181335762890498997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31803545575114350520665329 23852659181335762890498997)
          ·
            refine ⟨2236186798250227770984281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23852659181335762890498997 2236186798250227770984281)
            ·
              refine ⟨1677140098687670828238211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236186798250227770984281 1677140098687670828238211)
              ·
                refine ⟨2515710148031506242357317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677140098687670828238211 2515710148031506242357317)
                ·
                  refine ⟨471695652755907420441997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515710148031506242357317 471695652755907420441997)
                  ·
                    rfl

theorem cell20_1033452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_1033452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033452 prefixEnd_1033452 := by exact prefixLift 1033452
  have htrace : WordTrace (prefixWord ++ tailWord_1033452) baseStart_1033452 baseEnd_1033452 := by
    simpa [prefixWord, tailWord_1033452, baseEnd_1033452] using wordTrace_append hprefix tailTrace_1033452
  have hstable : (prefixWord ++ tailWord_1033452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033452).length < 2 ^ (prefixWord ++ tailWord_1033452).sum := by decide
  have hdescent : baseEnd_1033452 < baseStart_1033452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033476 : List Nat := [2, 3, 2, 2, 2, 1, 4, 4]
def baseStart_1033476 : Nat := 118140960795 + 1033476 * 2 ^ 59
def prefixEnd_1033476 : Nat := 4983230072969 + 3 ^ 40 * 1033476 * 2
def baseEnd_1033476 : Nat := 157235535669956667880633

theorem tailTrace_1033476 : CollatzResearch.WordTrace tailWord_1033476 prefixEnd_1033476 157235535669956667880633 := by
  unfold tailWord_1033476
  simp only [CollatzResearch.WordTrace]
  refine ⟨18846983201950215246868141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25129310935933620329157521 18846983201950215246868141)
  ·
    refine ⟨7067618700731330717575553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18846983201950215246868141 7067618700731330717575553)
    ·
      refine ⟨5300714025548498038181665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7067618700731330717575553 5300714025548498038181665)
      ·
        refine ⟨3975535519161373528636249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5300714025548498038181665 3975535519161373528636249)
        ·
          refine ⟨2981651639371030146477187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3975535519161373528636249 2981651639371030146477187)
          ·
            refine ⟨4472477459056545219715781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981651639371030146477187 4472477459056545219715781)
            ·
              refine ⟨838589523573102228696709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4472477459056545219715781 838589523573102228696709)
              ·
                refine ⟨157235535669956667880633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838589523573102228696709 157235535669956667880633)
                ·
                  rfl

theorem cell20_1033476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_1033476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033476 prefixEnd_1033476 := by exact prefixLift 1033476
  have htrace : WordTrace (prefixWord ++ tailWord_1033476) baseStart_1033476 baseEnd_1033476 := by
    simpa [prefixWord, tailWord_1033476, baseEnd_1033476] using wordTrace_append hprefix tailTrace_1033476
  have hstable : (prefixWord ++ tailWord_1033476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033476).length < 2 ^ (prefixWord ++ tailWord_1033476).sum := by decide
  have hdescent : baseEnd_1033476 < baseStart_1033476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033486 : List Nat := [4, 1, 1, 2, 1, 5, 1, 3, 2]
def baseStart_1033486 : Nat := 118140960795 + 1033486 * 2 ^ 59
def prefixEnd_1033486 : Nat := 4983230072969 + 3 ^ 40 * 1033486 * 2
def baseEnd_1033486 : Nat := 471711171282354413308525

theorem tailTrace_1033486 : CollatzResearch.WordTrace tailWord_1033486 prefixEnd_1033486 471711171282354413308525 := by
  unfold tailWord_1033486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711791391733025275200039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25129554089242801467733541 4711791391733025275200039)
  ·
    refine ⟨7067687087599537912800059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4711791391733025275200039 7067687087599537912800059)
    ·
      refine ⟨10601530631399306869200089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067687087599537912800059 10601530631399306869200089)
      ·
        refine ⟨7951147973549480151900067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10601530631399306869200089 7951147973549480151900067)
        ·
          refine ⟨11926721960324220227850101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951147973549480151900067 11926721960324220227850101)
          ·
            refine ⟨1118130183780395646360947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11926721960324220227850101 1118130183780395646360947)
            ·
              refine ⟨1677195275670593469541421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118130183780395646360947 1677195275670593469541421)
              ·
                refine ⟨628948228376472551078033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1677195275670593469541421 628948228376472551078033)
                ·
                  refine ⟨471711171282354413308525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628948228376472551078033 471711171282354413308525)
                  ·
                    rfl

theorem cell20_1033486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_1033486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033486 prefixEnd_1033486 := by exact prefixLift 1033486
  have htrace : WordTrace (prefixWord ++ tailWord_1033486) baseStart_1033486 baseEnd_1033486 := by
    simpa [prefixWord, tailWord_1033486, baseEnd_1033486] using wordTrace_append hprefix tailTrace_1033486
  have hstable : (prefixWord ++ tailWord_1033486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033486).length < 2 ^ (prefixWord ++ tailWord_1033486).sum := by decide
  have hdescent : baseEnd_1033486 < baseStart_1033486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033514 : List Nat := [3, 1, 4, 2, 1, 2, 2, 5]
def baseStart_1033514 : Nat := 118140960795 + 1033514 * 2 ^ 59
def prefixEnd_1033514 : Nat := 4983230072969 + 3 ^ 40 * 1033514 * 2
def baseEnd_1033514 : Nat := 157241317081770253458359

theorem tailTrace_1033514 : CollatzResearch.WordTrace tailWord_1033514 prefixEnd_1033514 157241317081770253458359 := by
  unfold tailWord_1033514
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423838094440690745904899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25130234918508508655746397 9423838094440690745904899)
  ·
    refine ⟨14135757141661036118857349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9423838094440690745904899 14135757141661036118857349)
    ·
      refine ⟨2650454464061444272285753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14135757141661036118857349 2650454464061444272285753)
      ·
        refine ⟨1987840848046083204214315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650454464061444272285753 1987840848046083204214315)
        ·
          refine ⟨2981761272069124806321473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987840848046083204214315 2981761272069124806321473)
          ·
            refine ⟨2236320954051843604741105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981761272069124806321473 2236320954051843604741105)
            ·
              refine ⟨1677240715538882703555829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236320954051843604741105 1677240715538882703555829)
              ·
                refine ⟨157241317081770253458359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677240715538882703555829 157241317081770253458359)
                ·
                  rfl

theorem cell20_1033514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 5].length) (baseStart_1033514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033514 prefixEnd_1033514 := by exact prefixLift 1033514
  have htrace : WordTrace (prefixWord ++ tailWord_1033514) baseStart_1033514 baseEnd_1033514 := by
    simpa [prefixWord, tailWord_1033514, baseEnd_1033514] using wordTrace_append hprefix tailTrace_1033514
  have hstable : (prefixWord ++ tailWord_1033514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033514).length < 2 ^ (prefixWord ++ tailWord_1033514).sum := by decide
  have hdescent : baseEnd_1033514 < baseStart_1033514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033517 : List Nat := [1, 5, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1033517 : Nat := 118140960795 + 1033517 * 2 ^ 59
def prefixEnd_1033517 : Nat := 4983230072969 + 3 ^ 40 * 1033517 * 2
def baseEnd_1033517 : Nat := 471725320527056083275065

theorem tailTrace_1033517 : CollatzResearch.WordTrace tailWord_1033517 prefixEnd_1033517 471725320527056083275065 := by
  unfold tailWord_1033517
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695461796751894495978805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25130307864501262997319203 37695461796751894495978805)
  ·
    refine ⟨3533949543445490108998013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37695461796751894495978805 3533949543445490108998013)
    ·
      refine ⟨1325231078792058790874255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3533949543445490108998013 1325231078792058790874255)
      ·
        refine ⟨1987846618188088186311383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325231078792058790874255 1987846618188088186311383)
        ·
          refine ⟨2981769927282132279467075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987846618188088186311383 2981769927282132279467075)
          ·
            refine ⟨4472654890923198419200613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981769927282132279467075 4472654890923198419200613)
            ·
              refine ⟨838622792048099703600115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4472654890923198419200613 838622792048099703600115)
              ·
                refine ⟨1257934188072149555400173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838622792048099703600115 1257934188072149555400173)
                ·
                  refine ⟨471725320527056083275065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257934188072149555400173 471725320527056083275065)
                  ·
                    rfl

theorem cell20_1033517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1033517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033517 prefixEnd_1033517 := by exact prefixLift 1033517
  have htrace : WordTrace (prefixWord ++ tailWord_1033517) baseStart_1033517 baseEnd_1033517 := by
    simpa [prefixWord, tailWord_1033517, baseEnd_1033517] using wordTrace_append hprefix tailTrace_1033517
  have hstable : (prefixWord ++ tailWord_1033517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033517).length < 2 ^ (prefixWord ++ tailWord_1033517).sum := by decide
  have hdescent : baseEnd_1033517 < baseStart_1033517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033521 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 3]
def baseStart_1033521 : Nat := 118140960795 + 1033521 * 2 ^ 59
def prefixEnd_1033521 : Nat := 4983230072969 + 3 ^ 40 * 1033521 * 2
def baseEnd_1033521 : Nat := 471727146236049847141715

theorem tailTrace_1033521 : CollatzResearch.WordTrace tailWord_1033521 prefixEnd_1033521 471727146236049847141715 := by
  unfold tailWord_1033521
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695607688737403179124417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25130405125824935452749611 37695607688737403179124417)
  ·
    refine ⟨28271705766553052384343313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37695607688737403179124417 28271705766553052384343313)
    ·
      refine ⟨21203779324914789288257485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28271705766553052384343313 21203779324914789288257485)
      ·
        refine ⟨7951417246843045983096557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21203779324914789288257485 7951417246843045983096557)
        ·
          refine ⟨2981781467566142243661209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7951417246843045983096557 2981781467566142243661209)
          ·
            refine ⟨2236336100674606682745907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981781467566142243661209 2236336100674606682745907)
            ·
              refine ⟨3354504151011910024118861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236336100674606682745907 3354504151011910024118861)
              ·
                refine ⟨1257939056629466259044573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3354504151011910024118861 1257939056629466259044573)
                ·
                  refine ⟨471727146236049847141715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257939056629466259044573 471727146236049847141715)
                  ·
                    rfl

theorem cell20_1033521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_1033521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033521 prefixEnd_1033521 := by exact prefixLift 1033521
  have htrace : WordTrace (prefixWord ++ tailWord_1033521) baseStart_1033521 baseEnd_1033521 := by
    simpa [prefixWord, tailWord_1033521, baseEnd_1033521] using wordTrace_append hprefix tailTrace_1033521
  have hstable : (prefixWord ++ tailWord_1033521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033521).length < 2 ^ (prefixWord ++ tailWord_1033521).sum := by decide
  have hdescent : baseEnd_1033521 < baseStart_1033521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033559 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 3]
def baseStart_1033559 : Nat := 118140960795 + 1033559 * 2 ^ 59
def prefixEnd_1033559 : Nat := 4983230072969 + 3 ^ 40 * 1033559 * 2
def baseEnd_1033559 : Nat := 471744490471490603874893

theorem tailTrace_1033559 : CollatzResearch.WordTrace tailWord_1033559 prefixEnd_1033559 471744490471490603874893 := by
  unfold tailWord_1033559
  simp only [CollatzResearch.WordTrace]
  refine ⟨37696993662599735669007731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25131329108399823779338487 37696993662599735669007731)
  ·
    refine ⟨56545490493899603503511597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37696993662599735669007731 56545490493899603503511597)
    ·
      refine ⟨21204558935212351313816849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56545490493899603503511597 21204558935212351313816849)
      ·
        refine ⟨15903419201409263485362637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21204558935212351313816849 15903419201409263485362637)
        ·
          refine ⟨5963782200528473807010989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15903419201409263485362637 5963782200528473807010989)
          ·
            refine ⟨2236418325198177677629121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5963782200528473807010989 2236418325198177677629121)
            ·
              refine ⟨1677313743898633258221841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236418325198177677629121 1677313743898633258221841)
              ·
                refine ⟨1257985307923974943666381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677313743898633258221841 1257985307923974943666381)
                ·
                  refine ⟨471744490471490603874893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257985307923974943666381 471744490471490603874893)
                  ·
                    rfl

theorem cell20_1033559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3].length) (baseStart_1033559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033559 prefixEnd_1033559 := by exact prefixLift 1033559
  have htrace : WordTrace (prefixWord ++ tailWord_1033559) baseStart_1033559 baseEnd_1033559 := by
    simpa [prefixWord, tailWord_1033559, baseEnd_1033559] using wordTrace_append hprefix tailTrace_1033559
  have hstable : (prefixWord ++ tailWord_1033559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033559).length < 2 ^ (prefixWord ++ tailWord_1033559).sum := by decide
  have hdescent : baseEnd_1033559 < baseStart_1033559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033565 : List Nat := [1, 4, 5, 1, 2, 1, 1, 5]
def baseStart_1033565 : Nat := 118140960795 + 1033565 * 2 ^ 59
def prefixEnd_1033565 : Nat := 4983230072969 + 3 ^ 40 * 1033565 * 2
def baseEnd_1033565 : Nat := 157249076344993749891623

theorem tailTrace_1033565 : CollatzResearch.WordTrace tailWord_1033565 prefixEnd_1033565 157249076344993749891623 := by
  unfold tailWord_1033565
  simp only [CollatzResearch.WordTrace]
  refine ⟨37697212500577998693726149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25131475000385332462484099 37697212500577998693726149)
  ·
    refine ⟨7068227343858374755073653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37697212500577998693726149 7068227343858374755073653)
    ·
      refine ⟨662646313486722633288155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7068227343858374755073653 662646313486722633288155)
      ·
        refine ⟨993969470230083949932233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662646313486722633288155 993969470230083949932233)
        ·
          refine ⟨745477102672562962449175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993969470230083949932233 745477102672562962449175)
          ·
            refine ⟨1118215654008844443673763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745477102672562962449175 1118215654008844443673763)
            ·
              refine ⟨1677323481013266665510645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118215654008844443673763 1677323481013266665510645)
              ·
                refine ⟨157249076344993749891623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677323481013266665510645 157249076344993749891623)
                ·
                  rfl

theorem cell20_1033565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 5].length) (baseStart_1033565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033565 prefixEnd_1033565 := by exact prefixLift 1033565
  have htrace : WordTrace (prefixWord ++ tailWord_1033565) baseStart_1033565 baseEnd_1033565 := by
    simpa [prefixWord, tailWord_1033565, baseEnd_1033565] using wordTrace_append hprefix tailTrace_1033565
  have hstable : (prefixWord ++ tailWord_1033565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033565).length < 2 ^ (prefixWord ++ tailWord_1033565).sum := by decide
  have hdescent : baseEnd_1033565 < baseStart_1033565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033625 : List Nat := [1, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_1033625 : Nat := 118140960795 + 1033625 * 2 ^ 59
def prefixEnd_1033625 : Nat := 4983230072969 + 3 ^ 40 * 1033625 * 2
def baseEnd_1033625 : Nat := 471774614669887707674623

theorem tailTrace_1033625 : CollatzResearch.WordTrace tailWord_1033625 prefixEnd_1033625 471774614669887707674623 := by
  unfold tailWord_1033625
  simp only [CollatzResearch.WordTrace]
  refine ⟨37699400880360628940910329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25132933920240419293940219 37699400880360628940910329)
  ·
    refine ⟨28274550660270471705682747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37699400880360628940910329 28274550660270471705682747)
    ·
      refine ⟨42411825990405707558524121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28274550660270471705682747 42411825990405707558524121)
      ·
        refine ⟨31808869492804280668893091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42411825990405707558524121 31808869492804280668893091)
        ·
          refine ⟨47713304239206421003339637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31808869492804280668893091 47713304239206421003339637)
          ·
            refine ⟨4473122272425601969063091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47713304239206421003339637 4473122272425601969063091)
            ·
              refine ⟨6709683408638402953594637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473122272425601969063091 6709683408638402953594637)
              ·
                refine ⟨2516131278239401107597989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6709683408638402953594637 2516131278239401107597989)
                ·
                  refine ⟨471774614669887707674623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516131278239401107597989 471774614669887707674623)
                  ·
                    rfl

theorem cell20_1033625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_1033625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033625 prefixEnd_1033625 := by exact prefixLift 1033625
  have htrace : WordTrace (prefixWord ++ tailWord_1033625) baseStart_1033625 baseEnd_1033625 := by
    simpa [prefixWord, tailWord_1033625, baseEnd_1033625] using wordTrace_append hprefix tailTrace_1033625
  have hstable : (prefixWord ++ tailWord_1033625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033625).length < 2 ^ (prefixWord ++ tailWord_1033625).sum := by decide
  have hdescent : baseEnd_1033625 < baseStart_1033625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033632 : List Nat := [2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_1033632 : Nat := 118140960795 + 1033632 * 2 ^ 59
def prefixEnd_1033632 : Nat := 4983230072969 + 3 ^ 40 * 1033632 * 2
def baseEnd_1033632 : Nat := 157259269886875598147087

theorem tailTrace_1033632 : CollatzResearch.WordTrace tailWord_1033632 prefixEnd_1033632 157259269886875598147087 := by
  unfold tailWord_1033632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849828095667634568207575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25133104127556846090943433 18849828095667634568207575)
  ·
    refine ⟨28274742143501451852311363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18849828095667634568207575 28274742143501451852311363)
    ·
      refine ⟨42412113215252177778467045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28274742143501451852311363 42412113215252177778467045)
      ·
        refine ⟨7952271227859783333462571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42412113215252177778467045 7952271227859783333462571)
        ·
          refine ⟨11928406841789675000193857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7952271227859783333462571 11928406841789675000193857)
          ·
            refine ⟨8946305131342256250145393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11928406841789675000193857 8946305131342256250145393)
            ·
              refine ⟨6709728848506692187609045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8946305131342256250145393 6709728848506692187609045)
              ·
                refine ⟨157259269886875598147087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6709728848506692187609045 157259269886875598147087)
                ·
                  rfl

theorem cell20_1033632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_1033632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033632 prefixEnd_1033632 := by exact prefixLift 1033632
  have htrace : WordTrace (prefixWord ++ tailWord_1033632) baseStart_1033632 baseEnd_1033632 := by
    simpa [prefixWord, tailWord_1033632, baseEnd_1033632] using wordTrace_append hprefix tailTrace_1033632
  have hstable : (prefixWord ++ tailWord_1033632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033632).length < 2 ^ (prefixWord ++ tailWord_1033632).sum := by decide
  have hdescent : baseEnd_1033632 < baseStart_1033632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033635 : List Nat := [1, 1, 1, 4, 1, 3, 5, 1, 3]
def baseStart_1033635 : Nat := 118140960795 + 1033635 * 2 ^ 59
def prefixEnd_1033635 : Nat := 4983230072969 + 3 ^ 40 * 1033635 * 2
def baseEnd_1033635 : Nat := 471779178942372117341249

theorem tailTrace_1033635 : CollatzResearch.WordTrace tailWord_1033635 prefixEnd_1033635 471779178942372117341249 := by
  unfold tailWord_1033635
  simp only [CollatzResearch.WordTrace]
  refine ⟨37699765610324400648774359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25133177073549600432516239 37699765610324400648774359)
  ·
    refine ⟨56549648415486600973161539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37699765610324400648774359 56549648415486600973161539)
    ·
      refine ⟨84824472623229901459742309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56549648415486600973161539 84824472623229901459742309)
      ·
        refine ⟨15904588616855606523701683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84824472623229901459742309 15904588616855606523701683)
        ·
          refine ⟨23856882925283409785552525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15904588616855606523701683 23856882925283409785552525)
          ·
            refine ⟨8946331096981278669582197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23856882925283409785552525 8946331096981278669582197)
            ·
              refine ⟨838718540341994875273331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8946331096981278669582197 838718540341994875273331)
              ·
                refine ⟨1258077810512992312909997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838718540341994875273331 1258077810512992312909997)
                ·
                  refine ⟨471779178942372117341249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258077810512992312909997 471779178942372117341249)
                  ·
                    rfl

theorem cell20_1033635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 3].length) (baseStart_1033635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033635 prefixEnd_1033635 := by exact prefixLift 1033635
  have htrace : WordTrace (prefixWord ++ tailWord_1033635) baseStart_1033635 baseEnd_1033635 := by
    simpa [prefixWord, tailWord_1033635, baseEnd_1033635] using wordTrace_append hprefix tailTrace_1033635
  have hstable : (prefixWord ++ tailWord_1033635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033635).length < 2 ^ (prefixWord ++ tailWord_1033635).sum := by decide
  have hdescent : baseEnd_1033635 < baseStart_1033635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033645 : List Nat := [1, 5, 2, 2, 1, 3, 2, 4]
def baseStart_1033645 : Nat := 118140960795 + 1033645 * 2 ^ 59
def prefixEnd_1033645 : Nat := 4983230072969 + 3 ^ 40 * 1033645 * 2
def baseEnd_1033645 : Nat := 157261247738285509002625

theorem tailTrace_1033645 : CollatzResearch.WordTrace tailWord_1033645 prefixEnd_1033645 157261247738285509002625 := by
  unfold tailWord_1033645
  simp only [CollatzResearch.WordTrace]
  refine ⟨37700130340288172356638389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25133420226858781571092259 37700130340288172356638389)
  ·
    refine ⟨3534387219402016158434849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37700130340288172356638389 3534387219402016158434849)
    ·
      refine ⟨2650790414551512118826137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3534387219402016158434849 2650790414551512118826137)
      ·
        refine ⟨1988092810913634089119603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650790414551512118826137 1988092810913634089119603)
        ·
          refine ⟨2982139216370451133679405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988092810913634089119603 2982139216370451133679405)
          ·
            refine ⟨1118302206138919175129777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2982139216370451133679405 1118302206138919175129777)
            ·
              refine ⟨838726654604189381347333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118302206138919175129777 838726654604189381347333)
              ·
                refine ⟨157261247738285509002625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838726654604189381347333 157261247738285509002625)
                ·
                  rfl

theorem cell20_1033645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 4].length) (baseStart_1033645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033645 prefixEnd_1033645 := by exact prefixLift 1033645
  have htrace : WordTrace (prefixWord ++ tailWord_1033645) baseStart_1033645 baseEnd_1033645 := by
    simpa [prefixWord, tailWord_1033645, baseEnd_1033645] using wordTrace_append hprefix tailTrace_1033645
  have hstable : (prefixWord ++ tailWord_1033645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033645).length < 2 ^ (prefixWord ++ tailWord_1033645).sum := by decide
  have hdescent : baseEnd_1033645 < baseStart_1033645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033676 : List Nat := [2, 2, 1, 4, 2, 2, 3, 2, 2]
def baseStart_1033676 : Nat := 118140960795 + 1033676 * 2 ^ 59
def prefixEnd_1033676 : Nat := 4983230072969 + 3 ^ 40 * 1033676 * 2
def baseEnd_1033676 : Nat := 471797892459558196974415

theorem tailTrace_1033676 : CollatzResearch.WordTrace tailWord_1033676 prefixEnd_1033676 471797892459558196974415 := by
  unfold tailWord_1033676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18850630501587932325508441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25134174002117243100677921 18850630501587932325508441)
  ·
    refine ⟨14137972876190949244131331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18850630501587932325508441 14137972876190949244131331)
    ·
      refine ⟨21206959314286423866196997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14137972876190949244131331 21206959314286423866196997)
      ·
        refine ⟨3976304871428704474911937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21206959314286423866196997 3976304871428704474911937)
        ·
          refine ⟨2982228653571528356183953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976304871428704474911937 2982228653571528356183953)
          ·
            refine ⟨2236671490178646267137965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2982228653571528356183953 2236671490178646267137965)
            ·
              refine ⟨838751808816992350176737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2236671490178646267137965 838751808816992350176737)
              ·
                refine ⟨629063856612744262632553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838751808816992350176737 629063856612744262632553)
                ·
                  refine ⟨471797892459558196974415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629063856612744262632553 471797892459558196974415)
                  ·
                    rfl

theorem cell20_1033676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_1033676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033676 prefixEnd_1033676 := by exact prefixLift 1033676
  have htrace : WordTrace (prefixWord ++ tailWord_1033676) baseStart_1033676 baseEnd_1033676 := by
    simpa [prefixWord, tailWord_1033676, baseEnd_1033676] using wordTrace_append hprefix tailTrace_1033676
  have hstable : (prefixWord ++ tailWord_1033676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033676).length < 2 ^ (prefixWord ++ tailWord_1033676).sum := by decide
  have hdescent : baseEnd_1033676 < baseStart_1033676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033690 : List Nat := [3, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_1033690 : Nat := 118140960795 + 1033690 * 2 ^ 59
def prefixEnd_1033690 : Nat := 4983230072969 + 3 ^ 40 * 1033690 * 2
def baseEnd_1033690 : Nat := 471804282441036370507691

theorem tailTrace_1033690 : CollatzResearch.WordTrace tailWord_1033690 prefixEnd_1033690 471804282441036370507691 := by
  unfold tailWord_1033690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9425442906281286260506631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25134514416750096694684349 9425442906281286260506631)
  ·
    refine ⟨14138164359421929390759947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9425442906281286260506631 14138164359421929390759947)
    ·
      refine ⟨21207246539132894086139921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14138164359421929390759947 21207246539132894086139921)
      ·
        refine ⟨15905434904349670564604941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21207246539132894086139921 15905434904349670564604941)
        ·
          refine ⟨5964538089131126461726853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15905434904349670564604941 5964538089131126461726853)
          ·
            refine ⟨1118350891712086211573785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5964538089131126461726853 1118350891712086211573785)
            ·
              refine ⟨838763168784064658680339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118350891712086211573785 838763168784064658680339)
              ·
                refine ⟨1258144753176096988020509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838763168784064658680339 1258144753176096988020509)
                ·
                  refine ⟨471804282441036370507691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258144753176096988020509 471804282441036370507691)
                  ·
                    rfl

theorem cell20_1033690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_1033690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033690 prefixEnd_1033690 := by exact prefixLift 1033690
  have htrace : WordTrace (prefixWord ++ tailWord_1033690) baseStart_1033690 baseEnd_1033690 := by
    simpa [prefixWord, tailWord_1033690, baseEnd_1033690] using wordTrace_append hprefix tailTrace_1033690
  have hstable : (prefixWord ++ tailWord_1033690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033690).length < 2 ^ (prefixWord ++ tailWord_1033690).sum := by decide
  have hdescent : baseEnd_1033690 < baseStart_1033690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033715 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_1033715 : Nat := 118140960795 + 1033715 * 2 ^ 59
def prefixEnd_1033715 : Nat := 4983230072969 + 3 ^ 40 * 1033715 * 2
def baseEnd_1033715 : Nat := 471815693122247394674255

theorem tailTrace_1033715 : CollatzResearch.WordTrace tailWord_1033715 prefixEnd_1033715 471815693122247394674255 := by
  unfold tailWord_1033715
  simp only [CollatzResearch.WordTrace]
  refine ⟨37702683450034574311686599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25135122300023049541124399 37702683450034574311686599)
  ·
    refine ⟨56554025175051861467529899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37702683450034574311686599 56554025175051861467529899)
    ·
      refine ⟨84831037762577792201294849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56554025175051861467529899 84831037762577792201294849)
      ·
        refine ⟨63623278321933344150971137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84831037762577792201294849 63623278321933344150971137)
        ·
          refine ⟨47717458741450008113228353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63623278321933344150971137 47717458741450008113228353)
          ·
            refine ⟨35788094056087506084921265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47717458741450008113228353 35788094056087506084921265)
            ·
              refine ⟨26841070542065629563690949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35788094056087506084921265 26841070542065629563690949)
              ·
                refine ⟨5032700726637305543192053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26841070542065629563690949 5032700726637305543192053)
                ·
                  refine ⟨471815693122247394674255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032700726637305543192053 471815693122247394674255)
                  ·
                    rfl

theorem cell20_1033715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_1033715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033715 prefixEnd_1033715 := by exact prefixLift 1033715
  have htrace : WordTrace (prefixWord ++ tailWord_1033715) baseStart_1033715 baseEnd_1033715 := by
    simpa [prefixWord, tailWord_1033715, baseEnd_1033715] using wordTrace_append hprefix tailTrace_1033715
  have hstable : (prefixWord ++ tailWord_1033715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033715).length < 2 ^ (prefixWord ++ tailWord_1033715).sum := by decide
  have hdescent : baseEnd_1033715 < baseStart_1033715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033735 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 2]
def baseStart_1033735 : Nat := 118140960795 + 1033735 * 2 ^ 59
def prefixEnd_1033735 : Nat := 4983230072969 + 3 ^ 40 * 1033735 * 2
def baseEnd_1033735 : Nat := 471824821667216214007507

theorem tailTrace_1033735 : CollatzResearch.WordTrace tailWord_1033735 prefixEnd_1033735 471824821667216214007507 := by
  unfold tailWord_1033735
  simp only [CollatzResearch.WordTrace]
  refine ⟨37703412909962117727414659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25135608606641411818276439 37703412909962117727414659)
  ·
    refine ⟨56555119364943176591121989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37703412909962117727414659 56555119364943176591121989)
    ·
      refine ⟨10604084880926845610835373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56555119364943176591121989 10604084880926845610835373)
      ·
        refine ⟨3976531830347567104063265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10604084880926845610835373 3976531830347567104063265)
        ·
          refine ⟨2982398872760675328047449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3976531830347567104063265 2982398872760675328047449)
          ·
            refine ⟨2236799154570506496035587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2982398872760675328047449 2236799154570506496035587)
            ·
              refine ⟨3355198731855759744053381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236799154570506496035587 3355198731855759744053381)
              ·
                refine ⟨629099762222954952010009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3355198731855759744053381 629099762222954952010009)
                ·
                  refine ⟨471824821667216214007507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629099762222954952010009 471824821667216214007507)
                  ·
                    rfl

theorem cell20_1033735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 2].length) (baseStart_1033735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033735 prefixEnd_1033735 := by exact prefixLift 1033735
  have htrace : WordTrace (prefixWord ++ tailWord_1033735) baseStart_1033735 baseEnd_1033735 := by
    simpa [prefixWord, tailWord_1033735, baseEnd_1033735] using wordTrace_append hprefix tailTrace_1033735
  have hstable : (prefixWord ++ tailWord_1033735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033735).length < 2 ^ (prefixWord ++ tailWord_1033735).sum := by decide
  have hdescent : baseEnd_1033735 < baseStart_1033735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033742 : List Nat := [4, 1, 1, 2, 4, 2, 1, 5]
def baseStart_1033742 : Nat := 118140960795 + 1033742 * 2 ^ 59
def prefixEnd_1033742 : Nat := 4983230072969 + 3 ^ 40 * 1033742 * 2
def baseEnd_1033742 : Nat := 157276005552651766924715

theorem tailTrace_1033742 : CollatzResearch.WordTrace tailWord_1033742 prefixEnd_1033742 157276005552651766924715 := by
  unfold tailWord_1033742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712958527617094740364935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25135778813957838615279653 4712958527617094740364935)
  ·
    refine ⟨7069437791425642110547403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4712958527617094740364935 7069437791425642110547403)
    ·
      refine ⟨10604156687138463165821105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7069437791425642110547403 10604156687138463165821105)
      ·
        refine ⟨7953117515353847374365829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10604156687138463165821105 7953117515353847374365829)
        ·
          refine ⟨1491209534128846382693593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7953117515353847374365829 1491209534128846382693593)
          ·
            refine ⟨1118407150596634787020195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1491209534128846382693593 1118407150596634787020195)
            ·
              refine ⟨1677610725894952180530293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118407150596634787020195 1677610725894952180530293)
              ·
                refine ⟨157276005552651766924715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677610725894952180530293 157276005552651766924715)
                ·
                  rfl

theorem cell20_1033742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_1033742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033742 prefixEnd_1033742 := by exact prefixLift 1033742
  have htrace : WordTrace (prefixWord ++ tailWord_1033742) baseStart_1033742 baseEnd_1033742 := by
    simpa [prefixWord, tailWord_1033742, baseEnd_1033742] using wordTrace_append hprefix tailTrace_1033742
  have hstable : (prefixWord ++ tailWord_1033742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033742).length < 2 ^ (prefixWord ++ tailWord_1033742).sum := by decide
  have hdescent : baseEnd_1033742 < baseStart_1033742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033770 : List Nat := [3, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1033770 : Nat := 118140960795 + 1033770 * 2 ^ 59
def prefixEnd_1033770 : Nat := 4983230072969 + 3 ^ 40 * 1033770 * 2
def baseEnd_1033770 : Nat := 471840796620911647840697

theorem tailTrace_1033770 : CollatzResearch.WordTrace tailWord_1033770 prefixEnd_1033770 471840796620911647840697 := by
  unfold tailWord_1033770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9426172366208829676234691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25136459643223545803292509 9426172366208829676234691)
  ·
    refine ⟨14139258549313244514352037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9426172366208829676234691 14139258549313244514352037)
    ·
      refine ⟨2651110977996233346441007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14139258549313244514352037 2651110977996233346441007)
      ·
        refine ⟨3976666466994350019661511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651110977996233346441007 3976666466994350019661511)
        ·
          refine ⟨5964999700491525029492267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976666466994350019661511 5964999700491525029492267)
          ·
            refine ⟨8947499550737287544238401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964999700491525029492267 8947499550737287544238401)
            ·
              refine ⟨6710624663052965658178801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8947499550737287544238401 6710624663052965658178801)
              ·
                refine ⟨5032968497289724243634101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710624663052965658178801 5032968497289724243634101)
                ·
                  refine ⟨471840796620911647840697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032968497289724243634101 471840796620911647840697)
                  ·
                    rfl

theorem cell20_1033770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1033770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033770 prefixEnd_1033770 := by exact prefixLift 1033770
  have htrace : WordTrace (prefixWord ++ tailWord_1033770) baseStart_1033770 baseEnd_1033770 := by
    simpa [prefixWord, tailWord_1033770, baseEnd_1033770] using wordTrace_append hprefix tailTrace_1033770
  have hstable : (prefixWord ++ tailWord_1033770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033770).length < 2 ^ (prefixWord ++ tailWord_1033770).sum := by decide
  have hdescent : baseEnd_1033770 < baseStart_1033770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033784 : List Nat := [2, 1, 2, 1, 4, 3, 7]
def baseStart_1033784 : Nat := 118140960795 + 1033784 * 2 ^ 59
def prefixEnd_1033784 : Nat := 4983230072969 + 3 ^ 40 * 1033784 * 2
def baseEnd_1033784 : Nat := 52427465178043313485997

theorem tailTrace_1033784 : CollatzResearch.WordTrace tailWord_1033784 prefixEnd_1033784 52427465178043313485997 := by
  unfold tailWord_1033784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18852600043392299547974203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25136800057856399397298937 18852600043392299547974203)
  ·
    refine ⟨28278900065088449321961305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18852600043392299547974203 28278900065088449321961305)
    ·
      refine ⟨21209175048816336991470979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28278900065088449321961305 21209175048816336991470979)
      ·
        refine ⟨31813762573224505487206469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21209175048816336991470979 31813762573224505487206469)
        ·
          refine ⟨5965080482479594778851213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31813762573224505487206469 5965080482479594778851213)
          ·
            refine ⟨2236905180929848042069205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5965080482479594778851213 2236905180929848042069205)
            ·
              refine ⟨52427465178043313485997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2236905180929848042069205 52427465178043313485997)
              ·
                rfl

theorem cell20_1033784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 7].length) (baseStart_1033784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033784 prefixEnd_1033784 := by exact prefixLift 1033784
  have htrace : WordTrace (prefixWord ++ tailWord_1033784) baseStart_1033784 baseEnd_1033784 := by
    simpa [prefixWord, tailWord_1033784, baseEnd_1033784] using wordTrace_append hprefix tailTrace_1033784
  have hstable : (prefixWord ++ tailWord_1033784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033784).length < 2 ^ (prefixWord ++ tailWord_1033784).sum := by decide
  have hdescent : baseEnd_1033784 < baseStart_1033784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033815 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_1033815 : Nat := 118140960795 + 1033815 * 2 ^ 59
def prefixEnd_1033815 : Nat := 4983230072969 + 3 ^ 40 * 1033815 * 2
def baseEnd_1033815 : Nat := 471861335847091491340513

theorem tailTrace_1033815 : CollatzResearch.WordTrace tailWord_1033815 prefixEnd_1033815 471861335847091491340513 := by
  unfold tailWord_1033815
  simp only [CollatzResearch.WordTrace]
  refine ⟨37706330749672291390326899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25137553833114860926884599 37706330749672291390326899)
  ·
    refine ⟨56559496124508437085490349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37706330749672291390326899 56559496124508437085490349)
    ·
      refine ⟨21209811046690663907058881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56559496124508437085490349 21209811046690663907058881)
      ·
        refine ⟨15907358285017997930294161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21209811046690663907058881 15907358285017997930294161)
        ·
          refine ⟨11930518713763498447720621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15907358285017997930294161 11930518713763498447720621)
          ·
            refine ⟨4473944517661311917895233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11930518713763498447720621 4473944517661311917895233)
            ·
              refine ⟨3355458388245983938421425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4473944517661311917895233 3355458388245983938421425)
              ·
                refine ⟨2516593791184487953816069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3355458388245983938421425 2516593791184487953816069)
                ·
                  refine ⟨471861335847091491340513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516593791184487953816069 471861335847091491340513)
                  ·
                    rfl

theorem cell20_1033815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_1033815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033815 prefixEnd_1033815 := by exact prefixLift 1033815
  have htrace : WordTrace (prefixWord ++ tailWord_1033815) baseStart_1033815 baseEnd_1033815 := by
    simpa [prefixWord, tailWord_1033815, baseEnd_1033815] using wordTrace_append hprefix tailTrace_1033815
  have hstable : (prefixWord ++ tailWord_1033815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033815).length < 2 ^ (prefixWord ++ tailWord_1033815).sum := by decide
  have hdescent : baseEnd_1033815 < baseStart_1033815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033849 : List Nat := [1, 2, 1, 3, 3, 1, 5, 2, 2]
def baseStart_1033849 : Nat := 118140960795 + 1033849 * 2 ^ 59
def prefixEnd_1033849 : Nat := 4983230072969 + 3 ^ 40 * 1033849 * 2
def baseEnd_1033849 : Nat := 471876854373538484207041

theorem tailTrace_1033849 : CollatzResearch.WordTrace tailWord_1033849 prefixEnd_1033849 471876854373538484207041 := by
  unfold tailWord_1033849
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707570831549115197064601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25138380554366076798043067 37707570831549115197064601)
  ·
    refine ⟨28280678123661836397798451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37707570831549115197064601 28280678123661836397798451)
    ·
      refine ⟨42421017185492754596697677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28280678123661836397798451 42421017185492754596697677)
      ·
        refine ⟨15907881444559782973761629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42421017185492754596697677 15907881444559782973761629)
        ·
          refine ⟨5965455541709918615160611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15907881444559782973761629 5965455541709918615160611)
          ·
            refine ⟨8948183312564877922740917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965455541709918615160611 8948183312564877922740917)
            ·
              refine ⟨838892185552957305256961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8948183312564877922740917 838892185552957305256961)
              ·
                refine ⟨629169139164717978942721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838892185552957305256961 629169139164717978942721)
                ·
                  refine ⟨471876854373538484207041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629169139164717978942721 471876854373538484207041)
                  ·
                    rfl

theorem cell20_1033849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_1033849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033849 prefixEnd_1033849 := by exact prefixLift 1033849
  have htrace : WordTrace (prefixWord ++ tailWord_1033849) baseStart_1033849 baseEnd_1033849 := by
    simpa [prefixWord, tailWord_1033849, baseEnd_1033849] using wordTrace_append hprefix tailTrace_1033849
  have hstable : (prefixWord ++ tailWord_1033849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033849).length < 2 ^ (prefixWord ++ tailWord_1033849).sum := by decide
  have hdescent : baseEnd_1033849 < baseStart_1033849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033863 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 3]
def baseStart_1033863 : Nat := 118140960795 + 1033863 * 2 ^ 59
def prefixEnd_1033863 : Nat := 4983230072969 + 3 ^ 40 * 1033863 * 2
def baseEnd_1033863 : Nat := 471883244355016657740317

theorem tailTrace_1033863 : CollatzResearch.WordTrace tailWord_1033863 prefixEnd_1033863 471883244355016657740317 := by
  unfold tailWord_1033863
  simp only [CollatzResearch.WordTrace]
  refine ⟨37708081453498395588074243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25138720968998930392049495 37708081453498395588074243)
  ·
    refine ⟨56562122180247593382111365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37708081453498395588074243 56562122180247593382111365)
    ·
      refine ⟨10605397908796423759145881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56562122180247593382111365 10605397908796423759145881)
      ·
        refine ⟨7954048431597317819359411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10605397908796423759145881 7954048431597317819359411)
        ·
          refine ⟨11931072647395976729039117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7954048431597317819359411 11931072647395976729039117)
          ·
            refine ⟨4474152242773491273389669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11931072647395976729039117 4474152242773491273389669)
            ·
              refine ⟨838903545520029613760563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4474152242773491273389669 838903545520029613760563)
              ·
                refine ⟨1258355318280044420640845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838903545520029613760563 1258355318280044420640845)
                ·
                  refine ⟨471883244355016657740317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258355318280044420640845 471883244355016657740317)
                  ·
                    rfl

theorem cell20_1033863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 3].length) (baseStart_1033863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033863 prefixEnd_1033863 := by exact prefixLift 1033863
  have htrace : WordTrace (prefixWord ++ tailWord_1033863) baseStart_1033863 baseEnd_1033863 := by
    simpa [prefixWord, tailWord_1033863, baseEnd_1033863] using wordTrace_append hprefix tailTrace_1033863
  have hstable : (prefixWord ++ tailWord_1033863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033863).length < 2 ^ (prefixWord ++ tailWord_1033863).sum := by decide
  have hdescent : baseEnd_1033863 < baseStart_1033863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033898 : List Nat := [3, 1, 5, 11]
def baseStart_1033898 : Nat := 118140960795 + 1033898 * 2 ^ 59
def prefixEnd_1033898 : Nat := 4983230072969 + 3 ^ 40 * 1033898 * 2
def baseEnd_1033898 : Nat := 1941972095920625891249

theorem tailTrace_1033898 : CollatzResearch.WordTrace tailWord_1033898 prefixEnd_1033898 1941972095920625891249 := by
  unfold tailWord_1033898
  simp only [CollatzResearch.WordTrace]
  refine ⟨9427339502092899141399587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25139572005581064377065565 9427339502092899141399587)
  ·
    refine ⟨14141009253139348712099381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9427339502092899141399587 14141009253139348712099381)
    ·
      refine ⟨1325719617481813941759317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14141009253139348712099381 1325719617481813941759317)
      ·
        refine ⟨1941972095920625891249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1325719617481813941759317 1941972095920625891249)
        ·
          rfl

theorem cell20_1033898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 11].length) (baseStart_1033898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033898 prefixEnd_1033898 := by exact prefixLift 1033898
  have htrace : WordTrace (prefixWord ++ tailWord_1033898) baseStart_1033898 baseEnd_1033898 := by
    simpa [prefixWord, tailWord_1033898, baseEnd_1033898] using wordTrace_append hprefix tailTrace_1033898
  have hstable : (prefixWord ++ tailWord_1033898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033898).length < 2 ^ (prefixWord ++ tailWord_1033898).sum := by decide
  have hdescent : baseEnd_1033898 < baseStart_1033898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033901 : List Nat := [1, 5, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1033901 : Nat := 118140960795 + 1033901 * 2 ^ 59
def prefixEnd_1033901 : Nat := 4983230072969 + 3 ^ 40 * 1033901 * 2
def baseEnd_1033901 : Nat := 471900588590457414473495

theorem tailTrace_1033901 : CollatzResearch.WordTrace tailWord_1033901 prefixEnd_1033901 471900588590457414473495 := by
  unfold tailWord_1033901
  simp only [CollatzResearch.WordTrace]
  refine ⟨37709467427360728077957557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25139644951573818718638371 37709467427360728077957557)
  ·
    refine ⟨3535262571315068257308521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37709467427360728077957557 3535262571315068257308521)
    ·
      refine ⟨2651446928486301192981391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3535262571315068257308521 2651446928486301192981391)
      ·
        refine ⟨3977170392729451789472087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651446928486301192981391 3977170392729451789472087)
        ·
          refine ⟨5965755589094177684208131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3977170392729451789472087 5965755589094177684208131)
          ·
            refine ⟨8948633383641266526312197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5965755589094177684208131 8948633383641266526312197)
            ·
              refine ⟨1677868759432737473683537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8948633383641266526312197 1677868759432737473683537)
              ·
                refine ⟨1258401569574553105262653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677868759432737473683537 1258401569574553105262653)
                ·
                  refine ⟨471900588590457414473495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258401569574553105262653 471900588590457414473495)
                  ·
                    rfl

theorem cell20_1033901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1033901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033901 prefixEnd_1033901 := by exact prefixLift 1033901
  have htrace : WordTrace (prefixWord ++ tailWord_1033901) baseStart_1033901 baseEnd_1033901 := by
    simpa [prefixWord, tailWord_1033901, baseEnd_1033901] using wordTrace_append hprefix tailTrace_1033901
  have hstable : (prefixWord ++ tailWord_1033901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033901).length < 2 ^ (prefixWord ++ tailWord_1033901).sum := by decide
  have hdescent : baseEnd_1033901 < baseStart_1033901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033912 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_1033912 : Nat := 118140960795 + 1033912 * 2 ^ 59
def prefixEnd_1033912 : Nat := 4983230072969 + 3 ^ 40 * 1033912 * 2
def baseEnd_1033912 : Nat := 471905609290190265106783

theorem tailTrace_1033912 : CollatzResearch.WordTrace tailWord_1033912 prefixEnd_1033912 471905609290190265106783 := by
  unfold tailWord_1033912
  simp only [CollatzResearch.WordTrace]
  refine ⟨18854934315160438478303995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25139912420213917971071993 18854934315160438478303995)
  ·
    refine ⟨28282401472740657717455993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18854934315160438478303995 28282401472740657717455993)
    ·
      refine ⟨21211801104555493288091995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28282401472740657717455993 21211801104555493288091995)
      ·
        refine ⟨31817701656833239932137993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21211801104555493288091995 31817701656833239932137993)
        ·
          refine ⟨23863276242624929949103495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31817701656833239932137993 23863276242624929949103495)
          ·
            refine ⟨35794914363937394923655243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23863276242624929949103495 35794914363937394923655243)
            ·
              refine ⟨53692371545906092385482865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35794914363937394923655243 53692371545906092385482865)
              ·
                refine ⟨40269278659429569289112149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53692371545906092385482865 40269278659429569289112149)
                ·
                  refine ⟨471905609290190265106783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40269278659429569289112149 471905609290190265106783)
                  ·
                    rfl

theorem cell20_1033912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_1033912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033912 prefixEnd_1033912 := by exact prefixLift 1033912
  have htrace : WordTrace (prefixWord ++ tailWord_1033912) baseStart_1033912 baseEnd_1033912 := by
    simpa [prefixWord, tailWord_1033912, baseEnd_1033912] using wordTrace_append hprefix tailTrace_1033912
  have hstable : (prefixWord ++ tailWord_1033912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033912).length < 2 ^ (prefixWord ++ tailWord_1033912).sum := by decide
  have hdescent : baseEnd_1033912 < baseStart_1033912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033932 : List Nat := [2, 2, 1, 5, 2, 1, 3, 4]
def baseStart_1033932 : Nat := 118140960795 + 1033932 * 2 ^ 59
def prefixEnd_1033932 : Nat := 4983230072969 + 3 ^ 40 * 1033932 * 2
def baseEnd_1033932 : Nat := 157304912611719694813345

theorem tailTrace_1033932 : CollatzResearch.WordTrace tailWord_1033932 prefixEnd_1033932 157304912611719694813345 := by
  unfold tailWord_1033932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855299045124210186168025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25140398726832280248224033 18855299045124210186168025)
  ·
    refine ⟨14141474283843157639626019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18855299045124210186168025 14141474283843157639626019)
    ·
      refine ⟨21212211425764736459439029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14141474283843157639626019 21212211425764736459439029)
      ·
        refine ⟨1988644821165444043072409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21212211425764736459439029 1988644821165444043072409)
        ·
          refine ⟨1491483615874083032304307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988644821165444043072409 1491483615874083032304307)
          ·
            refine ⟨2237225423811124548456461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491483615874083032304307 2237225423811124548456461)
            ·
              refine ⟨838959533929171705671173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2237225423811124548456461 838959533929171705671173)
              ·
                refine ⟨157304912611719694813345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 838959533929171705671173 157304912611719694813345)
                ·
                  rfl

theorem cell20_1033932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_1033932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033932 prefixEnd_1033932 := by exact prefixLift 1033932
  have htrace : WordTrace (prefixWord ++ tailWord_1033932) baseStart_1033932 baseEnd_1033932 := by
    simpa [prefixWord, tailWord_1033932, baseEnd_1033932] using wordTrace_append hprefix tailTrace_1033932
  have hstable : (prefixWord ++ tailWord_1033932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033932).length < 2 ^ (prefixWord ++ tailWord_1033932).sum := by decide
  have hdescent : baseEnd_1033932 < baseStart_1033932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033943 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_1033943 : Nat := 118140960795 + 1033943 * 2 ^ 59
def prefixEnd_1033943 : Nat := 4983230072969 + 3 ^ 40 * 1033943 * 2
def baseEnd_1033943 : Nat := 471919758534891935073323

theorem tailTrace_1033943 : CollatzResearch.WordTrace tailWord_1033943 prefixEnd_1033943 471919758534891935073323 := by
  unfold tailWord_1033943
  simp only [CollatzResearch.WordTrace]
  refine ⟨37710999293208569250986483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25140666195472379500657655 37710999293208569250986483)
  ·
    refine ⟨56566498939812853876479725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37710999293208569250986483 56566498939812853876479725)
    ·
      refine ⟨21212437102429820203679897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56566498939812853876479725 21212437102429820203679897)
      ·
        refine ⟨15909327826822365152759923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21212437102429820203679897 15909327826822365152759923)
        ·
          refine ⟨23863991740233547729139885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15909327826822365152759923 23863991740233547729139885)
          ·
            refine ⟨8948996902587580398427457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23863991740233547729139885 8948996902587580398427457)
            ·
              refine ⟨6711747676940685298820593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8948996902587580398427457 6711747676940685298820593)
              ·
                refine ⟨5033810757705513974115445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711747676940685298820593 5033810757705513974115445)
                ·
                  refine ⟨471919758534891935073323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033810757705513974115445 471919758534891935073323)
                  ·
                    rfl

theorem cell20_1033943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_1033943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033943 prefixEnd_1033943 := by exact prefixLift 1033943
  have htrace : WordTrace (prefixWord ++ tailWord_1033943) baseStart_1033943 baseEnd_1033943 := by
    simpa [prefixWord, tailWord_1033943, baseEnd_1033943] using wordTrace_append hprefix tailTrace_1033943
  have hstable : (prefixWord ++ tailWord_1033943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033943).length < 2 ^ (prefixWord ++ tailWord_1033943).sum := by decide
  have hdescent : baseEnd_1033943 < baseStart_1033943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033946 : List Nat := [3, 1, 1, 2, 2, 3, 1, 5, 2]
def baseStart_1033946 : Nat := 118140960795 + 1033946 * 2 ^ 59
def prefixEnd_1033946 : Nat := 4983230072969 + 3 ^ 40 * 1033946 * 2
def baseEnd_1033946 : Nat := 471921127816637257973311

theorem tailTrace_1033946 : CollatzResearch.WordTrace tailWord_1033946 prefixEnd_1033946 471921127816637257973311 := by
  unfold tailWord_1033946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9427777178049425190836423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25140739141465133842230461 9427777178049425190836423)
  ·
    refine ⟨14141665767074137786254635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9427777178049425190836423 14141665767074137786254635)
    ·
      refine ⟨21212498650611206679381953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14141665767074137786254635 21212498650611206679381953)
      ·
        refine ⟨15909373987958405009536465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21212498650611206679381953 15909373987958405009536465)
        ·
          refine ⟨11932030490968803757152349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15909373987958405009536465 11932030490968803757152349)
          ·
            refine ⟨4474511434113301408932131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11932030490968803757152349 4474511434113301408932131)
            ·
              refine ⟨6711767151169952113398197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474511434113301408932131 6711767151169952113398197)
              ·
                refine ⟨629228170422183010631081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6711767151169952113398197 629228170422183010631081)
                ·
                  refine ⟨471921127816637257973311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629228170422183010631081 471921127816637257973311)
                  ·
                    rfl

theorem cell20_1033946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_1033946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033946 prefixEnd_1033946 := by exact prefixLift 1033946
  have htrace : WordTrace (prefixWord ++ tailWord_1033946) baseStart_1033946 baseEnd_1033946 := by
    simpa [prefixWord, tailWord_1033946, baseEnd_1033946] using wordTrace_append hprefix tailTrace_1033946
  have hstable : (prefixWord ++ tailWord_1033946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033946).length < 2 ^ (prefixWord ++ tailWord_1033946).sum := by decide
  have hdescent : baseEnd_1033946 < baseStart_1033946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033960 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 5]
def baseStart_1033960 : Nat := 118140960795 + 1033960 * 2 ^ 59
def prefixEnd_1033960 : Nat := 4983230072969 + 3 ^ 40 * 1033960 * 2
def baseEnd_1033960 : Nat := 471927517798115431506587

theorem tailTrace_1033960 : CollatzResearch.WordTrace tailWord_1033960 prefixEnd_1033960 471927517798115431506587 := by
  unfold tailWord_1033960
  simp only [CollatzResearch.WordTrace]
  refine ⟨18855809667073490577177667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25141079556097987436236889 18855809667073490577177667)
  ·
    refine ⟨28283714500610235865766501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18855809667073490577177667 28283714500610235865766501)
    ·
      refine ⟨5303196468864419224831219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28283714500610235865766501 5303196468864419224831219)
      ·
        refine ⟨7954794703296628837246829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5303196468864419224831219 7954794703296628837246829)
        ·
          refine ⟨2983048013736235813967561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7954794703296628837246829 2983048013736235813967561)
          ·
            refine ⟨2237286010302176860475671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983048013736235813967561 2237286010302176860475671)
            ·
              refine ⟨3355929015453265290713507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237286010302176860475671 3355929015453265290713507)
              ·
                refine ⟨5033893523179897936070261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355929015453265290713507 5033893523179897936070261)
                ·
                  refine ⟨471927517798115431506587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033893523179897936070261 471927517798115431506587)
                  ·
                    rfl

theorem cell20_1033960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 5].length) (baseStart_1033960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033960 prefixEnd_1033960 := by exact prefixLift 1033960
  have htrace : WordTrace (prefixWord ++ tailWord_1033960) baseStart_1033960 baseEnd_1033960 := by
    simpa [prefixWord, tailWord_1033960, baseEnd_1033960] using wordTrace_append hprefix tailTrace_1033960
  have hstable : (prefixWord ++ tailWord_1033960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033960).length < 2 ^ (prefixWord ++ tailWord_1033960).sum := by decide
  have hdescent : baseEnd_1033960 < baseStart_1033960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033967 : List Nat := [1, 1, 2, 1, 5, 1, 4, 1, 4]
def baseStart_1033967 : Nat := 118140960795 + 1033967 * 2 ^ 59
def prefixEnd_1033967 : Nat := 4983230072969 + 3 ^ 40 * 1033967 * 2
def baseEnd_1033967 : Nat := 471930712788854518273225

theorem tailTrace_1033967 : CollatzResearch.WordTrace tailWord_1033967 prefixEnd_1033967 471930712788854518273225 := by
  unfold tailWord_1033967
  simp only [CollatzResearch.WordTrace]
  refine ⟨37711874645121621349860155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25141249763414414233240103 37711874645121621349860155)
  ·
    refine ⟨56567811967682432024790233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37711874645121621349860155 56567811967682432024790233)
    ·
      refine ⟨42425858975761824018592675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56567811967682432024790233 42425858975761824018592675)
      ·
        refine ⟨63638788463642736027889013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42425858975761824018592675 63638788463642736027889013)
        ·
          refine ⟨5966136418466506502614595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63638788463642736027889013 5966136418466506502614595)
          ·
            refine ⟨8949204627699759753921893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5966136418466506502614595 8949204627699759753921893)
            ·
              refine ⟨1677975867693704953860355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8949204627699759753921893 1677975867693704953860355)
              ·
                refine ⟨2516963801540557430790533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677975867693704953860355 2516963801540557430790533)
                ·
                  refine ⟨471930712788854518273225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516963801540557430790533 471930712788854518273225)
                  ·
                    rfl

theorem cell20_1033967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_1033967 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033967 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033967 prefixEnd_1033967 := by exact prefixLift 1033967
  have htrace : WordTrace (prefixWord ++ tailWord_1033967) baseStart_1033967 baseEnd_1033967 := by
    simpa [prefixWord, tailWord_1033967, baseEnd_1033967] using wordTrace_append hprefix tailTrace_1033967
  have hstable : (prefixWord ++ tailWord_1033967).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033967).length < 2 ^ (prefixWord ++ tailWord_1033967).sum := by decide
  have hdescent : baseEnd_1033967 < baseStart_1033967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1033991 : List Nat := [1, 1, 4, 4, 2, 1, 1, 6]
def baseStart_1033991 : Nat := 118140960795 + 1033991 * 2 ^ 59
def prefixEnd_1033991 : Nat := 4983230072969 + 3 ^ 40 * 1033991 * 2
def baseEnd_1033991 : Nat := 157313889014272367157709

theorem tailTrace_1033991 : CollatzResearch.WordTrace tailWord_1033991 prefixEnd_1033991 157313889014272367157709 := by
  unfold tailWord_1033991
  simp only [CollatzResearch.WordTrace]
  refine ⟨37712749997034673448733827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25141833331356448965822551 37712749997034673448733827)
  ·
    refine ⟨56569124995552010173100741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37712749997034673448733827 56569124995552010173100741)
    ·
      refine ⟨10606710936666001907456389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56569124995552010173100741 10606710936666001907456389)
      ·
        refine ⟨1988758300624875357648073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10606710936666001907456389 1988758300624875357648073)
        ·
          refine ⟨1491568725468656518236055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988758300624875357648073 1491568725468656518236055)
          ·
            refine ⟨2237353088202984777354083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491568725468656518236055 2237353088202984777354083)
            ·
              refine ⟨3356029632304477166031125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237353088202984777354083 3356029632304477166031125)
              ·
                refine ⟨157313889014272367157709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3356029632304477166031125 157313889014272367157709)
                ·
                  rfl

theorem cell20_1033991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 6].length) (baseStart_1033991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1033991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1033991 prefixEnd_1033991 := by exact prefixLift 1033991
  have htrace : WordTrace (prefixWord ++ tailWord_1033991) baseStart_1033991 baseEnd_1033991 := by
    simpa [prefixWord, tailWord_1033991, baseEnd_1033991] using wordTrace_append hprefix tailTrace_1033991
  have hstable : (prefixWord ++ tailWord_1033991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1033991).length < 2 ^ (prefixWord ++ tailWord_1033991).sum := by decide
  have hdescent : baseEnd_1033991 < baseStart_1033991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1033991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034004 : List Nat := [2, 4, 4, 1, 2, 1, 6]
def baseStart_1034004 : Nat := 118140960795 + 1034004 * 2 ^ 59
def prefixEnd_1034004 : Nat := 4983230072969 + 3 ^ 40 * 1034004 * 2
def baseEnd_1034004 : Nat := 52438622288560759337749

theorem tailTrace_1034004 : CollatzResearch.WordTrace tailWord_1034004 prefixEnd_1034004 52438622288560759337749 := by
  unfold tailWord_1034004
  simp only [CollatzResearch.WordTrace]
  refine ⟨18856612072993788334478533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25142149430658384445971377 18856612072993788334478533)
  ·
    refine ⟨3535614763686335312714725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18856612072993788334478533 3535614763686335312714725)
    ·
      refine ⟨662927768191187871134011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3535614763686335312714725 662927768191187871134011)
      ·
        refine ⟨994391652286781806701017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662927768191187871134011 994391652286781806701017)
        ·
          refine ⟨745793739215086355025763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994391652286781806701017 745793739215086355025763)
          ·
            refine ⟨1118690608822629532538645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745793739215086355025763 1118690608822629532538645)
            ·
              refine ⟨52438622288560759337749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1118690608822629532538645 52438622288560759337749)
              ·
                rfl

theorem cell20_1034004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 6].length) (baseStart_1034004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034004 prefixEnd_1034004 := by exact prefixLift 1034004
  have htrace : WordTrace (prefixWord ++ tailWord_1034004) baseStart_1034004 baseEnd_1034004 := by
    simpa [prefixWord, tailWord_1034004, baseEnd_1034004] using wordTrace_append hprefix tailTrace_1034004
  have hstable : (prefixWord ++ tailWord_1034004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034004).length < 2 ^ (prefixWord ++ tailWord_1034004).sum := by decide
  have hdescent : baseEnd_1034004 < baseStart_1034004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034014 : List Nat := [4, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1034014 : Nat := 118140960795 + 1034014 * 2 ^ 59
def prefixEnd_1034014 : Nat := 4983230072969 + 3 ^ 40 * 1034014 * 2
def baseEnd_1034014 : Nat := 471952164869531243706367

theorem tailTrace_1034014 : CollatzResearch.WordTrace tailWord_1034014 prefixEnd_1034014 471952164869531243706367 := by
  unfold tailWord_1034014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4714198609493918547102637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25142392583967565584547397 4714198609493918547102637)
  ·
    refine ⟨1767824478560219455163489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4714198609493918547102637 1767824478560219455163489)
    ·
      refine ⟨1325868358920164591372617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1767824478560219455163489 1325868358920164591372617)
      ·
        refine ⟨994401269190123443529463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1325868358920164591372617 994401269190123443529463)
        ·
          refine ⟨1491601903785185165294195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994401269190123443529463 1491601903785185165294195)
          ·
            refine ⟨2237402855677777747941293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491601903785185165294195 2237402855677777747941293)
            ·
              refine ⟨839026070879166655477985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2237402855677777747941293 839026070879166655477985)
              ·
                refine ⟨629269553159374991608489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839026070879166655477985 629269553159374991608489)
                ·
                  refine ⟨471952164869531243706367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629269553159374991608489 471952164869531243706367)
                  ·
                    rfl

theorem cell20_1034014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1034014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034014 prefixEnd_1034014 := by exact prefixLift 1034014
  have htrace : WordTrace (prefixWord ++ tailWord_1034014) baseStart_1034014 baseEnd_1034014 := by
    simpa [prefixWord, tailWord_1034014, baseEnd_1034014] using wordTrace_append hprefix tailTrace_1034014
  have hstable : (prefixWord ++ tailWord_1034014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034014).length < 2 ^ (prefixWord ++ tailWord_1034014).sum := by decide
  have hdescent : baseEnd_1034014 < baseStart_1034014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034019 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_1034019 : Nat := 118140960795 + 1034019 * 2 ^ 59
def prefixEnd_1034019 : Nat := 4983230072969 + 3 ^ 40 * 1034019 * 2
def baseEnd_1034019 : Nat := 471954447005773448539679

theorem tailTrace_1034019 : CollatzResearch.WordTrace tailWord_1034019 prefixEnd_1034019 471954447005773448539679 := by
  unfold tailWord_1034019
  simp only [CollatzResearch.WordTrace]
  refine ⟨37713771240933234230753111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25142514160622156153835407 37713771240933234230753111)
  ·
    refine ⟨56570656861399851346129667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37713771240933234230753111 56570656861399851346129667)
    ·
      refine ⟨84855985292099777019194501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56570656861399851346129667 84855985292099777019194501)
      ·
        refine ⟨15910497242268708191098969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84855985292099777019194501 15910497242268708191098969)
        ·
          refine ⟨11932872931701531143324227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15910497242268708191098969 11932872931701531143324227)
          ·
            refine ⟨17899309397552296714986341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11932872931701531143324227 17899309397552296714986341)
            ·
              refine ⟨3356120512041055634059939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17899309397552296714986341 3356120512041055634059939)
              ·
                refine ⟨5034180768061583451089909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356120512041055634059939 5034180768061583451089909)
                ·
                  refine ⟨471954447005773448539679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5034180768061583451089909 471954447005773448539679)
                  ·
                    rfl

theorem cell20_1034019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_1034019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034019 prefixEnd_1034019 := by exact prefixLift 1034019
  have htrace : WordTrace (prefixWord ++ tailWord_1034019) baseStart_1034019 baseEnd_1034019 := by
    simpa [prefixWord, tailWord_1034019, baseEnd_1034019] using wordTrace_append hprefix tailTrace_1034019
  have hstable : (prefixWord ++ tailWord_1034019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034019).length < 2 ^ (prefixWord ++ tailWord_1034019).sum := by decide
  have hdescent : baseEnd_1034019 < baseStart_1034019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034071 : List Nat := [1, 1, 3, 2, 13]
def baseStart_1034071 : Nat := 118140960795 + 1034071 * 2 ^ 59
def prefixEnd_1034071 : Nat := 4983230072969 + 3 ^ 40 * 1034071 * 2
def baseEnd_1034071 : Nat := 5826891126206078750693

theorem tailTrace_1034071 : CollatzResearch.WordTrace tailWord_1034071 prefixEnd_1034071 5826891126206078750693 := by
  unfold tailWord_1034071
  simp only [CollatzResearch.WordTrace]
  refine ⟨37715667836744847111646067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25143778557829898074430711 37715667836744847111646067)
  ·
    refine ⟨56573501755117270667469101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37715667836744847111646067 56573501755117270667469101)
    ·
      refine ⟨21215063158168976500300913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56573501755117270667469101 21215063158168976500300913)
      ·
        refine ⟨15911297368626732375225685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21215063158168976500300913 15911297368626732375225685)
        ·
          refine ⟨5826891126206078750693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15911297368626732375225685 5826891126206078750693)
          ·
            rfl

theorem cell20_1034071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 13].length) (baseStart_1034071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034071 prefixEnd_1034071 := by exact prefixLift 1034071
  have htrace : WordTrace (prefixWord ++ tailWord_1034071) baseStart_1034071 baseEnd_1034071 := by
    simpa [prefixWord, tailWord_1034071, baseEnd_1034071] using wordTrace_append hprefix tailTrace_1034071
  have hstable : (prefixWord ++ tailWord_1034071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034071).length < 2 ^ (prefixWord ++ tailWord_1034071).sum := by decide
  have hdescent : baseEnd_1034071 < baseStart_1034071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034074 : List Nat := [3, 1, 1, 2, 1, 3, 4, 2, 3]
def baseStart_1034074 : Nat := 118140960795 + 1034074 * 2 ^ 59
def prefixEnd_1034074 : Nat := 4983230072969 + 3 ^ 40 * 1034074 * 2
def baseEnd_1034074 : Nat := 471979550504437701706121

theorem tailTrace_1034074 : CollatzResearch.WordTrace tailWord_1034074 prefixEnd_1034074 471979550504437701706121 := by
  unfold tailWord_1034074
  simp only [CollatzResearch.WordTrace]
  refine ⟨9428944313933494656001319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25143851503822652416003517 9428944313933494656001319)
  ·
    refine ⟨14143416470900241984001979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9428944313933494656001319 14143416470900241984001979)
    ·
      refine ⟨21215124706350362976002969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14143416470900241984001979 21215124706350362976002969)
      ·
        refine ⟨15911343529762772232002227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21215124706350362976002969 15911343529762772232002227)
        ·
          refine ⟨23867015294644158348003341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15911343529762772232002227 23867015294644158348003341)
          ·
            refine ⟨8950130735491559380501253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23867015294644158348003341 8950130735491559380501253)
            ·
              refine ⟨1678149512904667383843985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8950130735491559380501253 1678149512904667383843985)
              ·
                refine ⟨1258612134678500537882989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678149512904667383843985 1258612134678500537882989)
                ·
                  refine ⟨471979550504437701706121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258612134678500537882989 471979550504437701706121)
                  ·
                    rfl

theorem cell20_1034074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_1034074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034074 prefixEnd_1034074 := by exact prefixLift 1034074
  have htrace : WordTrace (prefixWord ++ tailWord_1034074) baseStart_1034074 baseEnd_1034074 := by
    simpa [prefixWord, tailWord_1034074, baseEnd_1034074] using wordTrace_append hprefix tailTrace_1034074
  have hstable : (prefixWord ++ tailWord_1034074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034074).length < 2 ^ (prefixWord ++ tailWord_1034074).sum := by decide
  have hdescent : baseEnd_1034074 < baseStart_1034074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034084 : List Nat := [2, 3, 1, 1, 6, 1, 1, 5]
def baseStart_1034084 : Nat := 118140960795 + 1034084 * 2 ^ 59
def prefixEnd_1034084 : Nat := 4983230072969 + 3 ^ 40 * 1034084 * 2
def baseEnd_1034084 : Nat := 157328038258974037124249

theorem tailTrace_1034084 : CollatzResearch.WordTrace tailWord_1034084 prefixEnd_1034084 157328038258974037124249 := by
  unfold tailWord_1034084
  simp only [CollatzResearch.WordTrace]
  refine ⟨18858070992848875165934653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25144094657131833554579537 18858070992848875165934653)
  ·
    refine ⟨7071776622318328187225495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18858070992848875165934653 7071776622318328187225495)
    ·
      refine ⟨10607664933477492280838243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7071776622318328187225495 10607664933477492280838243)
      ·
        refine ⟨15911497400216238421257365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10607664933477492280838243 15911497400216238421257365)
        ·
          refine ⟨745851440635136175996439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15911497400216238421257365 745851440635136175996439)
          ·
            refine ⟨1118777160952704263994659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745851440635136175996439 1118777160952704263994659)
            ·
              refine ⟨1678165741429056395991989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118777160952704263994659 1678165741429056395991989)
              ·
                refine ⟨157328038258974037124249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1678165741429056395991989 157328038258974037124249)
                ·
                  rfl

theorem cell20_1034084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_1034084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034084 prefixEnd_1034084 := by exact prefixLift 1034084
  have htrace : WordTrace (prefixWord ++ tailWord_1034084) baseStart_1034084 baseEnd_1034084 := by
    simpa [prefixWord, tailWord_1034084, baseEnd_1034084] using wordTrace_append hprefix tailTrace_1034084
  have hstable : (prefixWord ++ tailWord_1034084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034084).length < 2 ^ (prefixWord ++ tailWord_1034084).sum := by decide
  have hdescent : baseEnd_1034084 < baseStart_1034084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034133 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_1034133 : Nat := 118140960795 + 1034133 * 2 ^ 59
def prefixEnd_1034133 : Nat := 4983230072969 + 3 ^ 40 * 1034133 * 2
def baseEnd_1034133 : Nat := 472006479712095718739213

theorem tailTrace_1034133 : CollatzResearch.WordTrace tailWord_1034133 prefixEnd_1034133 472006479712095718739213 := by
  unfold tailWord_1034133
  simp only [CollatzResearch.WordTrace]
  refine ⟨37717929162520231700403053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25145286108346821133602035 37717929162520231700403053)
  ·
    refine ⟨14144223435945086887651145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37717929162520231700403053 14144223435945086887651145)
    ·
      refine ⟨10608167576958815165738359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14144223435945086887651145 10608167576958815165738359)
      ·
        refine ⟨15912251365438222748607539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10608167576958815165738359 15912251365438222748607539)
        ·
          refine ⟨23868377048157334122911309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15912251365438222748607539 23868377048157334122911309)
          ·
            refine ⟨8950641393059000296091741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23868377048157334122911309 8950641393059000296091741)
            ·
              refine ⟨3356490522397125111034403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8950641393059000296091741 3356490522397125111034403)
              ·
                refine ⟨5034735783595687666551605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3356490522397125111034403 5034735783595687666551605)
                ·
                  refine ⟨472006479712095718739213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5034735783595687666551605 472006479712095718739213)
                  ·
                    rfl

theorem cell20_1034133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_1034133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034133 prefixEnd_1034133 := by exact prefixLift 1034133
  have htrace : WordTrace (prefixWord ++ tailWord_1034133) baseStart_1034133 baseEnd_1034133 := by
    simpa [prefixWord, tailWord_1034133, baseEnd_1034133] using wordTrace_append hprefix tailTrace_1034133
  have hstable : (prefixWord ++ tailWord_1034133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034133).length < 2 ^ (prefixWord ++ tailWord_1034133).sum := by decide
  have hdescent : baseEnd_1034133 < baseStart_1034133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034146 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 3]
def baseStart_1034146 : Nat := 118140960795 + 1034146 * 2 ^ 59
def prefixEnd_1034146 : Nat := 4983230072969 + 3 ^ 40 * 1034146 * 2
def baseEnd_1034146 : Nat := 472012413266325451305827

theorem tailTrace_1034146 : CollatzResearch.WordTrace tailWord_1034146 prefixEnd_1034146 472012413266325451305827 := by
  unfold tailWord_1034146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429600827868283730156573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25145602207648756613750861 9429600827868283730156573)
  ·
    refine ⟨3536100310450606398808715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9429600827868283730156573 3536100310450606398808715)
    ·
      refine ⟨5304150465675909598213073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3536100310450606398808715 5304150465675909598213073)
      ·
        refine ⟨3978112849256932198659805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5304150465675909598213073 3978112849256932198659805)
        ·
          refine ⟨1491792318471349574497427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3978112849256932198659805 1491792318471349574497427)
          ·
            refine ⟨2237688477707024361746141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491792318471349574497427 2237688477707024361746141)
            ·
              refine ⟨839133179140134135654803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2237688477707024361746141 839133179140134135654803)
              ·
                refine ⟨1258699768710201203482205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839133179140134135654803 1258699768710201203482205)
                ·
                  refine ⟨472012413266325451305827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258699768710201203482205 472012413266325451305827)
                  ·
                    rfl

theorem cell20_1034146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_1034146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034146 prefixEnd_1034146 := by exact prefixLift 1034146
  have htrace : WordTrace (prefixWord ++ tailWord_1034146) baseStart_1034146 baseEnd_1034146 := by
    simpa [prefixWord, tailWord_1034146, baseEnd_1034146] using wordTrace_append hprefix tailTrace_1034146
  have hstable : (prefixWord ++ tailWord_1034146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034146).length < 2 ^ (prefixWord ++ tailWord_1034146).sum := by decide
  have hdescent : baseEnd_1034146 < baseStart_1034146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034147 : List Nat := [1, 1, 1, 4, 1, 2, 1, 9]
def baseStart_1034147 : Nat := 118140960795 + 1034147 * 2 ^ 59
def prefixEnd_1034147 : Nat := 4983230072969 + 3 ^ 40 * 1034147 * 2
def baseEnd_1034147 : Nat := 157337623231191297424163

theorem tailTrace_1034147 : CollatzResearch.WordTrace tailWord_1034147 prefixEnd_1034147 157337623231191297424163 := by
  unfold tailWord_1034147
  simp only [CollatzResearch.WordTrace]
  refine ⟨37718439784469512091412695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25145626522979674727608463 37718439784469512091412695)
  ·
    refine ⟨56577659676704268137119043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37718439784469512091412695 56577659676704268137119043)
    ·
      refine ⟨84866489515056402205678565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56577659676704268137119043 84866489515056402205678565)
      ·
        refine ⟨15912466784073075413564731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84866489515056402205678565 15912466784073075413564731)
        ·
          refine ⟨23868700176109613120347097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15912466784073075413564731 23868700176109613120347097)
          ·
            refine ⟨17901525132082209840260323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23868700176109613120347097 17901525132082209840260323)
            ·
              refine ⟨26852287698123314760390485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17901525132082209840260323 26852287698123314760390485)
              ·
                refine ⟨157337623231191297424163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26852287698123314760390485 157337623231191297424163)
                ·
                  rfl

theorem cell20_1034147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_1034147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034147 prefixEnd_1034147 := by exact prefixLift 1034147
  have htrace : WordTrace (prefixWord ++ tailWord_1034147) baseStart_1034147 baseEnd_1034147 := by
    simpa [prefixWord, tailWord_1034147, baseEnd_1034147] using wordTrace_append hprefix tailTrace_1034147
  have hstable : (prefixWord ++ tailWord_1034147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034147).length < 2 ^ (prefixWord ++ tailWord_1034147).sum := by decide
  have hdescent : baseEnd_1034147 < baseStart_1034147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034198 : List Nat := [5, 2, 1, 1, 3, 1, 2, 5]
def baseStart_1034198 : Nat := 118140960795 + 1034198 * 2 ^ 59
def prefixEnd_1034198 : Nat := 4983230072969 + 3 ^ 40 * 1034198 * 2
def baseEnd_1034198 : Nat := 157345382494414793857427

theorem tailTrace_1034198 : CollatzResearch.WordTrace tailWord_1034198 prefixEnd_1034198 157345382494414793857427 := by
  unfold tailWord_1034198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357518744205296737594953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25146866604856498534346165 2357518744205296737594953)
  ·
    refine ⟨1768139058153972553196215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2357518744205296737594953 1768139058153972553196215)
    ·
      refine ⟨2652208587230958829794323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768139058153972553196215 2652208587230958829794323)
      ·
        refine ⟨3978312880846438244691485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652208587230958829794323 3978312880846438244691485)
        ·
          refine ⟨1491867330317414341759307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3978312880846438244691485 1491867330317414341759307)
          ·
            refine ⟨2237800995476121512638961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491867330317414341759307 2237800995476121512638961)
            ·
              refine ⟨1678350746607091134479221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237800995476121512638961 1678350746607091134479221)
              ·
                refine ⟨157345382494414793857427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1678350746607091134479221 157345382494414793857427)
                ·
                  rfl

theorem cell20_1034198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_1034198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034198 prefixEnd_1034198 := by exact prefixLift 1034198
  have htrace : WordTrace (prefixWord ++ tailWord_1034198) baseStart_1034198 baseEnd_1034198 := by
    simpa [prefixWord, tailWord_1034198, baseEnd_1034198] using wordTrace_append hprefix tailTrace_1034198
  have hstable : (prefixWord ++ tailWord_1034198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034198).length < 2 ^ (prefixWord ++ tailWord_1034198).sum := by decide
  have hdescent : baseEnd_1034198 < baseStart_1034198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034205 : List Nat := [1, 4, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1034205 : Nat := 118140960795 + 1034205 * 2 ^ 59
def prefixEnd_1034205 : Nat := 4983230072969 + 3 ^ 40 * 1034205 * 2
def baseEnd_1034205 : Nat := 472039342473983468338919

theorem tailTrace_1034205 : CollatzResearch.WordTrace tailWord_1034205 prefixEnd_1034205 472039342473983468338919 := by
  unfold tailWord_1034205
  simp only [CollatzResearch.WordTrace]
  refine ⟨37720555218259387997024069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25147036812172925331349379 37720555218259387997024069)
  ·
    refine ⟨7072604103423635249442013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37720555218259387997024069 7072604103423635249442013)
    ·
      refine ⟨2652226538783863218540755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7072604103423635249442013 2652226538783863218540755)
      ·
        refine ⟨3978339808175794827811133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652226538783863218540755 3978339808175794827811133)
        ·
          refine ⟨1491877428065923060429175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3978339808175794827811133 1491877428065923060429175)
          ·
            refine ⟨2237816142098884590643763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491877428065923060429175 2237816142098884590643763)
            ·
              refine ⟨3356724213148326885965645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237816142098884590643763 3356724213148326885965645)
              ·
                refine ⟨1258771579930622582237117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3356724213148326885965645 1258771579930622582237117)
                ·
                  refine ⟨472039342473983468338919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258771579930622582237117 472039342473983468338919)
                  ·
                    rfl

theorem cell20_1034205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1034205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034205 prefixEnd_1034205 := by exact prefixLift 1034205
  have htrace : WordTrace (prefixWord ++ tailWord_1034205) baseStart_1034205 baseEnd_1034205 := by
    simpa [prefixWord, tailWord_1034205, baseEnd_1034205] using wordTrace_append hprefix tailTrace_1034205
  have hstable : (prefixWord ++ tailWord_1034205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034205).length < 2 ^ (prefixWord ++ tailWord_1034205).sum := by decide
  have hdescent : baseEnd_1034205 < baseStart_1034205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034216 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_1034216 : Nat := 118140960795 + 1034216 * 2 ^ 59
def prefixEnd_1034216 : Nat := 4983230072969 + 3 ^ 40 * 1034216 * 2
def baseEnd_1034216 : Nat := 472044363173716318972207

theorem tailTrace_1034216 : CollatzResearch.WordTrace tailWord_1034216 prefixEnd_1034216 472044363173716318972207 := by
  unfold tailWord_1034216
  simp only [CollatzResearch.WordTrace]
  refine ⟨18860478210609768437837251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25147304280813024583783001 18860478210609768437837251)
  ·
    refine ⟨28290717315914652656755877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18860478210609768437837251 28290717315914652656755877)
    ·
      refine ⟨5304509496733997373141727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28290717315914652656755877 5304509496733997373141727)
      ·
        refine ⟨7956764245100996059712591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5304509496733997373141727 7956764245100996059712591)
        ·
          refine ⟨11935146367651494089568887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7956764245100996059712591 11935146367651494089568887)
          ·
            refine ⟨17902719551477241134353331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11935146367651494089568887 17902719551477241134353331)
            ·
              refine ⟨26854079327215861701529997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17902719551477241134353331 26854079327215861701529997)
              ·
                refine ⟨10070279747705948138073749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26854079327215861701529997 10070279747705948138073749)
                ·
                  refine ⟨472044363173716318972207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10070279747705948138073749 472044363173716318972207)
                  ·
                    rfl

theorem cell20_1034216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_1034216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034216 prefixEnd_1034216 := by exact prefixLift 1034216
  have htrace : WordTrace (prefixWord ++ tailWord_1034216) baseStart_1034216 baseEnd_1034216 := by
    simpa [prefixWord, tailWord_1034216, baseEnd_1034216] using wordTrace_append hprefix tailTrace_1034216
  have hstable : (prefixWord ++ tailWord_1034216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034216).length < 2 ^ (prefixWord ++ tailWord_1034216).sum := by decide
  have hdescent : baseEnd_1034216 < baseStart_1034216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034223 : List Nat := [1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_1034223 : Nat := 118140960795 + 1034223 * 2 ^ 59
def prefixEnd_1034223 : Nat := 4983230072969 + 3 ^ 40 * 1034223 * 2
def baseEnd_1034223 : Nat := 157349186054818468579615

theorem tailTrace_1034223 : CollatzResearch.WordTrace tailWord_1034223 prefixEnd_1034223 157349186054818468579615 := by
  unfold tailWord_1034223
  simp only [CollatzResearch.WordTrace]
  refine ⟨37721211732194177071179323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25147474488129451380786215 37721211732194177071179323)
  ·
    refine ⟨56581817598291265606768985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37721211732194177071179323 56581817598291265606768985)
    ·
      refine ⟨42436363198718449205076739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56581817598291265606768985 42436363198718449205076739)
      ·
        refine ⟨63654544798077673807615109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42436363198718449205076739 63654544798077673807615109)
        ·
          refine ⟨11935227149639563838927833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63654544798077673807615109 11935227149639563838927833)
          ·
            refine ⟨8951420362229672879195875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11935227149639563838927833 8951420362229672879195875)
            ·
              refine ⟨13427130543344509318793813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8951420362229672879195875 13427130543344509318793813)
              ·
                refine ⟨157349186054818468579615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13427130543344509318793813 157349186054818468579615)
                ·
                  rfl

theorem cell20_1034223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_1034223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034223 prefixEnd_1034223 := by exact prefixLift 1034223
  have htrace : WordTrace (prefixWord ++ tailWord_1034223) baseStart_1034223 baseEnd_1034223 := by
    simpa [prefixWord, tailWord_1034223, baseEnd_1034223] using wordTrace_append hprefix tailTrace_1034223
  have hstable : (prefixWord ++ tailWord_1034223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034223).length < 2 ^ (prefixWord ++ tailWord_1034223).sum := by decide
  have hdescent : baseEnd_1034223 < baseStart_1034223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034288 : List Nat := [2, 1, 1, 1, 2, 6, 2, 3, 2]
def baseStart_1034288 : Nat := 118140960795 + 1034288 * 2 ^ 59
def prefixEnd_1034288 : Nat := 4983230072969 + 3 ^ 40 * 1034288 * 2
def baseEnd_1034288 : Nat := 472077225935604068571913

theorem tailTrace_1034288 : CollatzResearch.WordTrace tailWord_1034288 prefixEnd_1034288 472077225935604068571913 := by
  unfold tailWord_1034288
  simp only [CollatzResearch.WordTrace]
  refine ⟨18861791238479346586147759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25149054984639128781530345 18861791238479346586147759)
  ·
    refine ⟨28292686857719019879221639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18861791238479346586147759 28292686857719019879221639)
    ·
      refine ⟨42439030286578529818832459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28292686857719019879221639 42439030286578529818832459)
      ·
        refine ⟨63658545429867794728248689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42439030286578529818832459 63658545429867794728248689)
        ·
          refine ⟨47743909072400846046186517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63658545429867794728248689 47743909072400846046186517)
          ·
            refine ⟨2237995737768789658414993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47743909072400846046186517 2237995737768789658414993)
            ·
              refine ⟨1678496803326592243811245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237995737768789658414993 1678496803326592243811245)
              ·
                refine ⟨629436301247472091429217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1678496803326592243811245 629436301247472091429217)
                ·
                  refine ⟨472077225935604068571913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629436301247472091429217 472077225935604068571913)
                  ·
                    rfl

theorem cell20_1034288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 3, 2].length) (baseStart_1034288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034288 prefixEnd_1034288 := by exact prefixLift 1034288
  have htrace : WordTrace (prefixWord ++ tailWord_1034288) baseStart_1034288 baseEnd_1034288 := by
    simpa [prefixWord, tailWord_1034288, baseEnd_1034288] using wordTrace_append hprefix tailTrace_1034288
  have hstable : (prefixWord ++ tailWord_1034288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034288).length < 2 ^ (prefixWord ++ tailWord_1034288).sum := by decide
  have hdescent : baseEnd_1034288 < baseStart_1034288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034330 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1034330 : Nat := 118140960795 + 1034330 * 2 ^ 59
def prefixEnd_1034330 : Nat := 4983230072969 + 3 ^ 40 * 1034330 * 2
def baseEnd_1034330 : Nat := 472096395880038589171741

theorem tailTrace_1034330 : CollatzResearch.WordTrace tailWord_1034330 prefixEnd_1034330 472096395880038589171741 := by
  unfold tailWord_1034330
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431278585701633586331111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25150076228537689563549629 9431278585701633586331111)
  ·
    refine ⟨14146917878552450379496667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9431278585701633586331111 14146917878552450379496667)
    ·
      refine ⟨21220376817828675569245001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14146917878552450379496667 21220376817828675569245001)
      ·
        refine ⟨15915282613371506676933751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21220376817828675569245001 15915282613371506676933751)
        ·
          refine ⟨23872923920057260015400627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15915282613371506676933751 23872923920057260015400627)
          ·
            refine ⟨35809385880085890023100941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23872923920057260015400627 35809385880085890023100941)
            ·
              refine ⟨13428519705032208758662853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35809385880085890023100941 13428519705032208758662853)
              ·
                refine ⟨2517847444693539142249285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13428519705032208758662853 2517847444693539142249285)
                ·
                  refine ⟨472096395880038589171741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517847444693539142249285 472096395880038589171741)
                  ·
                    rfl

theorem cell20_1034330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1034330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034330 prefixEnd_1034330 := by exact prefixLift 1034330
  have htrace : WordTrace (prefixWord ++ tailWord_1034330) baseStart_1034330 baseEnd_1034330 := by
    simpa [prefixWord, tailWord_1034330, baseEnd_1034330] using wordTrace_append hprefix tailTrace_1034330
  have hstable : (prefixWord ++ tailWord_1034330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034330).length < 2 ^ (prefixWord ++ tailWord_1034330).sum := by decide
  have hdescent : baseEnd_1034330 < baseStart_1034330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034333 : List Nat := [1, 4, 4, 1, 1, 2, 1, 6]
def baseStart_1034333 : Nat := 118140960795 + 1034333 * 2 ^ 59
def prefixEnd_1034333 : Nat := 4983230072969 + 3 ^ 40 * 1034333 * 2
def baseEnd_1034333 : Nat := 157365921720594637357243

theorem tailTrace_1034333 : CollatzResearch.WordTrace tailWord_1034333 prefixEnd_1034333 157365921720594637357243 := by
  unfold tailWord_1034333
  simp only [CollatzResearch.WordTrace]
  refine ⟨37725223761795665857683653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25150149174530443905122435 37725223761795665857683653)
  ·
    refine ⟨7073479455336687348315685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37725223761795665857683653 7073479455336687348315685)
    ·
      refine ⟨1326277397875628877809191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7073479455336687348315685 1326277397875628877809191)
      ·
        refine ⟨1989416096813443316713787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326277397875628877809191 1989416096813443316713787)
        ·
          refine ⟨2984124145220164975070681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989416096813443316713787 2984124145220164975070681)
          ·
            refine ⟨2238093108915123731303011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2984124145220164975070681 2238093108915123731303011)
            ·
              refine ⟨3357139663372685596954517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238093108915123731303011 3357139663372685596954517)
              ·
                refine ⟨157365921720594637357243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3357139663372685596954517 157365921720594637357243)
                ·
                  rfl

theorem cell20_1034333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 6].length) (baseStart_1034333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034333 prefixEnd_1034333 := by exact prefixLift 1034333
  have htrace : WordTrace (prefixWord ++ tailWord_1034333) baseStart_1034333 baseEnd_1034333 := by
    simpa [prefixWord, tailWord_1034333, baseEnd_1034333] using wordTrace_append hprefix tailTrace_1034333
  have hstable : (prefixWord ++ tailWord_1034333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034333).length < 2 ^ (prefixWord ++ tailWord_1034333).sum := by decide
  have hdescent : baseEnd_1034333 < baseStart_1034333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034354 : List Nat := [3, 2, 1, 2, 2, 4, 6]
def baseStart_1034354 : Nat := 118140960795 + 1034354 * 2 ^ 59
def prefixEnd_1034354 : Nat := 4983230072969 + 3 ^ 40 * 1034354 * 2
def baseEnd_1034354 : Nat := 52456372237111241374627

theorem tailTrace_1034354 : CollatzResearch.WordTrace tailWord_1034354 prefixEnd_1034354 52456372237111241374627 := by
  unfold tailWord_1034354
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431497423679896611049529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25150659796479724296132077 9431497423679896611049529)
  ·
    refine ⟨7073623067759922458287147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9431497423679896611049529 7073623067759922458287147)
    ·
      refine ⟨10610434601639883687430721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7073623067759922458287147 10610434601639883687430721)
      ·
        refine ⟨7957825951229912765573041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10610434601639883687430721 7957825951229912765573041)
        ·
          refine ⟨5968369463422434574179781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7957825951229912765573041 5968369463422434574179781)
          ·
            refine ⟨1119069274391706482658709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5968369463422434574179781 1119069274391706482658709)
            ·
              refine ⟨52456372237111241374627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1119069274391706482658709 52456372237111241374627)
              ·
                rfl

theorem cell20_1034354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 6].length) (baseStart_1034354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034354 prefixEnd_1034354 := by exact prefixLift 1034354
  have htrace : WordTrace (prefixWord ++ tailWord_1034354) baseStart_1034354 baseEnd_1034354 := by
    simpa [prefixWord, tailWord_1034354, baseEnd_1034354] using wordTrace_append hprefix tailTrace_1034354
  have hstable : (prefixWord ++ tailWord_1034354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034354).length < 2 ^ (prefixWord ++ tailWord_1034354).sum := by decide
  have hdescent : baseEnd_1034354 < baseStart_1034354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034361 : List Nat := [1, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_1034361 : Nat := 118140960795 + 1034361 * 2 ^ 59
def prefixEnd_1034361 : Nat := 4983230072969 + 3 ^ 40 * 1034361 * 2
def baseEnd_1034361 : Nat := 472110545124740259138281

theorem tailTrace_1034361 : CollatzResearch.WordTrace tailWord_1034361 prefixEnd_1034361 472110545124740259138281 := by
  unfold tailWord_1034361
  simp only [CollatzResearch.WordTrace]
  refine ⟨37726245005694226639702937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25150830003796151093135291 37726245005694226639702937)
  ·
    refine ⟨28294683754270669979777203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37726245005694226639702937 28294683754270669979777203)
    ·
      refine ⟨42442025631406004969665805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28294683754270669979777203 42442025631406004969665805)
      ·
        refine ⟨15915759611777251863624677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42442025631406004969665805 15915759611777251863624677)
        ·
          refine ⟨2984204927208234724429627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15915759611777251863624677 2984204927208234724429627)
          ·
            refine ⟨4476307390812352086644441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984204927208234724429627 4476307390812352086644441)
            ·
              refine ⟨3357230543109264064983331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4476307390812352086644441 3357230543109264064983331)
              ·
                refine ⟨5035845814663896097474997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357230543109264064983331 5035845814663896097474997)
                ·
                  refine ⟨472110545124740259138281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5035845814663896097474997 472110545124740259138281)
                  ·
                    rfl

theorem cell20_1034361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_1034361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034361 prefixEnd_1034361 := by exact prefixLift 1034361
  have htrace : WordTrace (prefixWord ++ tailWord_1034361) baseStart_1034361 baseEnd_1034361 := by
    simpa [prefixWord, tailWord_1034361, baseEnd_1034361] using wordTrace_append hprefix tailTrace_1034361
  have hstable : (prefixWord ++ tailWord_1034361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034361).length < 2 ^ (prefixWord ++ tailWord_1034361).sum := by decide
  have hdescent : baseEnd_1034361 < baseStart_1034361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034375 : List Nat := [1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_1034375 : Nat := 118140960795 + 1034375 * 2 ^ 59
def prefixEnd_1034375 : Nat := 4983230072969 + 3 ^ 40 * 1034375 * 2
def baseEnd_1034375 : Nat := 157372311702072810890519

theorem tailTrace_1034375 : CollatzResearch.WordTrace tailWord_1034375 prefixEnd_1034375 157372311702072810890519 := by
  unfold tailWord_1034375
  simp only [CollatzResearch.WordTrace]
  refine ⟨37726755627643507030712579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25151170418429004687141719 37726755627643507030712579)
  ·
    refine ⟨56590133441465260546068869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37726755627643507030712579 56590133441465260546068869)
    ·
      refine ⟨10610650020274736352387913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56590133441465260546068869 10610650020274736352387913)
      ·
        refine ⟨7957987515206052264290935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10610650020274736352387913 7957987515206052264290935)
        ·
          refine ⟨11936981272809078396436403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957987515206052264290935 11936981272809078396436403)
          ·
            refine ⟨17905471909213617594654605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936981272809078396436403 17905471909213617594654605)
            ·
              refine ⟨6714551965955106597995477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17905471909213617594654605 6714551965955106597995477)
              ·
                refine ⟨157372311702072810890519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6714551965955106597995477 157372311702072810890519)
                ·
                  rfl

theorem cell20_1034375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_1034375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034375 prefixEnd_1034375 := by exact prefixLift 1034375
  have htrace : WordTrace (prefixWord ++ tailWord_1034375) baseStart_1034375 baseEnd_1034375 := by
    simpa [prefixWord, tailWord_1034375, baseEnd_1034375] using wordTrace_append hprefix tailTrace_1034375
  have hstable : (prefixWord ++ tailWord_1034375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034375).length < 2 ^ (prefixWord ++ tailWord_1034375).sum := by decide
  have hdescent : baseEnd_1034375 < baseStart_1034375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034378 : List Nat := [3, 1, 2, 3, 1, 3, 1, 3, 3]
def baseStart_1034378 : Nat := 118140960795 + 1034378 * 2 ^ 59
def prefixEnd_1034378 : Nat := 4983230072969 + 3 ^ 40 * 1034378 * 2
def baseEnd_1034378 : Nat := 472118304387963755571545

theorem tailTrace_1034378 : CollatzResearch.WordTrace tailWord_1034378 prefixEnd_1034378 472118304387963755571545 := by
  unfold tailWord_1034378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9431716261658159635767947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25151243364421759028714525 9431716261658159635767947)
  ·
    refine ⟨14147574392487239453651921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9431716261658159635767947 14147574392487239453651921)
    ·
      refine ⟨10610680794365429590238941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14147574392487239453651921 10610680794365429590238941)
      ·
        refine ⟨3979005297887036096339603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10610680794365429590238941 3979005297887036096339603)
        ·
          refine ⟨5968507946830554144509405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979005297887036096339603 5968507946830554144509405)
          ·
            refine ⟨2238190480061457804191027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5968507946830554144509405 2238190480061457804191027)
            ·
              refine ⟨3357285720092186706286541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238190480061457804191027 3357285720092186706286541)
              ·
                refine ⟨1258982145034570014857453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3357285720092186706286541 1258982145034570014857453)
                ·
                  refine ⟨472118304387963755571545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258982145034570014857453 472118304387963755571545)
                  ·
                    rfl

theorem cell20_1034378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_1034378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034378 prefixEnd_1034378 := by exact prefixLift 1034378
  have htrace : WordTrace (prefixWord ++ tailWord_1034378) baseStart_1034378 baseEnd_1034378 := by
    simpa [prefixWord, tailWord_1034378, baseEnd_1034378] using wordTrace_append hprefix tailTrace_1034378
  have hstable : (prefixWord ++ tailWord_1034378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034378).length < 2 ^ (prefixWord ++ tailWord_1034378).sum := by decide
  have hdescent : baseEnd_1034378 < baseStart_1034378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034437 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 3]
def baseStart_1034437 : Nat := 118140960795 + 1034437 * 2 ^ 59
def prefixEnd_1034437 : Nat := 4983230072969 + 3 ^ 40 * 1034437 * 2
def baseEnd_1034437 : Nat := 472145233595621772604637

theorem tailTrace_1034437 : CollatzResearch.WordTrace tailWord_1034437 prefixEnd_1034437 472145233595621772604637 := by
  unfold tailWord_1034437
  simp only [CollatzResearch.WordTrace]
  refine ⟨37729016953418891619469565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25152677968945927746313043 37729016953418891619469565)
  ·
    refine ⟨14148381357532084357301087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37729016953418891619469565 14148381357532084357301087)
    ·
      refine ⟨21222572036298126535951631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14148381357532084357301087 21222572036298126535951631)
      ·
        refine ⟨31833858054447189803927447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21222572036298126535951631 31833858054447189803927447)
        ·
          refine ⟨47750787081670784705891171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31833858054447189803927447 47750787081670784705891171)
          ·
            refine ⟨71626180622506177058836757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47750787081670784705891171 71626180622506177058836757)
            ·
              refine ⟨3357477216679977049632973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 71626180622506177058836757 3357477216679977049632973)
              ·
                refine ⟨1259053956254991393612365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3357477216679977049632973 1259053956254991393612365)
                ·
                  refine ⟨472145233595621772604637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259053956254991393612365 472145233595621772604637)
                  ·
                    rfl

theorem cell20_1034437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_1034437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034437 prefixEnd_1034437 := by exact prefixLift 1034437
  have htrace : WordTrace (prefixWord ++ tailWord_1034437) baseStart_1034437 baseEnd_1034437 := by
    simpa [prefixWord, tailWord_1034437, baseEnd_1034437] using wordTrace_append hprefix tailTrace_1034437
  have hstable : (prefixWord ++ tailWord_1034437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034437).length < 2 ^ (prefixWord ++ tailWord_1034437).sum := by decide
  have hdescent : baseEnd_1034437 < baseStart_1034437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034471 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 3]
def baseStart_1034471 : Nat := 118140960795 + 1034471 * 2 ^ 59
def prefixEnd_1034471 : Nat := 4983230072969 + 3 ^ 40 * 1034471 * 2
def baseEnd_1034471 : Nat := 472160752122068765471165

theorem tailTrace_1034471 : CollatzResearch.WordTrace tailWord_1034471 prefixEnd_1034471 472160752122068765471165 := by
  unfold tailWord_1034471
  simp only [CollatzResearch.WordTrace]
  refine ⟨37730257035295715426207267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25153504690197143617471511 37730257035295715426207267)
  ·
    refine ⟨56595385552943573139310901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37730257035295715426207267 56595385552943573139310901)
    ·
      refine ⟨5305817395588459981810397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56595385552943573139310901 5305817395588459981810397)
      ·
        refine ⟨1989681523345672493178899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5305817395588459981810397 1989681523345672493178899)
        ·
          refine ⟨2984522285018508739768349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989681523345672493178899 2984522285018508739768349)
          ·
            refine ⟨1119195856881940777413131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2984522285018508739768349 1119195856881940777413131)
            ·
              refine ⟨1678793785322911166119697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1119195856881940777413131 1678793785322911166119697)
              ·
                refine ⟨1259095338992183374589773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678793785322911166119697 1259095338992183374589773)
                ·
                  refine ⟨472160752122068765471165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259095338992183374589773 472160752122068765471165)
                  ·
                    rfl

theorem cell20_1034471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_1034471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034471 prefixEnd_1034471 := by exact prefixLift 1034471
  have htrace : WordTrace (prefixWord ++ tailWord_1034471) baseStart_1034471 baseEnd_1034471 := by
    simpa [prefixWord, tailWord_1034471, baseEnd_1034471] using wordTrace_append hprefix tailTrace_1034471
  have hstable : (prefixWord ++ tailWord_1034471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034471).length < 2 ^ (prefixWord ++ tailWord_1034471).sum := by decide
  have hdescent : baseEnd_1034471 < baseStart_1034471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034506 : List Nat := [3, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1034506 : Nat := 118140960795 + 1034506 * 2 ^ 59
def prefixEnd_1034506 : Nat := 4983230072969 + 3 ^ 40 * 1034506 * 2
def baseEnd_1034506 : Nat := 157392242358588066434785

theorem tailTrace_1034506 : CollatzResearch.WordTrace tailWord_1034506 prefixEnd_1034506 157392242358588066434785 := by
  unfold tailWord_1034506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9432883397542229100932843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25154355726779277602487581 9432883397542229100932843)
  ·
    refine ⟨14149325096313343651399265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9432883397542229100932843 14149325096313343651399265)
    ·
      refine ⟨10611993822235007738549449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14149325096313343651399265 10611993822235007738549449)
      ·
        refine ⟨7958995366676255803912087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10611993822235007738549449 7958995366676255803912087)
        ·
          refine ⟨11938493050014383705868131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7958995366676255803912087 11938493050014383705868131)
          ·
            refine ⟨17907739575021575558802197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11938493050014383705868131 17907739575021575558802197)
            ·
              refine ⟨839425292579136354318853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17907739575021575558802197 839425292579136354318853)
              ·
                refine ⟨157392242358588066434785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839425292579136354318853 157392242358588066434785)
                ·
                  rfl

theorem cell20_1034506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1034506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034506 prefixEnd_1034506 := by exact prefixLift 1034506
  have htrace : WordTrace (prefixWord ++ tailWord_1034506) baseStart_1034506 baseEnd_1034506 := by
    simpa [prefixWord, tailWord_1034506, baseEnd_1034506] using wordTrace_append hprefix tailTrace_1034506
  have hstable : (prefixWord ++ tailWord_1034506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034506).length < 2 ^ (prefixWord ++ tailWord_1034506).sum := by decide
  have hdescent : baseEnd_1034506 < baseStart_1034506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034527 : List Nat := [1, 1, 2, 4, 3, 1, 8]
def baseStart_1034527 : Nat := 118140960795 + 1034527 * 2 ^ 59
def prefixEnd_1034527 : Nat := 4983230072969 + 3 ^ 40 * 1034527 * 2
def baseEnd_1034527 : Nat := 52465145783109051067141

theorem tailTrace_1034527 : CollatzResearch.WordTrace tailWord_1034527 prefixEnd_1034527 52465145783109051067141 := by
  unfold tailWord_1034527
  simp only [CollatzResearch.WordTrace]
  refine ⟨37732299523092836990245835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25154866348728557993497223 37732299523092836990245835)
  ·
    refine ⟨56598449284639255485368753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37732299523092836990245835 56598449284639255485368753)
    ·
      refine ⟨42448836963479441614026565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56598449284639255485368753 42448836963479441614026565)
      ·
        refine ⟨7959156930652395302629981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42448836963479441614026565 7959156930652395302629981)
        ·
          refine ⟨2984683848994648238486243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7959156930652395302629981 2984683848994648238486243)
          ·
            refine ⟨4477025773491972357729365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984683848994648238486243 4477025773491972357729365)
            ·
              refine ⟨52465145783109051067141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4477025773491972357729365 52465145783109051067141)
              ·
                rfl

theorem cell20_1034527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 8].length) (baseStart_1034527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034527 prefixEnd_1034527 := by exact prefixLift 1034527
  have htrace : WordTrace (prefixWord ++ tailWord_1034527) baseStart_1034527 baseEnd_1034527 := by
    simpa [prefixWord, tailWord_1034527, baseEnd_1034527] using wordTrace_append hprefix tailTrace_1034527
  have hstable : (prefixWord ++ tailWord_1034527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034527).length < 2 ^ (prefixWord ++ tailWord_1034527).sum := by decide
  have hdescent : baseEnd_1034527 < baseStart_1034527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034533 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 2]
def baseStart_1034533 : Nat := 118140960795 + 1034533 * 2 ^ 59
def prefixEnd_1034533 : Nat := 4983230072969 + 3 ^ 40 * 1034533 * 2
def baseEnd_1034533 : Nat := 472189050611472105404245

theorem tailTrace_1034533 : CollatzResearch.WordTrace tailWord_1034533 prefixEnd_1034533 472189050611472105404245 := by
  unfold tailWord_1034533
  simp only [CollatzResearch.WordTrace]
  refine ⟨37732518361071100014964253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25155012240714066676642835 37732518361071100014964253)
  ·
    refine ⟨14149694385401662505611595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37732518361071100014964253 14149694385401662505611595)
    ·
      refine ⟨21224541578102493758417393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14149694385401662505611595 21224541578102493758417393)
      ·
        refine ⟨15918406183576870318813045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21224541578102493758417393 15918406183576870318813045)
        ·
          refine ⟨1492350579710331592388723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15918406183576870318813045 1492350579710331592388723)
          ·
            refine ⟨2238525869565497388583085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492350579710331592388723 2238525869565497388583085)
            ·
              refine ⟨839447201087061520718657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2238525869565497388583085 839447201087061520718657)
              ·
                refine ⟨629585400815296140538993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839447201087061520718657 629585400815296140538993)
                ·
                  refine ⟨472189050611472105404245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629585400815296140538993 472189050611472105404245)
                  ·
                    rfl

theorem cell20_1034533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_1034533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034533 prefixEnd_1034533 := by exact prefixLift 1034533
  have htrace : WordTrace (prefixWord ++ tailWord_1034533) baseStart_1034533 baseEnd_1034533 := by
    simpa [prefixWord, tailWord_1034533, baseEnd_1034533] using wordTrace_append hprefix tailTrace_1034533
  have hstable : (prefixWord ++ tailWord_1034533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034533).length < 2 ^ (prefixWord ++ tailWord_1034533).sum := by decide
  have hdescent : baseEnd_1034533 < baseStart_1034533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034579 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_1034579 : Nat := 118140960795 + 1034579 * 2 ^ 59
def prefixEnd_1034579 : Nat := 4983230072969 + 3 ^ 40 * 1034579 * 2
def baseEnd_1034579 : Nat := 472210046264900389870723

theorem tailTrace_1034579 : CollatzResearch.WordTrace tailWord_1034579 prefixEnd_1034579 472210046264900389870723 := by
  unfold tailWord_1034579
  simp only [CollatzResearch.WordTrace]
  refine ⟨37734196118904449871138791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25156130745936299914092527 37734196118904449871138791)
  ·
    refine ⟨56601294178356674806708187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37734196118904449871138791 56601294178356674806708187)
    ·
      refine ⟨84901941267535012210062281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56601294178356674806708187 84901941267535012210062281)
      ·
        refine ⟨63676455950651259157546711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84901941267535012210062281 63676455950651259157546711)
        ·
          refine ⟨95514683925976888736320067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63676455950651259157546711 95514683925976888736320067)
          ·
            refine ⟨143272025888965333104480101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95514683925976888736320067 143272025888965333104480101)
            ·
              refine ⟨26863504854180999957090019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143272025888965333104480101 26863504854180999957090019)
              ·
                refine ⟨40295257281271499935635029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26863504854180999957090019 40295257281271499935635029)
                ·
                  refine ⟨472210046264900389870723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40295257281271499935635029 472210046264900389870723)
                  ·
                    rfl

theorem cell20_1034579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_1034579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034579 prefixEnd_1034579 := by exact prefixLift 1034579
  have htrace : WordTrace (prefixWord ++ tailWord_1034579) baseStart_1034579 baseEnd_1034579 := by
    simpa [prefixWord, tailWord_1034579, baseEnd_1034579] using wordTrace_append hprefix tailTrace_1034579
  have hstable : (prefixWord ++ tailWord_1034579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034579).length < 2 ^ (prefixWord ++ tailWord_1034579).sum := by decide
  have hdescent : baseEnd_1034579 < baseStart_1034579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034592 : List Nat := [2, 1, 1, 3, 5, 1, 1, 4, 2]
def baseStart_1034592 : Nat := 118140960795 + 1034592 * 2 ^ 59
def prefixEnd_1034592 : Nat := 4983230072969 + 3 ^ 40 * 1034592 * 2
def baseEnd_1034592 : Nat := 472215979819130122437337

theorem tailTrace_1034592 : CollatzResearch.WordTrace tailWord_1034592 prefixEnd_1034592 472215979819130122437337 := by
  unfold tailWord_1034592
  simp only [CollatzResearch.WordTrace]
  refine ⟨18867335133928676545681015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25156446845238235394241353 18867335133928676545681015)
  ·
    refine ⟨28301002700893014818521523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18867335133928676545681015 28301002700893014818521523)
    ·
      refine ⟨42451504051339522227782285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28301002700893014818521523 42451504051339522227782285)
      ·
        refine ⟨15919314019252320835418357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42451504051339522227782285 15919314019252320835418357)
        ·
          refine ⟨1492435689304905078320471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15919314019252320835418357 1492435689304905078320471)
          ·
            refine ⟨2238653533957357617480707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492435689304905078320471 2238653533957357617480707)
            ·
              refine ⟨3357980300936036426221061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238653533957357617480707 3357980300936036426221061)
              ·
                refine ⟨629621306425506829916449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3357980300936036426221061 629621306425506829916449)
                ·
                  refine ⟨472215979819130122437337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629621306425506829916449 472215979819130122437337)
                  ·
                    rfl

theorem cell20_1034592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 4, 2].length) (baseStart_1034592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034592 prefixEnd_1034592 := by exact prefixLift 1034592
  have htrace : WordTrace (prefixWord ++ tailWord_1034592) baseStart_1034592 baseEnd_1034592 := by
    simpa [prefixWord, tailWord_1034592, baseEnd_1034592] using wordTrace_append hprefix tailTrace_1034592
  have hstable : (prefixWord ++ tailWord_1034592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034592).length < 2 ^ (prefixWord ++ tailWord_1034592).sum := by decide
  have hdescent : baseEnd_1034592 < baseStart_1034592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034596 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1034596 : Nat := 118140960795 + 1034596 * 2 ^ 59
def prefixEnd_1034596 : Nat := 4983230072969 + 3 ^ 40 * 1034596 * 2
def baseEnd_1034596 : Nat := 472217805528123886303987

theorem tailTrace_1034596 : CollatzResearch.WordTrace tailWord_1034596 prefixEnd_1034596 472217805528123886303987 := by
  unfold tailWord_1034596
  simp only [CollatzResearch.WordTrace]
  refine ⟨18867408079921430887253821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25156544106561907849671761 18867408079921430887253821)
  ·
    refine ⟨7075278029970536582720183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18867408079921430887253821 7075278029970536582720183)
    ·
      refine ⟨10612917044955804874080275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7075278029970536582720183 10612917044955804874080275)
      ·
        refine ⟨15919375567433707311120413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10612917044955804874080275 15919375567433707311120413)
        ·
          refine ⟨5969765837787640241670155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15919375567433707311120413 5969765837787640241670155)
          ·
            refine ⟨8954648756681460362505233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969765837787640241670155 8954648756681460362505233)
            ·
              refine ⟨6715986567511095271878925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8954648756681460362505233 6715986567511095271878925)
              ·
                refine ⟨2518494962816660726954597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6715986567511095271878925 2518494962816660726954597)
                ·
                  refine ⟨472217805528123886303987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518494962816660726954597 472217805528123886303987)
                  ·
                    rfl

theorem cell20_1034596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1034596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034596 prefixEnd_1034596 := by exact prefixLift 1034596
  have htrace : WordTrace (prefixWord ++ tailWord_1034596) baseStart_1034596 baseEnd_1034596 := by
    simpa [prefixWord, tailWord_1034596, baseEnd_1034596] using wordTrace_append hprefix tailTrace_1034596
  have hstable : (prefixWord ++ tailWord_1034596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034596).length < 2 ^ (prefixWord ++ tailWord_1034596).sum := by decide
  have hdescent : baseEnd_1034596 < baseStart_1034596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034613 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 4]
def baseStart_1034613 : Nat := 118140960795 + 1034613 * 2 ^ 59
def prefixEnd_1034613 : Nat := 4983230072969 + 3 ^ 40 * 1034613 * 2
def baseEnd_1034613 : Nat := 472225564791347382737251

theorem tailTrace_1034613 : CollatzResearch.WordTrace tailWord_1034613 prefixEnd_1034613 472225564791347382737251 := by
  unfold tailWord_1034613
  simp only [CollatzResearch.WordTrace]
  refine ⟨37735436200781273677876493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25156957467187515785250995 37735436200781273677876493)
  ·
    refine ⟨14150788575292977629203685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37735436200781273677876493 14150788575292977629203685)
    ·
      refine ⟨2653272857867433305475691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14150788575292977629203685 2653272857867433305475691)
      ·
        refine ⟨3979909286801149958213537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653272857867433305475691 3979909286801149958213537)
        ·
          refine ⟨2984931965100862468660153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979909286801149958213537 2984931965100862468660153)
          ·
            refine ⟨2238698973825646851495115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2984931965100862468660153 2238698973825646851495115)
            ·
              refine ⟨3358048460738470277242673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238698973825646851495115 3358048460738470277242673)
              ·
                refine ⟨2518536345553852707932005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358048460738470277242673 2518536345553852707932005)
                ·
                  refine ⟨472225564791347382737251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518536345553852707932005 472225564791347382737251)
                  ·
                    rfl

theorem cell20_1034613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_1034613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034613 prefixEnd_1034613 := by exact prefixLift 1034613
  have htrace : WordTrace (prefixWord ++ tailWord_1034613) baseStart_1034613 baseEnd_1034613 := by
    simpa [prefixWord, tailWord_1034613, baseEnd_1034613] using wordTrace_append hprefix tailTrace_1034613
  have hstable : (prefixWord ++ tailWord_1034613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034613).length < 2 ^ (prefixWord ++ tailWord_1034613).sum := by decide
  have hdescent : baseEnd_1034613 < baseStart_1034613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034626 : List Nat := [3, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_1034626 : Nat := 118140960795 + 1034626 * 2 ^ 59
def prefixEnd_1034626 : Nat := 4983230072969 + 3 ^ 40 * 1034626 * 2
def baseEnd_1034626 : Nat := 472231498345577115303865

theorem tailTrace_1034626 : CollatzResearch.WordTrace tailWord_1034626 prefixEnd_1034626 472231498345577115303865 := by
  unfold tailWord_1034626
  simp only [CollatzResearch.WordTrace]
  refine ⟨9433977587433544224524933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25157273566489451265399821 9433977587433544224524933)
  ·
    refine ⟨1768870797643789542098425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9433977587433544224524933 1768870797643789542098425)
    ·
      refine ⟨1326653098232842156573819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1768870797643789542098425 1326653098232842156573819)
      ·
        refine ⟨1989979647349263234860729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1326653098232842156573819 1989979647349263234860729)
        ·
          refine ⟨1492484735511947426145547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1989979647349263234860729 1492484735511947426145547)
          ·
            refine ⟨2238727103267921139218321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492484735511947426145547 2238727103267921139218321)
            ·
              refine ⟨1679045327450940854413741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238727103267921139218321 1679045327450940854413741)
              ·
                refine ⟨629641997794102820405153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679045327450940854413741 629641997794102820405153)
                ·
                  refine ⟨472231498345577115303865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629641997794102820405153 472231498345577115303865)
                  ·
                    rfl

theorem cell20_1034626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_1034626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034626 prefixEnd_1034626 := by exact prefixLift 1034626
  have htrace : WordTrace (prefixWord ++ tailWord_1034626) baseStart_1034626 baseEnd_1034626 := by
    simpa [prefixWord, tailWord_1034626, baseEnd_1034626] using wordTrace_append hprefix tailTrace_1034626
  have hstable : (prefixWord ++ tailWord_1034626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034626).length < 2 ^ (prefixWord ++ tailWord_1034626).sum := by decide
  have hdescent : baseEnd_1034626 < baseStart_1034626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034644 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1034644 : Nat := 118140960795 + 1034644 * 2 ^ 59
def prefixEnd_1034644 : Nat := 4983230072969 + 3 ^ 40 * 1034644 * 2
def baseEnd_1034644 : Nat := 472239714036049052703791

theorem tailTrace_1034644 : CollatzResearch.WordTrace tailWord_1034644 prefixEnd_1034644 472239714036049052703791 := by
  unfold tailWord_1034644
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868283431834482986127493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25157711242445977314836657 18868283431834482986127493)
  ·
    refine ⟨3537803143468965559898905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18868283431834482986127493 3537803143468965559898905)
    ·
      refine ⟨2653352357601724169924179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3537803143468965559898905 2653352357601724169924179)
      ·
        refine ⟨3980028536402586254886269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653352357601724169924179 3980028536402586254886269)
        ·
          refine ⟨1492510701150969845582351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3980028536402586254886269 1492510701150969845582351)
          ·
            refine ⟨2238766051726454768373527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492510701150969845582351 2238766051726454768373527)
            ·
              refine ⟨3358149077589682152560291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238766051726454768373527 3358149077589682152560291)
              ·
                refine ⟨5037223616384523228840437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358149077589682152560291 5037223616384523228840437)
                ·
                  refine ⟨472239714036049052703791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5037223616384523228840437 472239714036049052703791)
                  ·
                    rfl

theorem cell20_1034644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1034644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034644 prefixEnd_1034644 := by exact prefixLift 1034644
  have htrace : WordTrace (prefixWord ++ tailWord_1034644) baseStart_1034644 baseEnd_1034644 := by
    simpa [prefixWord, tailWord_1034644, baseEnd_1034644] using wordTrace_append hprefix tailTrace_1034644
  have hstable : (prefixWord ++ tailWord_1034644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034644).length < 2 ^ (prefixWord ++ tailWord_1034644).sum := by decide
  have hdescent : baseEnd_1034644 < baseStart_1034644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034679 : List Nat := [1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_1034679 : Nat := 118140960795 + 1034679 * 2 ^ 59
def prefixEnd_1034679 : Nat := 4983230072969 + 3 ^ 40 * 1034679 * 2
def baseEnd_1034679 : Nat := 157418562996581495512327

theorem tailTrace_1034679 : CollatzResearch.WordTrace tailWord_1034679 prefixEnd_1034679 157418562996581495512327 := by
  unfold tailWord_1034679
  simp only [CollatzResearch.WordTrace]
  refine ⟨37737843418542166949779091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25158562279028111299852727 37737843418542166949779091)
  ·
    refine ⟨56606765127813250424668637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37737843418542166949779091 56606765127813250424668637)
    ·
      refine ⟨21227536922929968909250739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56606765127813250424668637 21227536922929968909250739)
      ·
        refine ⟨31841305384394953363876109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21227536922929968909250739 31841305384394953363876109)
        ·
          refine ⟨11940489519148107511453541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31841305384394953363876109 11940489519148107511453541)
          ·
            refine ⟨2238841784840270158397539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11940489519148107511453541 2238841784840270158397539)
            ·
              refine ⟨3358262677260405237596309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238841784840270158397539 3358262677260405237596309)
              ·
                refine ⟨157418562996581495512327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3358262677260405237596309 157418562996581495512327)
                ·
                  rfl

theorem cell20_1034679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_1034679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034679 prefixEnd_1034679 := by exact prefixLift 1034679
  have htrace : WordTrace (prefixWord ++ tailWord_1034679) baseStart_1034679 baseEnd_1034679 := by
    simpa [prefixWord, tailWord_1034679, baseEnd_1034679] using wordTrace_append hprefix tailTrace_1034679
  have hstable : (prefixWord ++ tailWord_1034679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034679).length < 2 ^ (prefixWord ++ tailWord_1034679).sum := by decide
  have hdescent : baseEnd_1034679 < baseStart_1034679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034731 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 6]
def baseStart_1034731 : Nat := 118140960795 + 1034731 * 2 ^ 59
def prefixEnd_1034731 : Nat := 4983230072969 + 3 ^ 40 * 1034731 * 2
def baseEnd_1034731 : Nat := 472279423206663416803435

theorem tailTrace_1034731 : CollatzResearch.WordTrace tailWord_1034731 prefixEnd_1034731 472279423206663416803435 := by
  unfold tailWord_1034731
  simp only [CollatzResearch.WordTrace]
  refine ⟨37739740014353779830672047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25159826676235853220448031 37739740014353779830672047)
  ·
    refine ⟨56609610021530669746008071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37739740014353779830672047 56609610021530669746008071)
    ·
      refine ⟨84914415032296004619012107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56609610021530669746008071 84914415032296004619012107)
      ·
        refine ⟨127371622548444006928518161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84914415032296004619012107 127371622548444006928518161)
        ·
          refine ⟨95528716911333005196388621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127371622548444006928518161 95528716911333005196388621)
          ·
            refine ⟨35823268841749876948645733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95528716911333005196388621 35823268841749876948645733)
            ·
              refine ⟨6716862907828101927871075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35823268841749876948645733 6716862907828101927871075)
              ·
                refine ⟨10075294361742152891806613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6716862907828101927871075 10075294361742152891806613)
                ·
                  refine ⟨472279423206663416803435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10075294361742152891806613 472279423206663416803435)
                  ·
                    rfl

theorem cell20_1034731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_1034731 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034731 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034731 prefixEnd_1034731 := by exact prefixLift 1034731
  have htrace : WordTrace (prefixWord ++ tailWord_1034731) baseStart_1034731 baseEnd_1034731 := by
    simpa [prefixWord, tailWord_1034731, baseEnd_1034731] using wordTrace_append hprefix tailTrace_1034731
  have hstable : (prefixWord ++ tailWord_1034731).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034731).length < 2 ^ (prefixWord ++ tailWord_1034731).sum := by decide
  have hdescent : baseEnd_1034731 < baseStart_1034731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034803 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 2]
def baseStart_1034803 : Nat := 118140960795 + 1034803 * 2 ^ 59
def prefixEnd_1034803 : Nat := 4983230072969 + 3 ^ 40 * 1034803 * 2
def baseEnd_1034803 : Nat := 472312285968551166403141

theorem tailTrace_1034803 : CollatzResearch.WordTrace tailWord_1034803 prefixEnd_1034803 472312285968551166403141 := by
  unfold tailWord_1034803
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742366070092936127293063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25161577380061957418195375 37742366070092936127293063)
  ·
    refine ⟨56613549105139404190939595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37742366070092936127293063 56613549105139404190939595)
    ·
      refine ⟨84920323657709106286409393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56613549105139404190939595 84920323657709106286409393)
      ·
        refine ⟨63690242743281829714807045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84920323657709106286409393 63690242743281829714807045)
        ·
          refine ⟨11941920514365343071526321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63690242743281829714807045 11941920514365343071526321)
          ·
            refine ⟨8956440385774007303644741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11941920514365343071526321 8956440385774007303644741)
            ·
              refine ⟨1679332572332626369433389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8956440385774007303644741 1679332572332626369433389)
              ·
                refine ⟨629749714624734888537521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679332572332626369433389 629749714624734888537521)
                ·
                  refine ⟨472312285968551166403141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629749714624734888537521 472312285968551166403141)
                  ·
                    rfl

theorem cell20_1034803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 2].length) (baseStart_1034803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034803 prefixEnd_1034803 := by exact prefixLift 1034803
  have htrace : WordTrace (prefixWord ++ tailWord_1034803) baseStart_1034803 baseEnd_1034803 := by
    simpa [prefixWord, tailWord_1034803, baseEnd_1034803] using wordTrace_append hprefix tailTrace_1034803
  have hstable : (prefixWord ++ tailWord_1034803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034803).length < 2 ^ (prefixWord ++ tailWord_1034803).sum := by decide
  have hdescent : baseEnd_1034803 < baseStart_1034803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034807 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_1034807 : Nat := 118140960795 + 1034807 * 2 ^ 59
def prefixEnd_1034807 : Nat := 4983230072969 + 3 ^ 40 * 1034807 * 2
def baseEnd_1034807 : Nat := 472314111677544930269791

theorem tailTrace_1034807 : CollatzResearch.WordTrace tailWord_1034807 prefixEnd_1034807 472314111677544930269791 := by
  unfold tailWord_1034807
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742511962078444810438675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25161674641385629873625783 37742511962078444810438675)
  ·
    refine ⟨56613767943117667215658013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37742511962078444810438675 56613767943117667215658013)
    ·
      refine ⟨21230162978669125205871755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56613767943117667215658013 21230162978669125205871755)
      ·
        refine ⟨31845244468003687808807633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21230162978669125205871755 31845244468003687808807633)
        ·
          refine ⟨23883933351002765856605725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31845244468003687808807633 23883933351002765856605725)
          ·
            refine ⟨8956475006626037196227147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23883933351002765856605725 8956475006626037196227147)
            ·
              refine ⟨13434712509939055794340721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8956475006626037196227147 13434712509939055794340721)
              ·
                refine ⟨10076034382454291845755541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13434712509939055794340721 10076034382454291845755541)
                ·
                  refine ⟨472314111677544930269791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10076034382454291845755541 472314111677544930269791)
                  ·
                    rfl

theorem cell20_1034807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_1034807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034807 prefixEnd_1034807 := by exact prefixLift 1034807
  have htrace : WordTrace (prefixWord ++ tailWord_1034807) baseStart_1034807 baseEnd_1034807 := by
    simpa [prefixWord, tailWord_1034807, baseEnd_1034807] using wordTrace_append hprefix tailTrace_1034807
  have hstable : (prefixWord ++ tailWord_1034807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034807).length < 2 ^ (prefixWord ++ tailWord_1034807).sum := by decide
  have hdescent : baseEnd_1034807 < baseStart_1034807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034817 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 5]
def baseStart_1034817 : Nat := 118140960795 + 1034817 * 2 ^ 59
def prefixEnd_1034817 : Nat := 4983230072969 + 3 ^ 40 * 1034817 * 2
def baseEnd_1034817 : Nat := 472318675950029339936417

theorem tailTrace_1034817 : CollatzResearch.WordTrace tailWord_1034817 prefixEnd_1034817 472318675950029339936417 := by
  unfold tailWord_1034817
  simp only [CollatzResearch.WordTrace]
  refine ⟨37742876692042216518302705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25161917794694811012201803 37742876692042216518302705)
  ·
    refine ⟨28307157519031662388727029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37742876692042216518302705 28307157519031662388727029)
    ·
      refine ⟨2653796017409218348943159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28307157519031662388727029 2653796017409218348943159)
      ·
        refine ⟨3980694026113827523414739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653796017409218348943159 3980694026113827523414739)
        ·
          refine ⟨5971041039170741285122109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980694026113827523414739 5971041039170741285122109)
          ·
            refine ⟨2239140389689027981920791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5971041039170741285122109 2239140389689027981920791)
            ·
              refine ⟨3358710584533541972881187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239140389689027981920791 3358710584533541972881187)
              ·
                refine ⟨5038065876800312959321781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358710584533541972881187 5038065876800312959321781)
                ·
                  refine ⟨472318675950029339936417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5038065876800312959321781 472318675950029339936417)
                  ·
                    rfl

theorem cell20_1034817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 5].length) (baseStart_1034817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034817 prefixEnd_1034817 := by exact prefixLift 1034817
  have htrace : WordTrace (prefixWord ++ tailWord_1034817) baseStart_1034817 baseEnd_1034817 := by
    simpa [prefixWord, tailWord_1034817, baseEnd_1034817] using wordTrace_append hprefix tailTrace_1034817
  have hstable : (prefixWord ++ tailWord_1034817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034817).length < 2 ^ (prefixWord ++ tailWord_1034817).sum := by decide
  have hdescent : baseEnd_1034817 < baseStart_1034817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034834 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1034834 : Nat := 118140960795 + 1034834 * 2 ^ 59
def prefixEnd_1034834 : Nat := 4983230072969 + 3 ^ 40 * 1034834 * 2
def baseEnd_1034834 : Nat := 472326435213252836369681

theorem tailTrace_1034834 : CollatzResearch.WordTrace tailWord_1034834 prefixEnd_1034834 472326435213252836369681 := by
  unfold tailWord_1034834
  simp only [CollatzResearch.WordTrace]
  refine ⟨9435874183245157105417889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25162331155320418947781037 9435874183245157105417889)
  ·
    refine ⟨7076905637433867829063417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9435874183245157105417889 7076905637433867829063417)
    ·
      refine ⟨5307679228075400871797563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7076905637433867829063417 5307679228075400871797563)
      ·
        refine ⟨7961518842113101307696345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5307679228075400871797563 7961518842113101307696345)
        ·
          refine ⟨5971139131584825980772259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7961518842113101307696345 5971139131584825980772259)
          ·
            refine ⟨8956708697377238971158389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5971139131584825980772259 8956708697377238971158389)
            ·
              refine ⟨839691440379116153546099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8956708697377238971158389 839691440379116153546099)
              ·
                refine ⟨1259537160568674230319149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839691440379116153546099 1259537160568674230319149)
                ·
                  refine ⟨472326435213252836369681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259537160568674230319149 472326435213252836369681)
                  ·
                    rfl

theorem cell20_1034834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1034834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034834 prefixEnd_1034834 := by exact prefixLift 1034834
  have htrace : WordTrace (prefixWord ++ tailWord_1034834) baseStart_1034834 baseEnd_1034834 := by
    simpa [prefixWord, tailWord_1034834, baseEnd_1034834] using wordTrace_append hprefix tailTrace_1034834
  have hstable : (prefixWord ++ tailWord_1034834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034834).length < 2 ^ (prefixWord ++ tailWord_1034834).sum := by decide
  have hdescent : baseEnd_1034834 < baseStart_1034834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034844 : List Nat := [2, 2, 4, 1, 4, 1, 2, 4]
def baseStart_1034844 : Nat := 118140960795 + 1034844 * 2 ^ 59
def prefixEnd_1034844 : Nat := 4983230072969 + 3 ^ 40 * 1034844 * 2
def baseEnd_1034844 : Nat := 157443666495245748678769

theorem tailTrace_1034844 : CollatzResearch.WordTrace tailWord_1034844 prefixEnd_1034844 157443666495245748678769 := by
  unfold tailWord_1034844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871930731472200064767793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25162574308629600086357057 18871930731472200064767793)
  ·
    refine ⟨14153948048604150048575845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18871930731472200064767793 14153948048604150048575845)
    ·
      refine ⟨2653865259113278134107971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14153948048604150048575845 2653865259113278134107971)
      ·
        refine ⟨3980797888669917201161957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653865259113278134107971 3980797888669917201161957)
        ·
          refine ⟨746399604125609475217867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3980797888669917201161957 746399604125609475217867)
          ·
            refine ⟨1119599406188414212826801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746399604125609475217867 1119599406188414212826801)
            ·
              refine ⟨839699554641310659620101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119599406188414212826801 839699554641310659620101)
              ·
                refine ⟨157443666495245748678769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 839699554641310659620101 157443666495245748678769)
                ·
                  rfl

theorem cell20_1034844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_1034844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034844 prefixEnd_1034844 := by exact prefixLift 1034844
  have htrace : WordTrace (prefixWord ++ tailWord_1034844) baseStart_1034844 baseEnd_1034844 := by
    simpa [prefixWord, tailWord_1034844, baseEnd_1034844] using wordTrace_append hprefix tailTrace_1034844
  have hstable : (prefixWord ++ tailWord_1034844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034844).length < 2 ^ (prefixWord ++ tailWord_1034844).sum := by decide
  have hdescent : baseEnd_1034844 < baseStart_1034844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034876 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1034876 : Nat := 118140960795 + 1034876 * 2 ^ 59
def prefixEnd_1034876 : Nat := 4983230072969 + 3 ^ 40 * 1034876 * 2
def baseEnd_1034876 : Nat := 472345605157687356969509

theorem tailTrace_1034876 : CollatzResearch.WordTrace tailWord_1034876 prefixEnd_1034876 472345605157687356969509 := by
  unfold tailWord_1034876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18872514299414234797350241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25163352399218979729800321 18872514299414234797350241)
  ·
    refine ⟨14154385724560676098012681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18872514299414234797350241 14154385724560676098012681)
    ·
      refine ⟨10615789293420507073509511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14154385724560676098012681 10615789293420507073509511)
      ·
        refine ⟨15923683940130760610264267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10615789293420507073509511 15923683940130760610264267)
        ·
          refine ⟨23885525910196140915396401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15923683940130760610264267 23885525910196140915396401)
          ·
            refine ⟨17914144432647105686547301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23885525910196140915396401 17914144432647105686547301)
            ·
              refine ⟨3358902081121332316227619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17914144432647105686547301 3358902081121332316227619)
              ·
                refine ⟨5038353121681998474341429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3358902081121332316227619 5038353121681998474341429)
                ·
                  refine ⟨472345605157687356969509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5038353121681998474341429 472345605157687356969509)
                  ·
                    rfl

theorem cell20_1034876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1034876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034876 prefixEnd_1034876 := by exact prefixLift 1034876
  have htrace : WordTrace (prefixWord ++ tailWord_1034876) baseStart_1034876 baseEnd_1034876 := by
    simpa [prefixWord, tailWord_1034876, baseEnd_1034876] using wordTrace_append hprefix tailTrace_1034876
  have hstable : (prefixWord ++ tailWord_1034876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034876).length < 2 ^ (prefixWord ++ tailWord_1034876).sum := by decide
  have hdescent : baseEnd_1034876 < baseStart_1034876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034931 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 3]
def baseStart_1034931 : Nat := 118140960795 + 1034931 * 2 ^ 59
def prefixEnd_1034931 : Nat := 4983230072969 + 3 ^ 40 * 1034931 * 2
def baseEnd_1034931 : Nat := 472370708656351610135951

theorem tailTrace_1034931 : CollatzResearch.WordTrace tailWord_1034931 prefixEnd_1034931 472370708656351610135951 := by
  unfold tailWord_1034931
  simp only [CollatzResearch.WordTrace]
  refine ⟨37747034613629213987952647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25164689742419475991968431 37747034613629213987952647)
  ·
    refine ⟨56620551920443820981928971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37747034613629213987952647 56620551920443820981928971)
    ·
      refine ⟨84930827880665731472893457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56620551920443820981928971 84930827880665731472893457)
      ·
        refine ⟨63698120910499298604670093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84930827880665731472893457 63698120910499298604670093)
        ·
          refine ⟨23886795341437236976751285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63698120910499298604670093 23886795341437236976751285)
          ·
            refine ⟨2239387063259740966570433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23886795341437236976751285 2239387063259740966570433)
            ·
              refine ⟨1679540297444805724927825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239387063259740966570433 1679540297444805724927825)
              ·
                refine ⟨1259655223083604293695869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679540297444805724927825 1259655223083604293695869)
                ·
                  refine ⟨472370708656351610135951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259655223083604293695869 472370708656351610135951)
                  ·
                    rfl

theorem cell20_1034931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 3].length) (baseStart_1034931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034931 prefixEnd_1034931 := by exact prefixLift 1034931
  have htrace : WordTrace (prefixWord ++ tailWord_1034931) baseStart_1034931 baseEnd_1034931 := by
    simpa [prefixWord, tailWord_1034931, baseEnd_1034931] using wordTrace_append hprefix tailTrace_1034931
  have hstable : (prefixWord ++ tailWord_1034931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034931).length < 2 ^ (prefixWord ++ tailWord_1034931).sum := by decide
  have hdescent : baseEnd_1034931 < baseStart_1034931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1034972 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 2]
def baseStart_1034972 : Nat := 118140960795 + 1034972 * 2 ^ 59
def prefixEnd_1034972 : Nat := 4983230072969 + 3 ^ 40 * 1034972 * 2
def baseEnd_1034972 : Nat := 472389422173537689769117

theorem tailTrace_1034972 : CollatzResearch.WordTrace tailWord_1034972 prefixEnd_1034972 472389422173537689769117 := by
  unfold tailWord_1034972
  simp only [CollatzResearch.WordTrace]
  refine ⟨18874265003240338995097585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25165686670987118660130113 18874265003240338995097585)
  ·
    refine ⟨14155698752430254246323189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18874265003240338995097585 14155698752430254246323189)
    ·
      refine ⟨1327096758040336335592799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14155698752430254246323189 1327096758040336335592799)
      ·
        refine ⟨1990645137060504503389199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1327096758040336335592799 1990645137060504503389199)
        ·
          refine ⟨2985967705590756755083799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990645137060504503389199 2985967705590756755083799)
          ·
            refine ⟨4478951558386135132625699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2985967705590756755083799 4478951558386135132625699)
            ·
              refine ⟨6718427337579202698938549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4478951558386135132625699 6718427337579202698938549)
              ·
                refine ⟨629852562898050253025489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6718427337579202698938549 629852562898050253025489)
                ·
                  refine ⟨472389422173537689769117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629852562898050253025489 472389422173537689769117)
                  ·
                    rfl

theorem cell20_1034972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_1034972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1034972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1034972 prefixEnd_1034972 := by exact prefixLift 1034972
  have htrace : WordTrace (prefixWord ++ tailWord_1034972) baseStart_1034972 baseEnd_1034972 := by
    simpa [prefixWord, tailWord_1034972, baseEnd_1034972] using wordTrace_append hprefix tailTrace_1034972
  have hstable : (prefixWord ++ tailWord_1034972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1034972).length < 2 ^ (prefixWord ++ tailWord_1034972).sum := by decide
  have hdescent : baseEnd_1034972 < baseStart_1034972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1034972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035048 : List Nat := [2, 1, 5, 1, 1, 1, 5, 2, 2]
def baseStart_1035048 : Nat := 118140960795 + 1035048 * 2 ^ 59
def prefixEnd_1035048 : Nat := 4983230072969 + 3 ^ 40 * 1035048 * 2
def baseEnd_1035048 : Nat := 472424110644419203235473

theorem tailTrace_1035048 : CollatzResearch.WordTrace tailWord_1035048 prefixEnd_1035048 472424110644419203235473 := by
  unfold tailWord_1035048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18875650977102671484980899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25167534636136895313307865 18875650977102671484980899)
  ·
    refine ⟨28313476465654007227471349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18875650977102671484980899 28313476465654007227471349)
    ·
      refine ⟨2654388418655063177575439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28313476465654007227471349 2654388418655063177575439)
      ·
        refine ⟨3981582627982594766363159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2654388418655063177575439 3981582627982594766363159)
        ·
          refine ⟨5972373941973892149544739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3981582627982594766363159 5972373941973892149544739)
          ·
            refine ⟨8958560912960838224317109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5972373941973892149544739 8958560912960838224317109)
            ·
              refine ⟨839865085590078583529729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8958560912960838224317109 839865085590078583529729)
              ·
                refine ⟨629898814192558937647297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839865085590078583529729 629898814192558937647297)
                ·
                  refine ⟨472424110644419203235473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629898814192558937647297 472424110644419203235473)
                  ·
                    rfl

theorem cell20_1035048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 2, 2].length) (baseStart_1035048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035048 prefixEnd_1035048 := by exact prefixLift 1035048
  have htrace : WordTrace (prefixWord ++ tailWord_1035048) baseStart_1035048 baseEnd_1035048 := by
    simpa [prefixWord, tailWord_1035048, baseEnd_1035048] using wordTrace_append hprefix tailTrace_1035048
  have hstable : (prefixWord ++ tailWord_1035048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035048).length < 2 ^ (prefixWord ++ tailWord_1035048).sum := by decide
  have hdescent : baseEnd_1035048 < baseStart_1035048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035059 : List Nat := [1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_1035059 : Nat := 118140960795 + 1035059 * 2 ^ 59
def prefixEnd_1035059 : Nat := 4983230072969 + 3 ^ 40 * 1035059 * 2
def baseEnd_1035059 : Nat := 157476377114717351289587

theorem tailTrace_1035059 : CollatzResearch.WordTrace tailWord_1035059 prefixEnd_1035059 157476377114717351289587 := by
  unfold tailWord_1035059
  simp only [CollatzResearch.WordTrace]
  refine ⟨37751703157165491848612231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25167802104776994565741487 37751703157165491848612231)
  ·
    refine ⟨56627554735748237772918347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37751703157165491848612231 56627554735748237772918347)
    ·
      refine ⟨84941332103622356659377521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56627554735748237772918347 84941332103622356659377521)
      ·
        refine ⟨63705999077716767494533141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84941332103622356659377521 63705999077716767494533141)
        ·
          refine ⟨2986218706767973476306241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63705999077716767494533141 2986218706767973476306241)
          ·
            refine ⟨2239664030075980107229681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986218706767973476306241 2239664030075980107229681)
            ·
              refine ⟨1679748022556985080422261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239664030075980107229681 1679748022556985080422261)
              ·
                refine ⟨157476377114717351289587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1679748022556985080422261 157476377114717351289587)
                ·
                  rfl

theorem cell20_1035059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_1035059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035059 prefixEnd_1035059 := by exact prefixLift 1035059
  have htrace : WordTrace (prefixWord ++ tailWord_1035059) baseStart_1035059 baseEnd_1035059 := by
    simpa [prefixWord, tailWord_1035059, baseEnd_1035059] using wordTrace_append hprefix tailTrace_1035059
  have hstable : (prefixWord ++ tailWord_1035059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035059).length < 2 ^ (prefixWord ++ tailWord_1035059).sum := by decide
  have hdescent : baseEnd_1035059 < baseStart_1035059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035080 : List Nat := [2, 1, 3, 1, 1, 3, 1, 8]
def baseStart_1035080 : Nat := 118140960795 + 1035080 * 2 ^ 59
def prefixEnd_1035080 : Nat := 4983230072969 + 3 ^ 40 * 1035080 * 2
def baseEnd_1035080 : Nat := 157479572105456438056225

theorem tailTrace_1035080 : CollatzResearch.WordTrace tailWord_1035080 prefixEnd_1035080 157479572105456438056225 := by
  unfold tailWord_1035080
  simp only [CollatzResearch.WordTrace]
  refine ⟨18876234545044706217563347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25168312726726274956751129 18876234545044706217563347)
  ·
    refine ⟨28314351817567059326345021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18876234545044706217563347 28314351817567059326345021)
    ·
      refine ⟨10617881931587647247379383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28314351817567059326345021 10617881931587647247379383)
      ·
        refine ⟨15926822897381470871069075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10617881931587647247379383 15926822897381470871069075)
        ·
          refine ⟨23890234346072206306603613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15926822897381470871069075 23890234346072206306603613)
          ·
            refine ⟨8958837879777077364976355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23890234346072206306603613 8958837879777077364976355)
            ·
              refine ⟨13438256819665616047464533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8958837879777077364976355 13438256819665616047464533)
              ·
                refine ⟨157479572105456438056225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13438256819665616047464533 157479572105456438056225)
                ·
                  rfl

theorem cell20_1035080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 8].length) (baseStart_1035080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035080 prefixEnd_1035080 := by exact prefixLift 1035080
  have htrace : WordTrace (prefixWord ++ tailWord_1035080) baseStart_1035080 baseEnd_1035080 := by
    simpa [prefixWord, tailWord_1035080, baseEnd_1035080] using wordTrace_append hprefix tailTrace_1035080
  have hstable : (prefixWord ++ tailWord_1035080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035080).length < 2 ^ (prefixWord ++ tailWord_1035080).sum := by decide
  have hdescent : baseEnd_1035080 < baseStart_1035080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035100 : List Nat := [2, 2, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1035100 : Nat := 118140960795 + 1035100 * 2 ^ 59
def prefixEnd_1035100 : Nat := 4983230072969 + 3 ^ 40 * 1035100 * 2
def baseEnd_1035100 : Nat := 472447844861338133501927

theorem tailTrace_1035100 : CollatzResearch.WordTrace tailWord_1035100 prefixEnd_1035100 472447844861338133501927 := by
  unfold tailWord_1035100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18876599275008477925427377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25168799033344637233903169 18876599275008477925427377)
  ·
    refine ⟨14157449456256358444070533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18876599275008477925427377 14157449456256358444070533)
    ·
      refine ⟨2654521773048067208263225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14157449456256358444070533 2654521773048067208263225)
      ·
        refine ⟨1990891329786050406197419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2654521773048067208263225 1990891329786050406197419)
        ·
          refine ⟨2986336994679075609296129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1990891329786050406197419 2986336994679075609296129)
          ·
            refine ⟨2239752746009306706972097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986336994679075609296129 2239752746009306706972097)
            ·
              refine ⟨1679814559506980030229073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239752746009306706972097 1679814559506980030229073)
              ·
                refine ⟨1259860919630235022671805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679814559506980030229073 1259860919630235022671805)
                ·
                  refine ⟨472447844861338133501927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259860919630235022671805 472447844861338133501927)
                  ·
                    rfl

theorem cell20_1035100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1035100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035100 prefixEnd_1035100 := by exact prefixLift 1035100
  have htrace : WordTrace (prefixWord ++ tailWord_1035100) baseStart_1035100 baseEnd_1035100 := by
    simpa [prefixWord, tailWord_1035100, baseEnd_1035100] using wordTrace_append hprefix tailTrace_1035100
  have hstable : (prefixWord ++ tailWord_1035100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035100).length < 2 ^ (prefixWord ++ tailWord_1035100).sum := by decide
  have hdescent : baseEnd_1035100 < baseStart_1035100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035107 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 2]
def baseStart_1035107 : Nat := 118140960795 + 1035107 * 2 ^ 59
def prefixEnd_1035107 : Nat := 4983230072969 + 3 ^ 40 * 1035107 * 2
def baseEnd_1035107 : Nat := 472451039852077220268565

theorem tailTrace_1035107 : CollatzResearch.WordTrace tailWord_1035107 prefixEnd_1035107 472451039852077220268565 := by
  unfold tailWord_1035107
  simp only [CollatzResearch.WordTrace]
  refine ⟨37753453860991596046359575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25168969240661064030906383 37753453860991596046359575)
  ·
    refine ⟨56630180791487394069539363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37753453860991596046359575 56630180791487394069539363)
    ·
      refine ⟨84945271187231091104309045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56630180791487394069539363 84945271187231091104309045)
      ·
        refine ⟨7963619173802914791028973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84945271187231091104309045 7963619173802914791028973)
        ·
          refine ⟨2986357190176093046635865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7963619173802914791028973 2986357190176093046635865)
          ·
            refine ⟨2239767892632069784976899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986357190176093046635865 2239767892632069784976899)
            ·
              refine ⟨3359651838948104677465349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239767892632069784976899 3359651838948104677465349)
              ·
                refine ⟨629934719802769627024753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3359651838948104677465349 629934719802769627024753)
                ·
                  refine ⟨472451039852077220268565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629934719802769627024753 472451039852077220268565)
                  ·
                    rfl

theorem cell20_1035107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 2].length) (baseStart_1035107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035107 prefixEnd_1035107 := by exact prefixLift 1035107
  have htrace : WordTrace (prefixWord ++ tailWord_1035107) baseStart_1035107 baseEnd_1035107 := by
    simpa [prefixWord, tailWord_1035107, baseEnd_1035107] using wordTrace_append hprefix tailTrace_1035107
  have hstable : (prefixWord ++ tailWord_1035107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035107).length < 2 ^ (prefixWord ++ tailWord_1035107).sum := by decide
  have hdescent : baseEnd_1035107 < baseStart_1035107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035145 : List Nat := [1, 2, 1, 1, 5, 3, 2, 3, 2]
def baseStart_1035145 : Nat := 118140960795 + 1035145 * 2 ^ 59
def prefixEnd_1035145 : Nat := 4983230072969 + 3 ^ 40 * 1035145 * 2
def baseEnd_1035145 : Nat := 472468384087517977001743

theorem tailTrace_1035145 : CollatzResearch.WordTrace tailWord_1035145 prefixEnd_1035145 472468384087517977001743 := by
  unfold tailWord_1035145
  simp only [CollatzResearch.WordTrace]
  refine ⟨37754839834853928536242889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25169893223235952357495259 37754839834853928536242889)
  ·
    refine ⟨28316129876140446402182167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37754839834853928536242889 28316129876140446402182167)
    ·
      refine ⟨42474194814210669603273251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28316129876140446402182167 42474194814210669603273251)
      ·
        refine ⟨63711292221316004404909877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42474194814210669603273251 63711292221316004404909877)
        ·
          refine ⟨5972933645748375412960301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63711292221316004404909877 5972933645748375412960301)
          ·
            refine ⟨2239850117155640779860113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5972933645748375412960301 2239850117155640779860113)
            ·
              refine ⟨1679887587866730584895085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239850117155640779860113 1679887587866730584895085)
              ·
                refine ⟨629957845450023969335657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1679887587866730584895085 629957845450023969335657)
                ·
                  refine ⟨472468384087517977001743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629957845450023969335657 472468384087517977001743)
                  ·
                    rfl

theorem cell20_1035145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_1035145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035145 prefixEnd_1035145 := by exact prefixLift 1035145
  have htrace : WordTrace (prefixWord ++ tailWord_1035145) baseStart_1035145 baseEnd_1035145 := by
    simpa [prefixWord, tailWord_1035145, baseEnd_1035145] using wordTrace_append hprefix tailTrace_1035145
  have hstable : (prefixWord ++ tailWord_1035145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035145).length < 2 ^ (prefixWord ++ tailWord_1035145).sum := by decide
  have hdescent : baseEnd_1035145 < baseStart_1035145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035194 : List Nat := [3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_1035194 : Nat := 118140960795 + 1035194 * 2 ^ 59
def prefixEnd_1035194 : Nat := 4983230072969 + 3 ^ 40 * 1035194 * 2
def baseEnd_1035194 : Nat := 157496916340897194789403

theorem tailTrace_1035194 : CollatzResearch.WordTrace tailWord_1035194 prefixEnd_1035194 157496916340897194789403 := by
  unfold tailWord_1035194
  simp only [CollatzResearch.WordTrace]
  refine ⟨9439156752919102476194159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25171084674450939936517757 9439156752919102476194159)
  ·
    refine ⟨14158735129378653714291239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9439156752919102476194159 14158735129378653714291239)
    ·
      refine ⟨21238102694067980571436859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14158735129378653714291239 21238102694067980571436859)
      ·
        refine ⟨31857154041101970857155289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21238102694067980571436859 31857154041101970857155289)
        ·
          refine ⟨23892865530826478142866467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31857154041101970857155289 23892865530826478142866467)
          ·
            refine ⟨35839298296239717214299701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23892865530826478142866467 35839298296239717214299701)
            ·
              refine ⟨3359934215272473488840597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35839298296239717214299701 3359934215272473488840597)
              ·
                refine ⟨157496916340897194789403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3359934215272473488840597 157496916340897194789403)
                ·
                  rfl

theorem cell20_1035194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_1035194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035194 prefixEnd_1035194 := by exact prefixLift 1035194
  have htrace : WordTrace (prefixWord ++ tailWord_1035194) baseStart_1035194 baseEnd_1035194 := by
    simpa [prefixWord, tailWord_1035194, baseEnd_1035194] using wordTrace_append hprefix tailTrace_1035194
  have hstable : (prefixWord ++ tailWord_1035194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035194).length < 2 ^ (prefixWord ++ tailWord_1035194).sum := by decide
  have hdescent : baseEnd_1035194 < baseStart_1035194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035213 : List Nat := [1, 6, 3, 1, 1, 1, 3, 2, 2]
def baseStart_1035213 : Nat := 118140960795 + 1035213 * 2 ^ 59
def prefixEnd_1035213 : Nat := 4983230072969 + 3 ^ 40 * 1035213 * 2
def baseEnd_1035213 : Nat := 472499421140411962734799

theorem tailTrace_1035213 : CollatzResearch.WordTrace tailWord_1035213 prefixEnd_1035213 472499421140411962734799 := by
  unfold tailWord_1035213
  simp only [CollatzResearch.WordTrace]
  refine ⟨37757319998607576149718293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25171546665738384099812195 37757319998607576149718293)
  ·
    refine ⟨1769874374934730132018045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 37757319998607576149718293 1769874374934730132018045)
    ·
      refine ⟨663702890600523799506767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1769874374934730132018045 663702890600523799506767)
      ·
        refine ⟨995554335900785699260151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663702890600523799506767 995554335900785699260151)
        ·
          refine ⟨1493331503851178548890227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995554335900785699260151 1493331503851178548890227)
          ·
            refine ⟨2239997255776767823335341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493331503851178548890227 2239997255776767823335341)
            ·
              refine ⟨839998970916287933750753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2239997255776767823335341 839998970916287933750753)
              ·
                refine ⟨629999228187215950313065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839998970916287933750753 629999228187215950313065)
                ·
                  refine ⟨472499421140411962734799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629999228187215950313065 472499421140411962734799)
                  ·
                    rfl

theorem cell20_1035213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_1035213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035213 prefixEnd_1035213 := by exact prefixLift 1035213
  have htrace : WordTrace (prefixWord ++ tailWord_1035213) baseStart_1035213 baseEnd_1035213 := by
    simpa [prefixWord, tailWord_1035213, baseEnd_1035213] using wordTrace_append hprefix tailTrace_1035213
  have hstable : (prefixWord ++ tailWord_1035213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035213).length < 2 ^ (prefixWord ++ tailWord_1035213).sum := by decide
  have hdescent : baseEnd_1035213 < baseStart_1035213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035221 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 4]
def baseStart_1035221 : Nat := 118140960795 + 1035221 * 2 ^ 59
def prefixEnd_1035221 : Nat := 4983230072969 + 3 ^ 40 * 1035221 * 2
def baseEnd_1035221 : Nat := 472503072558399490468099

theorem tailTrace_1035221 : CollatzResearch.WordTrace tailWord_1035221 prefixEnd_1035221 472503072558399490468099 := by
  unfold tailWord_1035221
  simp only [CollatzResearch.WordTrace]
  refine ⟨37757611782578593516009517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25171741188385729010673011 37757611782578593516009517)
  ·
    refine ⟨14159104418466972568503569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37757611782578593516009517 14159104418466972568503569)
    ·
      refine ⟨10619328313850229426377677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14159104418466972568503569 10619328313850229426377677)
      ·
        refine ⟨3982248117693836034891629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10619328313850229426377677 3982248117693836034891629)
        ·
          refine ⟨1493343044135188513084361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3982248117693836034891629 1493343044135188513084361)
          ·
            refine ⟨1120007283101391384813271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1493343044135188513084361 1120007283101391384813271)
            ·
              refine ⟨1680010924652087077219907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120007283101391384813271 1680010924652087077219907)
              ·
                refine ⟨2520016386978130615829861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680010924652087077219907 2520016386978130615829861)
                ·
                  refine ⟨472503072558399490468099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2520016386978130615829861 472503072558399490468099)
                  ·
                    rfl

theorem cell20_1035221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_1035221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035221 prefixEnd_1035221 := by exact prefixLift 1035221
  have htrace : WordTrace (prefixWord ++ tailWord_1035221) baseStart_1035221 baseEnd_1035221 := by
    simpa [prefixWord, tailWord_1035221, baseEnd_1035221] using wordTrace_append hprefix tailTrace_1035221
  have hstable : (prefixWord ++ tailWord_1035221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035221).length < 2 ^ (prefixWord ++ tailWord_1035221).sum := by decide
  have hdescent : baseEnd_1035221 < baseStart_1035221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035231 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 3]
def baseStart_1035231 : Nat := 118140960795 + 1035231 * 2 ^ 59
def prefixEnd_1035231 : Nat := 4983230072969 + 3 ^ 40 * 1035231 * 2
def baseEnd_1035231 : Nat := 472507636830883900134725

theorem tailTrace_1035231 : CollatzResearch.WordTrace tailWord_1035231 prefixEnd_1035231 472507636830883900134725 := by
  unfold tailWord_1035231
  simp only [CollatzResearch.WordTrace]
  refine ⟨37757976512542365223873547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25171984341694910149249031 37757976512542365223873547)
  ·
    refine ⟨56636964768813547835810321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37757976512542365223873547 56636964768813547835810321)
    ·
      refine ⟨42477723576610160876857741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56636964768813547835810321 42477723576610160876857741)
      ·
        refine ⟨15929146341228810328821653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42477723576610160876857741 15929146341228810328821653)
        ·
          refine ⟨746678734745100484163515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15929146341228810328821653 746678734745100484163515)
          ·
            refine ⟨1120018102117650726245273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746678734745100484163515 1120018102117650726245273)
            ·
              refine ⟨840013576588238044683955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1120018102117650726245273 840013576588238044683955)
              ·
                refine ⟨1260020364882357067025933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 840013576588238044683955 1260020364882357067025933)
                ·
                  refine ⟨472507636830883900134725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260020364882357067025933 472507636830883900134725)
                  ·
                    rfl

theorem cell20_1035231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 3].length) (baseStart_1035231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035231 prefixEnd_1035231 := by exact prefixLift 1035231
  have htrace : WordTrace (prefixWord ++ tailWord_1035231) baseStart_1035231 baseEnd_1035231 := by
    simpa [prefixWord, tailWord_1035231, baseEnd_1035231] using wordTrace_append hprefix tailTrace_1035231
  have hstable : (prefixWord ++ tailWord_1035231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035231).length < 2 ^ (prefixWord ++ tailWord_1035231).sum := by decide
  have hdescent : baseEnd_1035231 < baseStart_1035231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1035266 : List Nat := [3, 4, 1, 3, 1, 8]
def baseStart_1035266 : Nat := 118140960795 + 1035266 * 2 ^ 59
def prefixEnd_1035266 : Nat := 4983230072969 + 3 ^ 40 * 1035266 * 2
def baseEnd_1035266 : Nat := 17500874510539975332145

theorem tailTrace_1035266 : CollatzResearch.WordTrace tailWord_1035266 prefixEnd_1035266 17500874510539975332145 := by
  unfold tailWord_1035266
  simp only [CollatzResearch.WordTrace]
  refine ⟨9439813266853891550349413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25172835378277044134265101 9439813266853891550349413)
  ·
    refine ⟨1769964987535104665690515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9439813266853891550349413 1769964987535104665690515)
    ·
      refine ⟨2654947481302656998535773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1769964987535104665690515 2654947481302656998535773)
      ·
        refine ⟨995605305488496374450915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2654947481302656998535773 995605305488496374450915)
        ·
          refine ⟨1493407958232744561676373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995605305488496374450915 1493407958232744561676373)
          ·
            refine ⟨17500874510539975332145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1493407958232744561676373 17500874510539975332145)
            ·
              rfl

theorem cell20_1035266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 8].length) (baseStart_1035266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1035266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1035266 prefixEnd_1035266 := by exact prefixLift 1035266
  have htrace : WordTrace (prefixWord ++ tailWord_1035266) baseStart_1035266 baseEnd_1035266 := by
    simpa [prefixWord, tailWord_1035266, baseEnd_1035266] using wordTrace_append hprefix tailTrace_1035266
  have hstable : (prefixWord ++ tailWord_1035266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1035266).length < 2 ^ (prefixWord ++ tailWord_1035266).sum := by decide
  have hdescent : baseEnd_1035266 < baseStart_1035266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1035266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
