import V185TrunkScan23Chunk0570

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3375793 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3375793 : Nat := 118140960795 + 3375793 * 2 ^ 59
def prefixEnd_3375793 : Nat := 4983230072969 + 3 ^ 40 * 3375793 * 2
def baseEnd_3375793 : Nat := 1733404399083415928062517

theorem tailTrace_3375793 : CollatzResearch.WordTrace tailWord_3375793 prefixEnd_3375793 1733404399083415928062517 := by
  unfold tailWord_3375793
  simp only [CollatzResearch.WordTrace]
  refine ⟨123125285859085975388852033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82083523906057316925901355 123125285859085975388852033)
  ·
    refine ⟨92343964394314481541639025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123125285859085975388852033 92343964394314481541639025)
    ·
      refine ⟨69257973295735861156229269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92343964394314481541639025 69257973295735861156229269)
      ·
        refine ⟨3246467498237618491698247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69257973295735861156229269 3246467498237618491698247)
        ·
          refine ⟨4869701247356427737547371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3246467498237618491698247 4869701247356427737547371)
          ·
            refine ⟨7304551871034641606321057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4869701247356427737547371 7304551871034641606321057)
            ·
              refine ⟨5478413903275981204740793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7304551871034641606321057 5478413903275981204740793)
              ·
                refine ⟨4108810427456985903555595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5478413903275981204740793 4108810427456985903555595)
                ·
                  refine ⟨6163215641185478855333393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108810427456985903555595 6163215641185478855333393)
                  ·
                    refine ⟨4622411730889109141500045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6163215641185478855333393 4622411730889109141500045)
                    ·
                      refine ⟨1733404399083415928062517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622411730889109141500045 1733404399083415928062517)
                      ·
                        rfl

theorem cell23_3375793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3375793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375793 prefixEnd_3375793 := by exact prefixLift 3375793
  have htrace : WordTrace (prefixWord ++ tailWord_3375793) baseStart_3375793 baseEnd_3375793 := by
    simpa [prefixWord, tailWord_3375793, baseEnd_3375793] using wordTrace_append hprefix tailTrace_3375793
  have hstable : (prefixWord ++ tailWord_3375793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375793).length < 2 ^ (prefixWord ++ tailWord_3375793).sum := by decide
  have hdescent : baseEnd_3375793 < baseStart_3375793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375816 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2]
def baseStart_3375816 : Nat := 118140960795 + 3375816 * 2 ^ 59
def prefixEnd_3375816 : Nat := 4983230072969 + 3 ^ 40 * 3375816 * 2
def baseEnd_3375816 : Nat := 1733416209138469338074911

theorem tailTrace_3375816 : CollatzResearch.WordTrace tailWord_3375816 prefixEnd_3375816 1733416209138469338074911 := by
  unfold tailWord_3375816
  simp only [CollatzResearch.WordTrace]
  refine ⟨61563062369001325158469651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82084083158668433544626201 61563062369001325158469651)
  ·
    refine ⟨92344593553501987737704477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61563062369001325158469651 92344593553501987737704477)
    ·
      refine ⟨34629222582563245401639179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92344593553501987737704477 34629222582563245401639179)
      ·
        refine ⟨51943833873844868102458769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34629222582563245401639179 51943833873844868102458769)
        ·
          refine ⟨38957875405383651076844077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51943833873844868102458769 38957875405383651076844077)
          ·
            refine ⟨14609203277018869153816529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38957875405383651076844077 14609203277018869153816529)
            ·
              refine ⟨10956902457764151865362397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14609203277018869153816529 10956902457764151865362397)
              ·
                refine ⟨4108838421661556949510899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10956902457764151865362397 4108838421661556949510899)
                ·
                  refine ⟨6163257632492335424266349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4108838421661556949510899 6163257632492335424266349)
                  ·
                    refine ⟨2311221612184625784099881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6163257632492335424266349 2311221612184625784099881)
                    ·
                      refine ⟨1733416209138469338074911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311221612184625784099881 1733416209138469338074911)
                      ·
                        rfl

theorem cell23_3375816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_3375816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375816 prefixEnd_3375816 := by exact prefixLift 3375816
  have htrace : WordTrace (prefixWord ++ tailWord_3375816) baseStart_3375816 baseEnd_3375816 := by
    simpa [prefixWord, tailWord_3375816, baseEnd_3375816] using wordTrace_append hprefix tailTrace_3375816
  have hstable : (prefixWord ++ tailWord_3375816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375816).length < 2 ^ (prefixWord ++ tailWord_3375816).sum := by decide
  have hdescent : baseEnd_3375816 < baseStart_3375816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375835 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 13]
def baseStart_3375835 : Nat := 118140960795 + 3375835 * 2 ^ 59
def prefixEnd_3375835 : Nat := 4983230072969 + 3 ^ 40 * 3375835 * 2
def baseEnd_3375835 : Nat := 192602885030100529304147

theorem tailTrace_3375835 : CollatzResearch.WordTrace tailWord_3375835 prefixEnd_3375835 192602885030100529304147 := by
  unfold tailWord_3375835
  simp only [CollatzResearch.WordTrace]
  refine ⟨123126817724933816561880959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82084545149955877707920639 123126817724933816561880959)
  ·
    refine ⟨184690226587400724842821439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123126817724933816561880959 184690226587400724842821439)
    ·
      refine ⟨277035339881101087264232159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184690226587400724842821439 277035339881101087264232159)
      ·
        refine ⟨415553009821651630896348239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277035339881101087264232159 415553009821651630896348239)
        ·
          refine ⟨623329514732477446344522359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415553009821651630896348239 623329514732477446344522359)
          ·
            refine ⟨934994272098716169516783539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623329514732477446344522359 934994272098716169516783539)
            ·
              refine ⟨1402491408148074254275175309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934994272098716169516783539 1402491408148074254275175309)
              ·
                refine ⟨525934278055527845353190741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1402491408148074254275175309 525934278055527845353190741)
                ·
                  refine ⟨192602885030100529304147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 525934278055527845353190741 192602885030100529304147)
                  ·
                    rfl

theorem cell23_3375835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 13].length) (baseStart_3375835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375835 prefixEnd_3375835 := by exact prefixLift 3375835
  have htrace : WordTrace (prefixWord ++ tailWord_3375835) baseStart_3375835 baseEnd_3375835 := by
    simpa [prefixWord, tailWord_3375835, baseEnd_3375835] using wordTrace_append hprefix tailTrace_3375835
  have hstable : (prefixWord ++ tailWord_3375835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375835).length < 2 ^ (prefixWord ++ tailWord_3375835).sum := by decide
  have hdescent : baseEnd_3375835 < baseStart_3375835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375869 : List Nat := [1, 4, 1, 1, 1, 1, 4, 5, 5]
def baseStart_3375869 : Nat := 118140960795 + 3375869 * 2 ^ 59
def prefixEnd_3375869 : Nat := 4983230072969 + 3 ^ 40 * 3375869 * 2
def baseEnd_3375869 : Nat := 192604824845906403412463

theorem tailTrace_3375869 : CollatzResearch.WordTrace tailWord_3375869 prefixEnd_3375869 192604824845906403412463 := by
  unfold tailWord_3375869
  simp only [CollatzResearch.WordTrace]
  refine ⟨123128057806810640368618661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82085371871207093579079107 123128057806810640368618661)
  ·
    refine ⟨23086510838776995069115999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123128057806810640368618661 23086510838776995069115999)
    ·
      refine ⟨34629766258165492603673999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23086510838776995069115999 34629766258165492603673999)
      ·
        refine ⟨51944649387248238905510999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34629766258165492603673999 51944649387248238905510999)
        ·
          refine ⟨77916974080872358358266499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51944649387248238905510999 77916974080872358358266499)
          ·
            refine ⟨116875461121308537537399749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77916974080872358358266499 116875461121308537537399749)
            ·
              refine ⟨21914148960245350788262453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116875461121308537537399749 21914148960245350788262453)
              ·
                refine ⟨2054451465023001636399605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21914148960245350788262453 2054451465023001636399605)
                ·
                  refine ⟨192604824845906403412463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2054451465023001636399605 192604824845906403412463)
                  ·
                    rfl

theorem cell23_3375869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_3375869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375869 prefixEnd_3375869 := by exact prefixLift 3375869
  have htrace : WordTrace (prefixWord ++ tailWord_3375869) baseStart_3375869 baseEnd_3375869 := by
    simpa [prefixWord, tailWord_3375869, baseEnd_3375869] using wordTrace_append hprefix tailTrace_3375869
  have hstable : (prefixWord ++ tailWord_3375869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375869).length < 2 ^ (prefixWord ++ tailWord_3375869).sum := by decide
  have hdescent : baseEnd_3375869 < baseStart_3375869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375889 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 2, 5, 2]
def baseStart_3375889 : Nat := 118140960795 + 3375889 * 2 ^ 59
def prefixEnd_3375889 : Nat := 4983230072969 + 3 ^ 40 * 3375889 * 2
def baseEnd_3375889 : Nat := 1733453693226247552462075

theorem tailTrace_3375889 : CollatzResearch.WordTrace tailWord_3375889 prefixEnd_3375889 1733453693226247552462075 := by
  unfold tailWord_3375889
  simp only [CollatzResearch.WordTrace]
  refine ⟨123128787266738183784346721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82085858177825455856231147 123128787266738183784346721)
  ·
    refine ⟨92346590450053637838260041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123128787266738183784346721 92346590450053637838260041)
    ·
      refine ⟨69259942837540228378695031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92346590450053637838260041 69259942837540228378695031)
      ·
        refine ⟨103889914256310342568042547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69259942837540228378695031 103889914256310342568042547)
        ·
          refine ⟨155834871384465513852063821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103889914256310342568042547 155834871384465513852063821)
          ·
            refine ⟨58438076769174567694523933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155834871384465513852063821 58438076769174567694523933)
            ·
              refine ⟨21914278788440462885446475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58438076769174567694523933 21914278788440462885446475)
              ·
                refine ⟨32871418182660694328169713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21914278788440462885446475 32871418182660694328169713)
                ·
                  refine ⟨24653563636995520746127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32871418182660694328169713 24653563636995520746127285)
                  ·
                    refine ⟨2311271590968330069949433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24653563636995520746127285 2311271590968330069949433)
                    ·
                      refine ⟨1733453693226247552462075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311271590968330069949433 1733453693226247552462075)
                      ·
                        rfl

theorem cell23_3375889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_3375889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375889 prefixEnd_3375889 := by exact prefixLift 3375889
  have htrace : WordTrace (prefixWord ++ tailWord_3375889) baseStart_3375889 baseEnd_3375889 := by
    simpa [prefixWord, tailWord_3375889, baseEnd_3375889] using wordTrace_append hprefix tailTrace_3375889
  have hstable : (prefixWord ++ tailWord_3375889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375889).length < 2 ^ (prefixWord ++ tailWord_3375889).sum := by decide
  have hdescent : baseEnd_3375889 < baseStart_3375889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375919 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 6, 4, 2]
def baseStart_3375919 : Nat := 118140960795 + 3375919 * 2 ^ 59
def prefixEnd_3375919 : Nat := 4983230072969 + 3 ^ 40 * 3375919 * 2
def baseEnd_3375919 : Nat := 1733469097645882435086937

theorem tailTrace_3375919 : CollatzResearch.WordTrace tailWord_3375919 prefixEnd_3375919 1733469097645882435086937 := by
  unfold tailWord_3375919
  simp only [CollatzResearch.WordTrace]
  refine ⟨123129881456629498907938811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82086587637752999271959207 123129881456629498907938811)
  ·
    refine ⟨184694822184944248361908217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123129881456629498907938811 184694822184944248361908217)
    ·
      refine ⟨138521116638708186271431163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184694822184944248361908217 138521116638708186271431163)
      ·
        refine ⟨207781674958062279407146745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138521116638708186271431163 207781674958062279407146745)
        ·
          refine ⟨155836256218546709555360059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207781674958062279407146745 155836256218546709555360059)
          ·
            refine ⟨233754384327820064333040089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155836256218546709555360059 233754384327820064333040089)
            ·
              refine ⟨175315788245865048249780067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233754384327820064333040089 175315788245865048249780067)
              ·
                refine ⟨262973682368797572374670101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175315788245865048249780067 262973682368797572374670101)
                ·
                  refine ⟨12326891361037386205062661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 262973682368797572374670101 12326891361037386205062661)
                  ·
                    refine ⟨2311292130194509913449249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12326891361037386205062661 2311292130194509913449249)
                    ·
                      refine ⟨1733469097645882435086937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311292130194509913449249 1733469097645882435086937)
                      ·
                        rfl

theorem cell23_3375919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 4, 2].length) (baseStart_3375919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375919 prefixEnd_3375919 := by exact prefixLift 3375919
  have htrace : WordTrace (prefixWord ++ tailWord_3375919) baseStart_3375919 baseEnd_3375919 := by
    simpa [prefixWord, tailWord_3375919, baseEnd_3375919] using wordTrace_append hprefix tailTrace_3375919
  have hstable : (prefixWord ++ tailWord_3375919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375919).length < 2 ^ (prefixWord ++ tailWord_3375919).sum := by decide
  have hdescent : baseEnd_3375919 < baseStart_3375919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375939 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 3]
def baseStart_3375939 : Nat := 118140960795 + 3375939 * 2 ^ 59
def prefixEnd_3375939 : Nat := 4983230072969 + 3 ^ 40 * 3375939 * 2
def baseEnd_3375939 : Nat := 1733479367258972356836845

theorem tailTrace_3375939 : CollatzResearch.WordTrace tailWord_3375939 prefixEnd_3375939 1733479367258972356836845 := by
  unfold tailWord_3375939
  simp only [CollatzResearch.WordTrace]
  refine ⟨123130610916557042323666871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82087073944371361549111247 123130610916557042323666871)
  ·
    refine ⟨184695916374835563485500307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123130610916557042323666871 184695916374835563485500307)
    ·
      refine ⟨277043874562253345228250461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184695916374835563485500307 277043874562253345228250461)
      ·
        refine ⟨103891452960845004460593923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277043874562253345228250461 103891452960845004460593923)
        ·
          refine ⟨155837179441267506690890885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103891452960845004460593923 155837179441267506690890885)
          ·
            refine ⟨29219471145237657504542041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155837179441267506690890885 29219471145237657504542041)
            ·
              refine ⟨21914603358928243128406531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29219471145237657504542041 21914603358928243128406531)
              ·
                refine ⟨32871905038392364692609797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21914603358928243128406531 32871905038392364692609797)
                ·
                  refine ⟨6163482194698568379864337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32871905038392364692609797 6163482194698568379864337)
                  ·
                    refine ⟨4622611646023926284898253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6163482194698568379864337 4622611646023926284898253)
                    ·
                      refine ⟨1733479367258972356836845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622611646023926284898253 1733479367258972356836845)
                      ·
                        rfl

theorem cell23_3375939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 4, 2, 3].length) (baseStart_3375939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375939 prefixEnd_3375939 := by exact prefixLift 3375939
  have htrace : WordTrace (prefixWord ++ tailWord_3375939) baseStart_3375939 baseEnd_3375939 := by
    simpa [prefixWord, tailWord_3375939, baseEnd_3375939] using wordTrace_append hprefix tailTrace_3375939
  have hstable : (prefixWord ++ tailWord_3375939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375939).length < 2 ^ (prefixWord ++ tailWord_3375939).sum := by decide
  have hdescent : baseEnd_3375939 < baseStart_3375939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3375986 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 5, 1, 3]
def baseStart_3375986 : Nat := 118140960795 + 3375986 * 2 ^ 59
def prefixEnd_3375986 : Nat := 4983230072969 + 3 ^ 40 * 3375986 * 2
def baseEnd_3375986 : Nat := 1733503500849733672949129

theorem tailTrace_3375986 : CollatzResearch.WordTrace tailWord_3375986 prefixEnd_3375986 1733503500849733672949129 := by
  unfold tailWord_3375986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30783081286846692337656953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82088216764924512900418541 30783081286846692337656953)
  ·
    refine ⟨23087310965135019253242715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30783081286846692337656953 23087310965135019253242715)
    ·
      refine ⟨34630966447702528879864073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23087310965135019253242715 34630966447702528879864073)
      ·
        refine ⟨25973224835776896659898055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34630966447702528879864073 25973224835776896659898055)
        ·
          refine ⟨38959837253665344989847083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25973224835776896659898055 38959837253665344989847083)
          ·
            refine ⟨58439755880498017484770625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38959837253665344989847083 58439755880498017484770625)
            ·
              refine ⟨43829816910373513113577969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58439755880498017484770625 43829816910373513113577969)
              ·
                refine ⟨32872362682780134835183477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43829816910373513113577969 32872362682780134835183477)
                ·
                  refine ⟨3081784001510637640798451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32872362682780134835183477 3081784001510637640798451)
                  ·
                    refine ⟨4622676002265956461197677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081784001510637640798451 4622676002265956461197677)
                    ·
                      refine ⟨1733503500849733672949129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622676002265956461197677 1733503500849733672949129)
                      ·
                        rfl

theorem cell23_3375986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_3375986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3375986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3375986 prefixEnd_3375986 := by exact prefixLift 3375986
  have htrace : WordTrace (prefixWord ++ tailWord_3375986) baseStart_3375986 baseEnd_3375986 := by
    simpa [prefixWord, tailWord_3375986, baseEnd_3375986] using wordTrace_append hprefix tailTrace_3375986
  have hstable : (prefixWord ++ tailWord_3375986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3375986).length < 2 ^ (prefixWord ++ tailWord_3375986).sum := by decide
  have hdescent : baseEnd_3375986 < baseStart_3375986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3375986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376019 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 6, 4]
def baseStart_3376019 : Nat := 118140960795 + 3376019 * 2 ^ 59
def prefixEnd_3376019 : Nat := 4983230072969 + 3 ^ 40 * 3376019 * 2
def baseEnd_3376019 : Nat := 577840148570444014612159

theorem tailTrace_3376019 : CollatzResearch.WordTrace tailWord_3376019 prefixEnd_3376019 577840148570444014612159 := by
  unfold tailWord_3376019
  simp only [CollatzResearch.WordTrace]
  refine ⟨123133528756267215986579111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82089019170844810657719407 123133528756267215986579111)
  ·
    refine ⟨184700293134400823979868667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123133528756267215986579111 184700293134400823979868667)
    ·
      refine ⟨277050439701601235969803001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184700293134400823979868667 277050439701601235969803001)
      ·
        refine ⟨207787829776200926977352251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277050439701601235969803001 207787829776200926977352251)
        ·
          refine ⟨311681744664301390466028377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207787829776200926977352251 311681744664301390466028377)
          ·
            refine ⟨233761308498226042849521283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311681744664301390466028377 233761308498226042849521283)
            ·
              refine ⟨350641962747339064274281925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233761308498226042849521283 350641962747339064274281925)
              ·
                refine ⟨65745368015126074551427861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350641962747339064274281925 65745368015126074551427861)
                ·
                  refine ⟨3081814125709034744598181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65745368015126074551427861 3081814125709034744598181)
                  ·
                    refine ⟨577840148570444014612159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081814125709034744598181 577840148570444014612159)
                    ·
                      rfl

theorem cell23_3376019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 6, 4].length) (baseStart_3376019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376019 prefixEnd_3376019 := by exact prefixLift 3376019
  have htrace : WordTrace (prefixWord ++ tailWord_3376019) baseStart_3376019 baseEnd_3376019 := by
    simpa [prefixWord, tailWord_3376019, baseEnd_3376019] using wordTrace_append hprefix tailTrace_3376019
  have hstable : (prefixWord ++ tailWord_3376019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376019).length < 2 ^ (prefixWord ++ tailWord_3376019).sum := by decide
  have hdescent : baseEnd_3376019 < baseStart_3376019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376049 : List Nat := [1, 2, 2, 4, 3, 11]
def baseStart_3376049 : Nat := 118140960795 + 3376049 * 2 ^ 59
def prefixEnd_3376049 : Nat := 4983230072969 + 3 ^ 40 * 3376049 * 2
def baseEnd_3376049 : Nat := 7133892387370234265273

theorem tailTrace_3376049 : CollatzResearch.WordTrace tailWord_3376049 prefixEnd_3376049 7133892387370234265273 := by
  unfold tailWord_3376049
  simp only [CollatzResearch.WordTrace]
  refine ⟨123134622946158531110171201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82089748630772354073447467 123134622946158531110171201)
  ·
    refine ⟨92350967209618898332628401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123134622946158531110171201 92350967209618898332628401)
    ·
      refine ⟨69263225407214173749471301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92350967209618898332628401 69263225407214173749471301)
      ·
        refine ⟨12986854763852657578025869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69263225407214173749471301 12986854763852657578025869)
        ·
          refine ⟨4870070536444746591759701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12986854763852657578025869 4870070536444746591759701)
          ·
            refine ⟨7133892387370234265273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4870070536444746591759701 7133892387370234265273)
            ·
              rfl

theorem cell23_3376049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 11].length) (baseStart_3376049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376049 prefixEnd_3376049 := by exact prefixLift 3376049
  have htrace : WordTrace (prefixWord ++ tailWord_3376049) baseStart_3376049 baseEnd_3376049 := by
    simpa [prefixWord, tailWord_3376049, baseEnd_3376049] using wordTrace_append hprefix tailTrace_3376049
  have hstable : (prefixWord ++ tailWord_3376049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376049).length < 2 ^ (prefixWord ++ tailWord_3376049).sum := by decide
  have hdescent : baseEnd_3376049 < baseStart_3376049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376053 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3376053 : Nat := 118140960795 + 3376053 * 2 ^ 59
def prefixEnd_3376053 : Nat := 4983230072969 + 3 ^ 40 * 3376053 * 2
def baseEnd_3376053 : Nat := 577845968017861636937107

theorem tailTrace_3376053 : CollatzResearch.WordTrace tailWord_3376053 prefixEnd_3376053 577845968017861636937107 := by
  unfold tailWord_3376053
  simp only [CollatzResearch.WordTrace]
  refine ⟨123134768838144039793316813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82089845892096026528877875 123134768838144039793316813)
  ·
    refine ⟨46175538314304014922493805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123134768838144039793316813 46175538314304014922493805)
    ·
      refine ⟨17315826867864005595935177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46175538314304014922493805 17315826867864005595935177)
      ·
        refine ⟨12986870150898004196951383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17315826867864005595935177 12986870150898004196951383)
        ·
          refine ⟨19480305226347006295427075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12986870150898004196951383 19480305226347006295427075)
          ·
            refine ⟨29220457839520509443140613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19480305226347006295427075 29220457839520509443140613)
            ·
              refine ⟨5478835844910095520588865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29220457839520509443140613 5478835844910095520588865)
              ·
                refine ⟨4109126883682571640441649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5478835844910095520588865 4109126883682571640441649)
                ·
                  refine ⟨3081845162761928730331237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109126883682571640441649 3081845162761928730331237)
                  ·
                    refine ⟨577845968017861636937107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3081845162761928730331237 577845968017861636937107)
                    ·
                      rfl

theorem cell23_3376053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3376053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376053 prefixEnd_3376053 := by exact prefixLift 3376053
  have htrace : WordTrace (prefixWord ++ tailWord_3376053) baseStart_3376053 baseEnd_3376053 := by
    simpa [prefixWord, tailWord_3376053, baseEnd_3376053] using wordTrace_append hprefix tailTrace_3376053
  have hstable : (prefixWord ++ tailWord_3376053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376053).length < 2 ^ (prefixWord ++ tailWord_3376053).sum := by decide
  have hdescent : baseEnd_3376053 < baseStart_3376053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376093 : List Nat := [1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3376093 : Nat := 118140960795 + 3376093 * 2 ^ 59
def prefixEnd_3376093 : Nat := 4983230072969 + 3 ^ 40 * 3376093 * 2
def baseEnd_3376093 : Nat := 1733558443279764754311137

theorem tailTrace_3376093 : CollatzResearch.WordTrace tailWord_3376093 prefixEnd_3376093 1733558443279764754311137 := by
  unfold tailWord_3376093
  simp only [CollatzResearch.WordTrace]
  refine ⟨123136227757999126624772933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82090818505332751083181955 123136227757999126624772933)
  ·
    refine ⟨23088042704624836242144925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123136227757999126624772933 23088042704624836242144925)
    ·
      refine ⟨8658016014234313590804347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23088042704624836242144925 8658016014234313590804347)
      ·
        refine ⟨12987024021351470386206521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8658016014234313590804347 12987024021351470386206521)
        ·
          refine ⟨9740268016013602789654891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12987024021351470386206521 9740268016013602789654891)
          ·
            refine ⟨14610402024020404184482337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740268016013602789654891 14610402024020404184482337)
            ·
              refine ⟨10957801518015303138361753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610402024020404184482337 10957801518015303138361753)
              ·
                refine ⟨8218351138511477353771315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10957801518015303138361753 8218351138511477353771315)
                ·
                  refine ⟨12327526707767216030656973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8218351138511477353771315 12327526707767216030656973)
                  ·
                    refine ⟨4622822515412706011496365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12327526707767216030656973 4622822515412706011496365)
                    ·
                      refine ⟨1733558443279764754311137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622822515412706011496365 1733558443279764754311137)
                      ·
                        rfl

theorem cell23_3376093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3376093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376093 prefixEnd_3376093 := by exact prefixLift 3376093
  have htrace : WordTrace (prefixWord ++ tailWord_3376093) baseStart_3376093 baseEnd_3376093 := by
    simpa [prefixWord, tailWord_3376093, baseEnd_3376093] using wordTrace_append hprefix tailTrace_3376093
  have hstable : (prefixWord ++ tailWord_3376093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376093).length < 2 ^ (prefixWord ++ tailWord_3376093).sum := by decide
  have hdescent : baseEnd_3376093 < baseStart_3376093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376110 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3]
def baseStart_3376110 : Nat := 118140960795 + 3376110 * 2 ^ 59
def prefixEnd_3376110 : Nat := 4983230072969 + 3 ^ 40 * 3376110 * 2
def baseEnd_3376110 : Nat := 1733567172450891187798559

theorem tailTrace_3376110 : CollatzResearch.WordTrace tailWord_3376110 prefixEnd_3376110 1733567172450891187798559 := by
  unfold tailWord_3376110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392105974867192316017723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82091231865958359018761189 15392105974867192316017723)
  ·
    refine ⟨23088158962300788474026585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15392105974867192316017723 23088158962300788474026585)
    ·
      refine ⟨17316119221725591355519939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23088158962300788474026585 17316119221725591355519939)
      ·
        refine ⟨25974178832588387033279909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316119221725591355519939 25974178832588387033279909)
        ·
          refine ⟨4870158531110322568739983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25974178832588387033279909 4870158531110322568739983)
          ·
            refine ⟨7305237796665483853109975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870158531110322568739983 7305237796665483853109975)
            ·
              refine ⟨10957856694998225779664963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305237796665483853109975 10957856694998225779664963)
              ·
                refine ⟨16436785042497338669497445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10957856694998225779664963 16436785042497338669497445)
                ·
                  refine ⟨3081897195468251000530771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16436785042497338669497445 3081897195468251000530771)
                  ·
                    refine ⟨4622845793202376500796157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081897195468251000530771 4622845793202376500796157)
                    ·
                      refine ⟨1733567172450891187798559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4622845793202376500796157 1733567172450891187798559)
                      ·
                        rfl

theorem cell23_3376110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_3376110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376110 prefixEnd_3376110 := by exact prefixLift 3376110
  have htrace : WordTrace (prefixWord ++ tailWord_3376110) baseStart_3376110 baseEnd_3376110 := by
    simpa [prefixWord, tailWord_3376110, baseEnd_3376110] using wordTrace_append hprefix tailTrace_3376110
  have hstable : (prefixWord ++ tailWord_3376110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376110).length < 2 ^ (prefixWord ++ tailWord_3376110).sum := by decide
  have hdescent : baseEnd_3376110 < baseStart_3376110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376167 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3376167 : Nat := 118140960795 + 3376167 * 2 ^ 59
def prefixEnd_3376167 : Nat := 4983230072969 + 3 ^ 40 * 3376167 * 2
def baseEnd_3376167 : Nat := 1733596440848197464785797

theorem tailTrace_3376167 : CollatzResearch.WordTrace tailWord_3376167 prefixEnd_3376167 1733596440848197464785797 := by
  unfold tailWord_3376167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123138926759731037262966755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82092617839820691508644503 123138926759731037262966755)
  ·
    refine ⟨184708390139596555894450133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123138926759731037262966755 184708390139596555894450133)
    ·
      refine ⟨4329102893896794278776175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 184708390139596555894450133 4329102893896794278776175)
      ·
        refine ⟨6493654340845191418164263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329102893896794278776175 6493654340845191418164263)
        ·
          refine ⟨9740481511267787127246395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493654340845191418164263 9740481511267787127246395)
          ·
            refine ⟨14610722266901680690869593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740481511267787127246395 14610722266901680690869593)
            ·
              refine ⟨10958041700176260518152195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610722266901680690869593 10958041700176260518152195)
              ·
                refine ⟨16437062550264390777228293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10958041700176260518152195 16437062550264390777228293)
                ·
                  refine ⟨3081949228174573270730305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16437062550264390777228293 3081949228174573270730305)
                  ·
                    refine ⟨2311461921130929953047729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3081949228174573270730305 2311461921130929953047729)
                    ·
                      refine ⟨1733596440848197464785797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311461921130929953047729 1733596440848197464785797)
                      ·
                        rfl

theorem cell23_3376167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3376167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376167 prefixEnd_3376167 := by exact prefixLift 3376167
  have htrace : WordTrace (prefixWord ++ tailWord_3376167) baseStart_3376167 baseEnd_3376167 := by
    simpa [prefixWord, tailWord_3376167, baseEnd_3376167] using wordTrace_append hprefix tailTrace_3376167
  have hstable : (prefixWord ++ tailWord_3376167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376167).length < 2 ^ (prefixWord ++ tailWord_3376167).sum := by decide
  have hdescent : baseEnd_3376167 < baseStart_3376167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376184 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 2, 2, 2]
def baseStart_3376184 : Nat := 118140960795 + 3376184 * 2 ^ 59
def prefixEnd_3376184 : Nat := 4983230072969 + 3 ^ 40 * 3376184 * 2
def baseEnd_3376184 : Nat := 1733605170019323898273219

theorem tailTrace_3376184 : CollatzResearch.WordTrace tailWord_3376184 prefixEnd_3376184 1733605170019323898273219 := by
  unfold tailWord_3376184
  simp only [CollatzResearch.WordTrace]
  refine ⟨61569773400334724583167803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82093031200446299444223737 61569773400334724583167803)
  ·
    refine ⟨92354660100502086874751705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61569773400334724583167803 92354660100502086874751705)
    ·
      refine ⟨69265995075376565156063779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92354660100502086874751705 69265995075376565156063779)
      ·
        refine ⟨103898992613064847734095669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69265995075376565156063779 103898992613064847734095669)
        ·
          refine ⟨9740530557474829475071469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103898992613064847734095669 9740530557474829475071469)
          ·
            refine ⟨3652698959053061053151801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9740530557474829475071469 3652698959053061053151801)
            ·
              refine ⟨2739524219289795789863851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652698959053061053151801 2739524219289795789863851)
              ·
                refine ⟨4109286328934693684795777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739524219289795789863851 4109286328934693684795777)
                ·
                  refine ⟨3081964746701020263596833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109286328934693684795777 3081964746701020263596833)
                  ·
                    refine ⟨2311473560025765197697625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3081964746701020263596833 2311473560025765197697625)
                    ·
                      refine ⟨1733605170019323898273219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311473560025765197697625 1733605170019323898273219)
                      ·
                        rfl

theorem cell23_3376184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 2, 2, 2].length) (baseStart_3376184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376184 prefixEnd_3376184 := by exact prefixLift 3376184
  have htrace : WordTrace (prefixWord ++ tailWord_3376184) baseStart_3376184 baseEnd_3376184 := by
    simpa [prefixWord, tailWord_3376184, baseEnd_3376184] using wordTrace_append hprefix tailTrace_3376184
  have hstable : (prefixWord ++ tailWord_3376184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376184).length < 2 ^ (prefixWord ++ tailWord_3376184).sum := by decide
  have hdescent : baseEnd_3376184 < baseStart_3376184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376223 : List Nat := [1, 1, 2, 3, 1, 1, 4, 2, 2, 4, 2]
def baseStart_3376223 : Nat := 118140960795 + 3376223 * 2 ^ 59
def prefixEnd_3376223 : Nat := 4983230072969 + 3 ^ 40 * 3376223 * 2
def baseEnd_3376223 : Nat := 1733625195764849245685539

theorem tailTrace_3376223 : CollatzResearch.WordTrace tailWord_3376223 prefixEnd_3376223 1733625195764849245685539 := by
  unfold tailWord_3376223
  simp only [CollatzResearch.WordTrace]
  refine ⟨123140969247528158827005323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82093979498352105884670215 123140969247528158827005323)
  ·
    refine ⟨184711453871292238240507985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123140969247528158827005323 184711453871292238240507985)
    ·
      refine ⟨138533590403469178680380989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184711453871292238240507985 138533590403469178680380989)
      ·
        refine ⟨51950096401300942005142871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138533590403469178680380989 51950096401300942005142871)
        ·
          refine ⟨77925144601951413007714307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51950096401300942005142871 77925144601951413007714307)
          ·
            refine ⟨116887716902927119511571461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77925144601951413007714307 116887716902927119511571461)
            ·
              refine ⟨21916446919298834908419649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116887716902927119511571461 21916446919298834908419649)
              ·
                refine ⟨16437335189474126181314737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21916446919298834908419649 16437335189474126181314737)
                ·
                  refine ⟨12328001392105594635986053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16437335189474126181314737 12328001392105594635986053)
                  ·
                    refine ⟨2311500261019798994247385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12328001392105594635986053 2311500261019798994247385)
                    ·
                      refine ⟨1733625195764849245685539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311500261019798994247385 1733625195764849245685539)
                      ·
                        rfl

theorem cell23_3376223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_3376223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376223 prefixEnd_3376223 := by exact prefixLift 3376223
  have htrace : WordTrace (prefixWord ++ tailWord_3376223) baseStart_3376223 baseEnd_3376223 := by
    simpa [prefixWord, tailWord_3376223, baseEnd_3376223] using wordTrace_append hprefix tailTrace_3376223
  have hstable : (prefixWord ++ tailWord_3376223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376223).length < 2 ^ (prefixWord ++ tailWord_3376223).sum := by decide
  have hdescent : baseEnd_3376223 < baseStart_3376223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376260 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_3376260 : Nat := 118140960795 + 3376260 * 2 ^ 59
def prefixEnd_3376260 : Nat := 4983230072969 + 3 ^ 40 * 3376260 * 2
def baseEnd_3376260 : Nat := 1733644194549065600922869

theorem tailTrace_3376260 : CollatzResearch.WordTrace tailWord_3376260 prefixEnd_3376260 1733644194549065600922869 := by
  unfold tailWord_3376260
  simp only [CollatzResearch.WordTrace]
  refine ⟨61571159374197057073051117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82094879165596076097401489 61571159374197057073051117)
  ·
    refine ⟨23089184765323896402394169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61571159374197057073051117 23089184765323896402394169)
    ·
      refine ⟨17316888573992922301795627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23089184765323896402394169 17316888573992922301795627)
      ·
        refine ⟨25975332860989383452693441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17316888573992922301795627 25975332860989383452693441)
        ·
          refine ⟨19481499645742037589520081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25975332860989383452693441 19481499645742037589520081)
          ·
            refine ⟨14611124734306528192140061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19481499645742037589520081 14611124734306528192140061)
            ·
              refine ⟨5479171775364948072052523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14611124734306528192140061 5479171775364948072052523)
              ·
                refine ⟨8218757663047422108078785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479171775364948072052523 8218757663047422108078785)
                ·
                  refine ⟨6164068247285566581059089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8218757663047422108078785 6164068247285566581059089)
                  ·
                    refine ⟨4623051185464174935794317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164068247285566581059089 4623051185464174935794317)
                    ·
                      refine ⟨1733644194549065600922869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4623051185464174935794317 1733644194549065600922869)
                      ·
                        rfl

theorem cell23_3376260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_3376260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376260 prefixEnd_3376260 := by exact prefixLift 3376260
  have htrace : WordTrace (prefixWord ++ tailWord_3376260) baseStart_3376260 baseEnd_3376260 := by
    simpa [prefixWord, tailWord_3376260, baseEnd_3376260] using wordTrace_append hprefix tailTrace_3376260
  have hstable : (prefixWord ++ tailWord_3376260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376260).length < 2 ^ (prefixWord ++ tailWord_3376260).sum := by decide
  have hdescent : baseEnd_3376260 < baseStart_3376260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376280 : List Nat := [2, 1, 2, 4, 2, 3, 1, 2, 6]
def baseStart_3376280 : Nat := 118140960795 + 3376280 * 2 ^ 59
def prefixEnd_3376280 : Nat := 4983230072969 + 3 ^ 40 * 3376280 * 2
def baseEnd_3376280 : Nat := 192628273795795058074753

theorem tailTrace_3376280 : CollatzResearch.WordTrace tailWord_3376280 prefixEnd_3376280 192628273795795058074753 := by
  unfold tailWord_3376280
  simp only [CollatzResearch.WordTrace]
  refine ⟨61571524104160828780915147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82095365472214438374553529 61571524104160828780915147)
  ·
    refine ⟨92357286156241243171372721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61571524104160828780915147 92357286156241243171372721)
    ·
      refine ⟨69267964617180932378529541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92357286156241243171372721 69267964617180932378529541)
      ·
        refine ⟨12987743365721424820974289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69267964617180932378529541 12987743365721424820974289)
        ·
          refine ⟨9740807524291068615730717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12987743365721424820974289 9740807524291068615730717)
          ·
            refine ⟨3652802821609150730899019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9740807524291068615730717 3652802821609150730899019)
            ·
              refine ⟨5479204232413726096348529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652802821609150730899019 5479204232413726096348529)
              ·
                refine ⟨4109403174310294572261397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5479204232413726096348529 4109403174310294572261397)
                ·
                  refine ⟨192628273795795058074753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4109403174310294572261397 192628273795795058074753)
                  ·
                    rfl

theorem cell23_3376280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 2, 6].length) (baseStart_3376280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376280 prefixEnd_3376280 := by exact prefixLift 3376280
  have htrace : WordTrace (prefixWord ++ tailWord_3376280) baseStart_3376280 baseEnd_3376280 := by
    simpa [prefixWord, tailWord_3376280, baseEnd_3376280] using wordTrace_append hprefix tailTrace_3376280
  have hstable : (prefixWord ++ tailWord_3376280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376280).length < 2 ^ (prefixWord ++ tailWord_3376280).sum := by decide
  have hdescent : baseEnd_3376280 < baseStart_3376280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376330 : List Nat := [3, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_3376330 : Nat := 118140960795 + 3376330 * 2 ^ 59
def prefixEnd_3376330 : Nat := 4983230072969 + 3 ^ 40 * 3376330 * 2
def baseEnd_3376330 : Nat := 1733680138194880327047547

theorem tailTrace_3376330 : CollatzResearch.WordTrace tailWord_3376330 prefixEnd_3376330 1733680138194880327047547 := by
  unfold tailWord_3376330
  simp only [CollatzResearch.WordTrace]
  refine ⟨30786217964535129025287611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82096581238760344067433629 30786217964535129025287611)
  ·
    refine ⟨46179326946802693537931417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30786217964535129025287611 46179326946802693537931417)
    ·
      refine ⟨34634495210102020153448563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46179326946802693537931417 34634495210102020153448563)
      ·
        refine ⟨51951742815153030230172845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34634495210102020153448563 51951742815153030230172845)
        ·
          refine ⟨19481903555682386336314817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51951742815153030230172845 19481903555682386336314817)
          ·
            refine ⟨14611427666761789752236113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19481903555682386336314817 14611427666761789752236113)
            ·
              refine ⟨10958570750071342314177085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14611427666761789752236113 10958570750071342314177085)
              ·
                refine ⟨4109464031276753367816407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10958570750071342314177085 4109464031276753367816407)
                ·
                  refine ⟨6164196046915130051724611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109464031276753367816407 6164196046915130051724611)
                  ·
                    refine ⟨9246294070372695077586917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6164196046915130051724611 9246294070372695077586917)
                    ·
                      refine ⟨1733680138194880327047547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9246294070372695077586917 1733680138194880327047547)
                      ·
                        rfl

theorem cell23_3376330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_3376330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376330 prefixEnd_3376330 := by exact prefixLift 3376330
  have htrace : WordTrace (prefixWord ++ tailWord_3376330) baseStart_3376330 baseEnd_3376330 := by
    simpa [prefixWord, tailWord_3376330, baseEnd_3376330] using wordTrace_append hprefix tailTrace_3376330
  have hstable : (prefixWord ++ tailWord_3376330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376330).length < 2 ^ (prefixWord ++ tailWord_3376330).sum := by decide
  have hdescent : baseEnd_3376330 < baseStart_3376330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376341 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3376341 : Nat := 118140960795 + 3376341 * 2 ^ 59
def prefixEnd_3376341 : Nat := 4983230072969 + 3 ^ 40 * 3376341 * 2
def baseEnd_3376341 : Nat := 1733685786482079784009997

theorem tailTrace_3376341 : CollatzResearch.WordTrace tailWord_3376341 prefixEnd_3376341 1733685786482079784009997 := by
  unfold tailWord_3376341
  simp only [CollatzResearch.WordTrace]
  refine ⟨123145273061100664979800877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82096848707400443319867251 123145273061100664979800877)
  ·
    refine ⟨46179477397912749367425329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123145273061100664979800877 46179477397912749367425329)
    ·
      refine ⟨34634608048434562025568997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46179477397912749367425329 34634608048434562025568997)
      ·
        refine ⟨6493989009081480379794187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34634608048434562025568997 6493989009081480379794187)
        ·
          refine ⟨9740983513622220569691281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493989009081480379794187 9740983513622220569691281)
          ·
            refine ⟨7305737635216665427268461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9740983513622220569691281 7305737635216665427268461)
            ·
              refine ⟨2739651613206249535225673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7305737635216665427268461 2739651613206249535225673)
              ·
                refine ⟨2054738709904687151419255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739651613206249535225673 2054738709904687151419255)
                ·
                  refine ⟨3082108064857030727128883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054738709904687151419255 3082108064857030727128883)
                  ·
                    refine ⟨4623162097285546090693325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3082108064857030727128883 4623162097285546090693325)
                    ·
                      refine ⟨1733685786482079784009997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4623162097285546090693325 1733685786482079784009997)
                      ·
                        rfl

theorem cell23_3376341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3376341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376341 prefixEnd_3376341 := by exact prefixLift 3376341
  have htrace : WordTrace (prefixWord ++ tailWord_3376341) baseStart_3376341 baseEnd_3376341 := by
    simpa [prefixWord, tailWord_3376341, baseEnd_3376341] using wordTrace_append hprefix tailTrace_3376341
  have hstable : (prefixWord ++ tailWord_3376341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376341).length < 2 ^ (prefixWord ++ tailWord_3376341).sum := by decide
  have hdescent : baseEnd_3376341 < baseStart_3376341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376353 : List Nat := [1, 2, 3, 1, 3, 3, 2, 8]
def baseStart_3376353 : Nat := 118140960795 + 3376353 * 2 ^ 59
def prefixEnd_3376353 : Nat := 4983230072969 + 3 ^ 40 * 3376353 * 2
def baseEnd_3376353 : Nat := 64210812898145693965183

theorem tailTrace_3376353 : CollatzResearch.WordTrace tailWord_3376353 prefixEnd_3376353 64210812898145693965183 := by
  unfold tailWord_3376353
  simp only [CollatzResearch.WordTrace]
  refine ⟨123145710737057191029237713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82097140491371460686158475 123145710737057191029237713)
  ·
    refine ⟨92359283052792893271928285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123145710737057191029237713 92359283052792893271928285)
    ·
      refine ⟨34634731144797334976973107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92359283052792893271928285 34634731144797334976973107)
      ·
        refine ⟨51952096717196002465459661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34634731144797334976973107 51952096717196002465459661)
        ·
          refine ⟨19482036268948500924547373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51952096717196002465459661 19482036268948500924547373)
          ·
            refine ⟨7305763600855687846705265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19482036268948500924547373 7305763600855687846705265)
            ·
              refine ⟨5479322700641765885028949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305763600855687846705265 5479322700641765885028949)
              ·
                refine ⟨64210812898145693965183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5479322700641765885028949 64210812898145693965183)
                ·
                  rfl

theorem cell23_3376353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 8].length) (baseStart_3376353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376353 prefixEnd_3376353 := by exact prefixLift 3376353
  have htrace : WordTrace (prefixWord ++ tailWord_3376353) baseStart_3376353 baseEnd_3376353 := by
    simpa [prefixWord, tailWord_3376353, baseEnd_3376353] using wordTrace_append hprefix tailTrace_3376353
  have hstable : (prefixWord ++ tailWord_3376353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376353).length < 2 ^ (prefixWord ++ tailWord_3376353).sum := by decide
  have hdescent : baseEnd_3376353 < baseStart_3376353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376357 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 2, 4]
def baseStart_3376357 : Nat := 118140960795 + 3376357 * 2 ^ 59
def prefixEnd_3376357 : Nat := 4983230072969 + 3 ^ 40 * 3376357 * 2
def baseEnd_3376357 : Nat := 577898000724183907136641

theorem tailTrace_3376357 : CollatzResearch.WordTrace tailWord_3376357 prefixEnd_3376357 577898000724183907136641 := by
  unfold tailWord_3376357
  simp only [CollatzResearch.WordTrace]
  refine ⟨123145856629042699712383325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82097237752695133141588883 123145856629042699712383325)
  ·
    refine ⟨46179696235891012392143747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123145856629042699712383325 46179696235891012392143747)
    ·
      refine ⟨69269544353836518588215621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46179696235891012392143747 69269544353836518588215621)
      ·
        refine ⟨12988039566344347235290429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69269544353836518588215621 12988039566344347235290429)
        ·
          refine ⟨4870514837379130213233911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12988039566344347235290429 4870514837379130213233911)
          ·
            refine ⟨7305772256068695319850867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4870514837379130213233911 7305772256068695319850867)
            ·
              refine ⟨10958658384103042979776301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305772256068695319850867 10958658384103042979776301)
              ·
                refine ⟨4109496894038641117416113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10958658384103042979776301 4109496894038641117416113)
                ·
                  refine ⟨3082122670528980838062085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109496894038641117416113 3082122670528980838062085)
                  ·
                    refine ⟨577898000724183907136641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082122670528980838062085 577898000724183907136641)
                    ·
                      rfl

theorem cell23_3376357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_3376357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376357 prefixEnd_3376357 := by exact prefixLift 3376357
  have htrace : WordTrace (prefixWord ++ tailWord_3376357) baseStart_3376357 baseEnd_3376357 := by
    simpa [prefixWord, tailWord_3376357, baseEnd_3376357] using wordTrace_append hprefix tailTrace_3376357
  have hstable : (prefixWord ++ tailWord_3376357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376357).length < 2 ^ (prefixWord ++ tailWord_3376357).sum := by decide
  have hdescent : baseEnd_3376357 < baseStart_3376357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376398 : List Nat := [4, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2]
def baseStart_3376398 : Nat := 118140960795 + 3376398 * 2 ^ 59
def prefixEnd_3376398 : Nat := 4983230072969 + 3 ^ 40 * 3376398 * 2
def baseEnd_3376398 : Nat := 1733715054879386060997235

theorem tailTrace_3376398 : CollatzResearch.WordTrace tailWord_3376398 prefixEnd_3376398 1733715054879386060997235 := by
  unfold tailWord_3376398
  simp only [CollatzResearch.WordTrace]
  refine ⟨15393419002736770464328231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82098234681262775809750565 15393419002736770464328231)
  ·
    refine ⟨23090128504105155696492347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15393419002736770464328231 23090128504105155696492347)
    ·
      refine ⟨34635192756157733544738521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23090128504105155696492347 34635192756157733544738521)
      ·
        refine ⟨25976394567118300158553891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34635192756157733544738521 25976394567118300158553891)
        ·
          refine ⟨38964591850677450237830837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25976394567118300158553891 38964591850677450237830837)
          ·
            refine ⟨3652930486001010959796641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38964591850677450237830837 3652930486001010959796641)
            ·
              refine ⟨2739697864500758219847481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652930486001010959796641 2739697864500758219847481)
              ·
                refine ⟨2054773398375568664885611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739697864500758219847481 2054773398375568664885611)
                ·
                  refine ⟨3082160097563352997328417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054773398375568664885611 3082160097563352997328417)
                  ·
                    refine ⟨2311620073172514747996313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3082160097563352997328417 2311620073172514747996313)
                    ·
                      refine ⟨1733715054879386060997235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311620073172514747996313 1733715054879386060997235)
                      ·
                        rfl

theorem cell23_3376398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_3376398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376398 prefixEnd_3376398 := by exact prefixLift 3376398
  have htrace : WordTrace (prefixWord ++ tailWord_3376398) baseStart_3376398 baseEnd_3376398 := by
    simpa [prefixWord, tailWord_3376398, baseEnd_3376398] using wordTrace_append hprefix tailTrace_3376398
  have hstable : (prefixWord ++ tailWord_3376398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376398).length < 2 ^ (prefixWord ++ tailWord_3376398).sum := by decide
  have hdescent : baseEnd_3376398 < baseStart_3376398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376437 : List Nat := [1, 3, 3, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_3376437 : Nat := 118140960795 + 3376437 * 2 ^ 59
def prefixEnd_3376437 : Nat := 4983230072969 + 3 ^ 40 * 3376437 * 2
def baseEnd_3376437 : Nat := 1733735080624911408409555

theorem tailTrace_3376437 : CollatzResearch.WordTrace tailWord_3376437 prefixEnd_3376437 1733735080624911408409555 := by
  unfold tailWord_3376437
  simp only [CollatzResearch.WordTrace]
  refine ⟨123148774468752873375295565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82099182979168582250197043 123148774468752873375295565)
  ·
    refine ⟨46180790425782327515735837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123148774468752873375295565 46180790425782327515735837)
    ·
      refine ⟨17317796409668372818400939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46180790425782327515735837 17317796409668372818400939)
      ·
        refine ⟨25976694614502559227601409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17317796409668372818400939 25976694614502559227601409)
        ·
          refine ⟨19482520960876919420701057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25976694614502559227601409 19482520960876919420701057)
          ·
            refine ⟨14611890720657689565525793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19482520960876919420701057 14611890720657689565525793)
            ·
              refine ⟨10958918040493267174144345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14611890720657689565525793 10958918040493267174144345)
              ·
                refine ⟨8219188530369950380608259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10958918040493267174144345 8219188530369950380608259)
                ·
                  refine ⟨12328782795554925570912389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219188530369950380608259 12328782795554925570912389)
                  ·
                    refine ⟨2311646774166548544546073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12328782795554925570912389 2311646774166548544546073)
                    ·
                      refine ⟨1733735080624911408409555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311646774166548544546073 1733735080624911408409555)
                      ·
                        rfl

theorem cell23_3376437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_3376437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376437 prefixEnd_3376437 := by exact prefixLift 3376437
  have htrace : WordTrace (prefixWord ++ tailWord_3376437) baseStart_3376437 baseEnd_3376437 := by
    simpa [prefixWord, tailWord_3376437, baseEnd_3376437] using wordTrace_append hprefix tailTrace_3376437
  have hstable : (prefixWord ++ tailWord_3376437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376437).length < 2 ^ (prefixWord ++ tailWord_3376437).sum := by decide
  have hdescent : baseEnd_3376437 < baseStart_3376437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376460 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 7]
def baseStart_3376460 : Nat := 118140960795 + 3376460 * 2 ^ 59
def prefixEnd_3376460 : Nat := 4983230072969 + 3 ^ 40 * 3376460 * 2
def baseEnd_3376460 : Nat := 192638543408884979824661

theorem tailTrace_3376460 : CollatzResearch.WordTrace tailWord_3376460 prefixEnd_3376460 192638543408884979824661 := by
  unfold tailWord_3376460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61574806673834774151691417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82099742231779698868921889 61574806673834774151691417)
  ·
    refine ⟨46181105005376080613768563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61574806673834774151691417 46181105005376080613768563)
    ·
      refine ⟨69271657508064120920652845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46181105005376080613768563 69271657508064120920652845)
      ·
        refine ⟨25976871565524045345244817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69271657508064120920652845 25976871565524045345244817)
        ·
          refine ⟨19482653674143034008933613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25976871565524045345244817 19482653674143034008933613)
          ·
            refine ⟨7305995127803637753350105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19482653674143034008933613 7305995127803637753350105)
            ·
              refine ⟨5479496345852728315012579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305995127803637753350105 5479496345852728315012579)
              ·
                refine ⟨8219244518779092472518869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479496345852728315012579 8219244518779092472518869)
                ·
                  refine ⟨192638543408884979824661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8219244518779092472518869 192638543408884979824661)
                  ·
                    rfl

theorem cell23_3376460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_3376460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376460 prefixEnd_3376460 := by exact prefixLift 3376460
  have htrace : WordTrace (prefixWord ++ tailWord_3376460) baseStart_3376460 baseEnd_3376460 := by
    simpa [prefixWord, tailWord_3376460, baseEnd_3376460] using wordTrace_append hprefix tailTrace_3376460
  have hstable : (prefixWord ++ tailWord_3376460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376460).length < 2 ^ (prefixWord ++ tailWord_3376460).sum := by decide
  have hdescent : baseEnd_3376460 < baseStart_3376460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376471 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 2, 2, 2]
def baseStart_3376471 : Nat := 118140960795 + 3376471 * 2 ^ 59
def prefixEnd_3376471 : Nat := 4983230072969 + 3 ^ 40 * 3376471 * 2
def baseEnd_3376471 : Nat := 1733752538967164275384399

theorem tailTrace_3376471 : CollatzResearch.WordTrace tailWord_3376471 prefixEnd_3376471 1733752538967164275384399 := by
  unfold tailWord_3376471
  simp only [CollatzResearch.WordTrace]
  refine ⟨123150014550629697182033267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82100009700419798121355511 123150014550629697182033267)
  ·
    refine ⟨184725021825944545773049901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123150014550629697182033267 184725021825944545773049901)
    ·
      refine ⟨69271883184729204664893713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184725021825944545773049901 69271883184729204664893713)
      ·
        refine ⟨51953912388546903498670285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69271883184729204664893713 51953912388546903498670285)
        ·
          refine ⟨19482717145705088812001357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51953912388546903498670285 19482717145705088812001357)
          ·
            refine ⟨7306018929639408304500509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19482717145705088812001357 7306018929639408304500509)
            ·
              refine ⟨2739757098614778114187691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7306018929639408304500509 2739757098614778114187691)
              ·
                refine ⟨4109635647922167171281537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739757098614778114187691 4109635647922167171281537)
                ·
                  refine ⟨3082226735941625378461153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109635647922167171281537 3082226735941625378461153)
                  ·
                    refine ⟨2311670051956219033845865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3082226735941625378461153 2311670051956219033845865)
                    ·
                      refine ⟨1733752538967164275384399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311670051956219033845865 1733752538967164275384399)
                      ·
                        rfl

theorem cell23_3376471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_3376471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376471 prefixEnd_3376471 := by exact prefixLift 3376471
  have htrace : WordTrace (prefixWord ++ tailWord_3376471) baseStart_3376471 baseEnd_3376471 := by
    simpa [prefixWord, tailWord_3376471, baseEnd_3376471] using wordTrace_append hprefix tailTrace_3376471
  have hstable : (prefixWord ++ tailWord_3376471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376471).length < 2 ^ (prefixWord ++ tailWord_3376471).sum := by decide
  have hdescent : baseEnd_3376471 < baseStart_3376471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376473 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 1, 7]
def baseStart_3376473 : Nat := 118140960795 + 3376473 * 2 ^ 59
def prefixEnd_3376473 : Nat := 4983230072969 + 3 ^ 40 * 3376473 * 2
def baseEnd_3376473 : Nat := 577917855309491089186463

theorem tailTrace_3376473 : CollatzResearch.WordTrace tailWord_3376473 prefixEnd_3376473 577917855309491089186463 := by
  unfold tailWord_3376473
  simp only [CollatzResearch.WordTrace]
  refine ⟨123150087496622451523606073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82100058331081634349070715 123150087496622451523606073)
  ·
    refine ⟨92362565622466838642704555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123150087496622451523606073 92362565622466838642704555)
    ·
      refine ⟨138543848433700257964056833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92362565622466838642704555 138543848433700257964056833)
      ·
        refine ⟨103907886325275193473042625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138543848433700257964056833 103907886325275193473042625)
        ·
          refine ⟨77930914743956395104781969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103907886325275193473042625 77930914743956395104781969)
          ·
            refine ⟨58448186057967296328586477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77930914743956395104781969 58448186057967296328586477)
            ·
              refine ⟨21918069771737736123219929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58448186057967296328586477 21918069771737736123219929)
              ·
                refine ⟨16438552328803302092414947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21918069771737736123219929 16438552328803302092414947)
                ·
                  refine ⟨24657828493204953138622421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16438552328803302092414947 24657828493204953138622421)
                  ·
                    refine ⟨577917855309491089186463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24657828493204953138622421 577917855309491089186463)
                    ·
                      rfl

theorem cell23_3376473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 7].length) (baseStart_3376473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376473 prefixEnd_3376473 := by exact prefixLift 3376473
  have htrace : WordTrace (prefixWord ++ tailWord_3376473) baseStart_3376473 baseEnd_3376473 := by
    simpa [prefixWord, tailWord_3376473, baseEnd_3376473] using wordTrace_append hprefix tailTrace_3376473
  have hstable : (prefixWord ++ tailWord_3376473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376473).length < 2 ^ (prefixWord ++ tailWord_3376473).sum := by decide
  have hdescent : baseEnd_3376473 < baseStart_3376473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376547 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 3]
def baseStart_3376547 : Nat := 118140960795 + 3376547 * 2 ^ 59
def prefixEnd_3376547 : Nat := 4983230072969 + 3 ^ 40 * 3376547 * 2
def baseEnd_3376547 : Nat := 1733791563496905978034049

theorem tailTrace_3376547 : CollatzResearch.WordTrace tailWord_3376547 prefixEnd_3376547 1733791563496905978034049 := by
  unfold tailWord_3376547
  simp only [CollatzResearch.WordTrace]
  refine ⟨123152786498354362161799895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82101857665569574774533263 123152786498354362161799895)
  ·
    refine ⟨184729179747531543242699843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123152786498354362161799895 184729179747531543242699843)
    ·
      refine ⟨277093769621297314864049765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184729179747531543242699843 277093769621297314864049765)
      ·
        refine ⟨51955081803993246537009331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277093769621297314864049765 51955081803993246537009331)
        ·
          refine ⟨77932622705989869805513997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51955081803993246537009331 77932622705989869805513997)
          ·
            refine ⟨29224733514746201177067749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77932622705989869805513997 29224733514746201177067749)
            ·
              refine ⟨5479637534014912720700203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29224733514746201177067749 5479637534014912720700203)
              ·
                refine ⟨8219456301022369081050305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479637534014912720700203 8219456301022369081050305)
                ·
                  refine ⟨6164592225766776810787729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8219456301022369081050305 6164592225766776810787729)
                  ·
                    refine ⟨4623444169325082608090797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164592225766776810787729 4623444169325082608090797)
                    ·
                      refine ⟨1733791563496905978034049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4623444169325082608090797 1733791563496905978034049)
                      ·
                        rfl

theorem cell23_3376547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_3376547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376547 prefixEnd_3376547 := by exact prefixLift 3376547
  have htrace : WordTrace (prefixWord ++ tailWord_3376547) baseStart_3376547 baseEnd_3376547 := by
    simpa [prefixWord, tailWord_3376547, baseEnd_3376547] using wordTrace_append hprefix tailTrace_3376547
  have hstable : (prefixWord ++ tailWord_3376547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376547).length < 2 ^ (prefixWord ++ tailWord_3376547).sum := by decide
  have hdescent : baseEnd_3376547 < baseStart_3376547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376553 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 8]
def baseStart_3376553 : Nat := 118140960795 + 3376553 * 2 ^ 59
def prefixEnd_3376553 : Nat := 4983230072969 + 3 ^ 40 * 3376553 * 2
def baseEnd_3376553 : Nat := 1733794644380832954559021

theorem tailTrace_3376553 : CollatzResearch.WordTrace tailWord_3376553 prefixEnd_3376553 1733794644380832954559021 := by
  unfold tailWord_3376553
  simp only [CollatzResearch.WordTrace]
  refine ⟨123153005336332625186518313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82102003557555083457678875 123153005336332625186518313)
  ·
    refine ⟨92364754002249468889888735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123153005336332625186518313 92364754002249468889888735)
    ·
      refine ⟨138547131003374203334833103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92364754002249468889888735 138547131003374203334833103)
      ·
        refine ⟨207820696505061305002249655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138547131003374203334833103 207820696505061305002249655)
        ·
          refine ⟨311731044757591957503374483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207820696505061305002249655 311731044757591957503374483)
          ·
            refine ⟨467596567136387936255061725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311731044757591957503374483 467596567136387936255061725)
            ·
              refine ⟨175348712676145476095648147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 467596567136387936255061725 175348712676145476095648147)
              ·
                refine ⟨263023069014218214143472221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175348712676145476095648147 263023069014218214143472221)
                ·
                  refine ⟨98633650880331830303802083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263023069014218214143472221 98633650880331830303802083)
                  ·
                    refine ⟨147950476320497745455703125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98633650880331830303802083 147950476320497745455703125)
                    ·
                      refine ⟨1733794644380832954559021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 147950476320497745455703125 1733794644380832954559021)
                      ·
                        rfl

theorem cell23_3376553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_3376553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376553 prefixEnd_3376553 := by exact prefixLift 3376553
  have htrace : WordTrace (prefixWord ++ tailWord_3376553) baseStart_3376553 baseEnd_3376553 := by
    simpa [prefixWord, tailWord_3376553, baseEnd_3376553] using wordTrace_append hprefix tailTrace_3376553
  have hstable : (prefixWord ++ tailWord_3376553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376553).length < 2 ^ (prefixWord ++ tailWord_3376553).sum := by decide
  have hdescent : baseEnd_3376553 < baseStart_3376553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376587 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 4, 3, 2]
def baseStart_3376587 : Nat := 118140960795 + 3376587 * 2 ^ 59
def prefixEnd_3376587 : Nat := 4983230072969 + 3 ^ 40 * 3376587 * 2
def baseEnd_3376587 : Nat := 1733812102723085821533865

theorem tailTrace_3376587 : CollatzResearch.WordTrace tailWord_3376587 prefixEnd_3376587 1733812102723085821533865 := by
  unfold tailWord_3376587
  simp only [CollatzResearch.WordTrace]
  refine ⟨123154245418209448993256015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82102830278806299328837343 123154245418209448993256015)
  ·
    refine ⟨184731368127314173489884023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123154245418209448993256015 184731368127314173489884023)
    ·
      refine ⟨277097052190971260234826035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184731368127314173489884023 277097052190971260234826035)
      ·
        refine ⟨415645578286456890352239053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277097052190971260234826035 415645578286456890352239053)
        ·
          refine ⟨155867091857421333882089645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415645578286456890352239053 155867091857421333882089645)
          ·
            refine ⟨58450159446533000205783617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155867091857421333882089645 58450159446533000205783617)
            ·
              refine ⟨43837619584899750154337713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58450159446533000205783617 43837619584899750154337713)
              ·
                refine ⟨32878214688674812615753285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43837619584899750154337713 32878214688674812615753285)
                ·
                  refine ⟨6164665254126527365453741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32878214688674812615753285 6164665254126527365453741)
                  ·
                    refine ⟨2311749470297447762045153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6164665254126527365453741 2311749470297447762045153)
                    ·
                      refine ⟨1733812102723085821533865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311749470297447762045153 1733812102723085821533865)
                      ·
                        rfl

theorem cell23_3376587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 3, 2].length) (baseStart_3376587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376587 prefixEnd_3376587 := by exact prefixLift 3376587
  have htrace : WordTrace (prefixWord ++ tailWord_3376587) baseStart_3376587 baseEnd_3376587 := by
    simpa [prefixWord, tailWord_3376587, baseEnd_3376587] using wordTrace_append hprefix tailTrace_3376587
  have hstable : (prefixWord ++ tailWord_3376587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376587).length < 2 ^ (prefixWord ++ tailWord_3376587).sum := by decide
  have hdescent : baseEnd_3376587 < baseStart_3376587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376597 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3376597 : Nat := 118140960795 + 3376597 * 2 ^ 59
def prefixEnd_3376597 : Nat := 4983230072969 + 3 ^ 40 * 3376597 * 2
def baseEnd_3376597 : Nat := 577939079176543594136273

theorem tailTrace_3376597 : CollatzResearch.WordTrace tailWord_3376597 prefixEnd_3376597 577939079176543594136273 := by
  unfold tailWord_3376597
  simp only [CollatzResearch.WordTrace]
  refine ⟨123154610148173220701120045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82103073432115480467413363 123154610148173220701120045)
  ·
    refine ⟨46182978805564957762920017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123154610148173220701120045 46182978805564957762920017)
    ·
      refine ⟨34637234104173718322190013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46182978805564957762920017 34637234104173718322190013)
      ·
        refine ⟨12988962789065144370821255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34637234104173718322190013 12988962789065144370821255)
        ·
          refine ⟨19483444183597716556231883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12988962789065144370821255 19483444183597716556231883)
          ·
            refine ⟨29225166275396574834347825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19483444183597716556231883 29225166275396574834347825)
            ·
              refine ⟨21918874706547431125760869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29225166275396574834347825 21918874706547431125760869)
              ·
                refine ⟨4109789007477643336080163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21918874706547431125760869 4109789007477643336080163)
                ·
                  refine ⟨6164683511216465004120245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109789007477643336080163 6164683511216465004120245)
                  ·
                    refine ⟨577939079176543594136273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6164683511216465004120245 577939079176543594136273)
                    ·
                      rfl

theorem cell23_3376597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3376597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376597 prefixEnd_3376597 := by exact prefixLift 3376597
  have htrace : WordTrace (prefixWord ++ tailWord_3376597) baseStart_3376597 baseEnd_3376597 := by
    simpa [prefixWord, tailWord_3376597, baseEnd_3376597] using wordTrace_append hprefix tailTrace_3376597
  have hstable : (prefixWord ++ tailWord_3376597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376597).length < 2 ^ (prefixWord ++ tailWord_3376597).sum := by decide
  have hdescent : baseEnd_3376597 < baseStart_3376597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376611 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 1, 1, 3]
def baseStart_3376611 : Nat := 118140960795 + 3376611 * 2 ^ 59
def prefixEnd_3376611 : Nat := 4983230072969 + 3 ^ 40 * 3376611 * 2
def baseEnd_3376611 : Nat := 1733824426258793727633755

theorem tailTrace_3376611 : CollatzResearch.WordTrace tailWord_3376611 prefixEnd_3376611 1733824426258793727633755 := by
  unfold tailWord_3376611
  simp only [CollatzResearch.WordTrace]
  refine ⟨123155120770122501092129687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82103413846748334061419791 123155120770122501092129687)
  ·
    refine ⟨184732681155183751638194531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123155120770122501092129687 184732681155183751638194531)
    ·
      refine ⟨277099021732775627457291797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184732681155183751638194531 277099021732775627457291797)
      ·
        refine ⟨12989016643723857537060553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 277099021732775627457291797 12989016643723857537060553)
        ·
          refine ⟨9741762482792893152795415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12989016643723857537060553 9741762482792893152795415)
          ·
            refine ⟨14612643724189339729193123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9741762482792893152795415 14612643724189339729193123)
            ·
              refine ⟨21918965586284009593789685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14612643724189339729193123 21918965586284009593789685)
              ·
                refine ⟨2054903023714125899417783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21918965586284009593789685 2054903023714125899417783)
                ·
                  refine ⟨3082354535571188849126675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054903023714125899417783 3082354535571188849126675)
                  ·
                    refine ⟨4623531803356783273690013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3082354535571188849126675 4623531803356783273690013)
                    ·
                      refine ⟨1733824426258793727633755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4623531803356783273690013 1733824426258793727633755)
                      ·
                        rfl

theorem cell23_3376611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_3376611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376611 prefixEnd_3376611 := by exact prefixLift 3376611
  have htrace : WordTrace (prefixWord ++ tailWord_3376611) baseStart_3376611 baseEnd_3376611 := by
    simpa [prefixWord, tailWord_3376611, baseEnd_3376611] using wordTrace_append hprefix tailTrace_3376611
  have hstable : (prefixWord ++ tailWord_3376611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376611).length < 2 ^ (prefixWord ++ tailWord_3376611).sum := by decide
  have hdescent : baseEnd_3376611 < baseStart_3376611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376627 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 2, 4]
def baseStart_3376627 : Nat := 118140960795 + 3376627 * 2 ^ 59
def prefixEnd_3376627 : Nat := 4983230072969 + 3 ^ 40 * 3376627 * 2
def baseEnd_3376627 : Nat := 577944213983088555011227

theorem tailTrace_3376627 : CollatzResearch.WordTrace tailWord_3376627 prefixEnd_3376627 577944213983088555011227 := by
  unfold tailWord_3376627
  simp only [CollatzResearch.WordTrace]
  refine ⟨123155704338064535824712135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82103802892043023883141423 123155704338064535824712135)
  ·
    refine ⟨184733556507096803737068203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123155704338064535824712135 184733556507096803737068203)
    ·
      refine ⟨277100334760645205605602305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184733556507096803737068203 277100334760645205605602305)
      ·
        refine ⟨207825251070483904204201729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277100334760645205605602305 207825251070483904204201729)
        ·
          refine ⟨155868938302862928153151297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207825251070483904204201729 155868938302862928153151297)
          ·
            refine ⟨116901703727147196114863473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155868938302862928153151297 116901703727147196114863473)
            ·
              refine ⟨87676277795360397086147605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116901703727147196114863473 87676277795360397086147605)
              ·
                refine ⟨4109825521657518613413169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87676277795360397086147605 4109825521657518613413169)
                ·
                  refine ⟨3082369141243138960059877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109825521657518613413169 3082369141243138960059877)
                  ·
                    refine ⟨577944213983088555011227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082369141243138960059877 577944213983088555011227)
                    ·
                      rfl

theorem cell23_3376627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 2, 4].length) (baseStart_3376627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376627 prefixEnd_3376627 := by exact prefixLift 3376627
  have htrace : WordTrace (prefixWord ++ tailWord_3376627) baseStart_3376627 baseEnd_3376627 := by
    simpa [prefixWord, tailWord_3376627, baseEnd_3376627] using wordTrace_append hprefix tailTrace_3376627
  have hstable : (prefixWord ++ tailWord_3376627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376627).length < 2 ^ (prefixWord ++ tailWord_3376627).sum := by decide
  have hdescent : baseEnd_3376627 < baseStart_3376627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376637 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_3376637 : Nat := 118140960795 + 3376637 * 2 ^ 59
def prefixEnd_3376637 : Nat := 4983230072969 + 3 ^ 40 * 3376637 * 2
def baseEnd_3376637 : Nat := 1733837776755810625908635

theorem tailTrace_3376637 : CollatzResearch.WordTrace tailWord_3376637 prefixEnd_3376637 1733837776755810625908635 := by
  unfold tailWord_3376637
  simp only [CollatzResearch.WordTrace]
  refine ⟨123156069068028307532576165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82104046045352205021717443 123156069068028307532576165)
  ·
    refine ⟨23091762950255307662358031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123156069068028307532576165 23091762950255307662358031)
    ·
      refine ⟨34637644425382961493537047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23091762950255307662358031 34637644425382961493537047)
      ·
        refine ⟨51956466638074442240305571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34637644425382961493537047 51956466638074442240305571)
        ·
          refine ⟨77934699957111663360458357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51956466638074442240305571 77934699957111663360458357)
          ·
            refine ⟨7306378120979218440042971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77934699957111663360458357 7306378120979218440042971)
            ·
              refine ⟨10959567181468827660064457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306378120979218440042971 10959567181468827660064457)
              ·
                refine ⟨8219675386101620745048343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10959567181468827660064457 8219675386101620745048343)
                ·
                  refine ⟨12329513079152431117572515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219675386101620745048343 12329513079152431117572515)
                  ·
                    refine ⟨18494269618728646676358773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12329513079152431117572515 18494269618728646676358773)
                    ·
                      refine ⟨1733837776755810625908635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18494269618728646676358773 1733837776755810625908635)
                      ·
                        rfl

theorem cell23_3376637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_3376637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376637 prefixEnd_3376637 := by exact prefixLift 3376637
  have htrace : WordTrace (prefixWord ++ tailWord_3376637) baseStart_3376637 baseEnd_3376637 := by
    simpa [prefixWord, tailWord_3376637, baseEnd_3376637] using wordTrace_append hprefix tailTrace_3376637
  have hstable : (prefixWord ++ tailWord_3376637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376637).length < 2 ^ (prefixWord ++ tailWord_3376637).sum := by decide
  have hdescent : baseEnd_3376637 < baseStart_3376637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376647 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_3376647 : Nat := 118140960795 + 3376647 * 2 ^ 59
def prefixEnd_3376647 : Nat := 4983230072969 + 3 ^ 40 * 3376647 * 2
def baseEnd_3376647 : Nat := 1733842911562355586783589

theorem tailTrace_3376647 : CollatzResearch.WordTrace tailWord_3376647 prefixEnd_3376647 1733842911562355586783589 := by
  unfold tailWord_3376647
  simp only [CollatzResearch.WordTrace]
  refine ⟨123156433797992079240440195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82104289198661386160293463 123156433797992079240440195)
  ·
    refine ⟨184734650696988118860660293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123156433797992079240440195 184734650696988118860660293)
    ·
      refine ⟨34637747005685272286373805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184734650696988118860660293 34637747005685272286373805)
      ·
        refine ⟨12989155127131977107390177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34637747005685272286373805 12989155127131977107390177)
        ·
          refine ⟨9741866345348982830542633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12989155127131977107390177 9741866345348982830542633)
          ·
            refine ⟨7306399759011737122906975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9741866345348982830542633 7306399759011737122906975)
            ·
              refine ⟨10959599638517605684360463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306399759011737122906975 10959599638517605684360463)
              ·
                refine ⟨16439399457776408526540695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10959599638517605684360463 16439399457776408526540695)
                ·
                  refine ⟨24659099186664612789811043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16439399457776408526540695 24659099186664612789811043)
                  ·
                    refine ⟨36988648779996919184716565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24659099186664612789811043 36988648779996919184716565)
                    ·
                      refine ⟨1733842911562355586783589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36988648779996919184716565 1733842911562355586783589)
                      ·
                        rfl

theorem cell23_3376647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_3376647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376647 prefixEnd_3376647 := by exact prefixLift 3376647
  have htrace : WordTrace (prefixWord ++ tailWord_3376647) baseStart_3376647 baseEnd_3376647 := by
    simpa [prefixWord, tailWord_3376647, baseEnd_3376647] using wordTrace_append hprefix tailTrace_3376647
  have hstable : (prefixWord ++ tailWord_3376647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376647).length < 2 ^ (prefixWord ++ tailWord_3376647).sum := by decide
  have hdescent : baseEnd_3376647 < baseStart_3376647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376711 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_3376711 : Nat := 118140960795 + 3376711 * 2 ^ 59
def prefixEnd_3376711 : Nat := 4983230072969 + 3 ^ 40 * 3376711 * 2
def baseEnd_3376711 : Nat := 1733875774324243336383295

theorem tailTrace_3376711 : CollatzResearch.WordTrace tailWord_3376711 prefixEnd_3376711 1733875774324243336383295 := by
  unfold tailWord_3376711
  simp only [CollatzResearch.WordTrace]
  refine ⟨123158768069760218170769987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82105845379840145447179991 123158768069760218170769987)
  ·
    refine ⟨184738152104640327256154981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123158768069760218170769987 184738152104640327256154981)
    ·
      refine ⟨34638403519620061360529059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184738152104640327256154981 34638403519620061360529059)
      ·
        refine ⟨51957605279430092040793589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34638403519620061360529059 51957605279430092040793589)
        ·
          refine ⟨4871025494946571128824399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51957605279430092040793589 4871025494946571128824399)
          ·
            refine ⟨7306538242419856693236599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4871025494946571128824399 7306538242419856693236599)
            ·
              refine ⟨10959807363629785039854899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306538242419856693236599 10959807363629785039854899)
              ·
                refine ⟨16439711045444677559782349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10959807363629785039854899 16439711045444677559782349)
                ·
                  refine ⟨6164891642041754084918381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16439711045444677559782349 6164891642041754084918381)
                  ·
                    refine ⟨2311834365765657781844393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6164891642041754084918381 2311834365765657781844393)
                    ·
                      refine ⟨1733875774324243336383295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311834365765657781844393 1733875774324243336383295)
                      ·
                        rfl

theorem cell23_3376711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_3376711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376711 prefixEnd_3376711 := by exact prefixLift 3376711
  have htrace : WordTrace (prefixWord ++ tailWord_3376711) baseStart_3376711 baseEnd_3376711 := by
    simpa [prefixWord, tailWord_3376711, baseEnd_3376711] using wordTrace_append hprefix tailTrace_3376711
  have hstable : (prefixWord ++ tailWord_3376711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376711).length < 2 ^ (prefixWord ++ tailWord_3376711).sum := by decide
  have hdescent : baseEnd_3376711 < baseStart_3376711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376727 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_3376727 : Nat := 118140960795 + 3376727 * 2 ^ 59
def prefixEnd_3376727 : Nat := 4983230072969 + 3 ^ 40 * 3376727 * 2
def baseEnd_3376727 : Nat := 1733883990014715273783221

theorem tailTrace_3376727 : CollatzResearch.WordTrace tailWord_3376727 prefixEnd_3376727 1733883990014715273783221 := by
  unfold tailWord_3376727
  simp only [CollatzResearch.WordTrace]
  refine ⟨123159351637702252903352435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82106234425134835268901623 123159351637702252903352435)
  ·
    refine ⟨184739027456553379355028653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123159351637702252903352435 184739027456553379355028653)
    ·
      refine ⟨69277135296207517258135745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184739027456553379355028653 69277135296207517258135745)
      ·
        refine ⟨51957851472155637943601809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69277135296207517258135745 51957851472155637943601809)
        ·
          refine ⟨38968388604116728457701357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51957851472155637943601809 38968388604116728457701357)
          ·
            refine ⟨14613145726543773171638009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38968388604116728457701357 14613145726543773171638009)
            ·
              refine ⟨10959859294907829878728507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14613145726543773171638009 10959859294907829878728507)
              ·
                refine ⟨16439788942361744818092761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10959859294907829878728507 16439788942361744818092761)
                ·
                  refine ⟨12329841706771308613569571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16439788942361744818092761 12329841706771308613569571)
                  ·
                    refine ⟨18494762560156962920354357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12329841706771308613569571 18494762560156962920354357)
                    ·
                      refine ⟨1733883990014715273783221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18494762560156962920354357 1733883990014715273783221)
                      ·
                        rfl

theorem cell23_3376727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_3376727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376727 prefixEnd_3376727 := by exact prefixLift 3376727
  have htrace : WordTrace (prefixWord ++ tailWord_3376727) baseStart_3376727 baseEnd_3376727 := by
    simpa [prefixWord, tailWord_3376727, baseEnd_3376727] using wordTrace_append hprefix tailTrace_3376727
  have hstable : (prefixWord ++ tailWord_3376727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376727).length < 2 ^ (prefixWord ++ tailWord_3376727).sum := by decide
  have hdescent : baseEnd_3376727 < baseStart_3376727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376737 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_3376737 : Nat := 118140960795 + 3376737 * 2 ^ 59
def prefixEnd_3376737 : Nat := 4983230072969 + 3 ^ 40 * 3376737 * 2
def baseEnd_3376737 : Nat := 1733889124821260234658175

theorem tailTrace_3376737 : CollatzResearch.WordTrace tailWord_3376737 prefixEnd_3376737 1733889124821260234658175 := by
  unfold tailWord_3376737
  simp only [CollatzResearch.WordTrace]
  refine ⟨123159716367666024611216465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82106477578444016407477643 123159716367666024611216465)
  ·
    refine ⟨92369787275749518458412349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123159716367666024611216465 92369787275749518458412349)
    ·
      refine ⟨34638670228406069421904631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92369787275749518458412349 34638670228406069421904631)
      ·
        refine ⟨51958005342609104132856947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34638670228406069421904631 51958005342609104132856947)
        ·
          refine ⟨77937008013913656199285421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51958005342609104132856947 77937008013913656199285421)
          ·
            refine ⟨29226378005217621074732033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77937008013913656199285421 29226378005217621074732033)
            ·
              refine ⟨21919783503913215806049025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29226378005217621074732033 21919783503913215806049025)
              ·
                refine ⟨16439837627934911854536769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21919783503913215806049025 16439837627934911854536769)
                ·
                  refine ⟨12329878220951183890902577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16439837627934911854536769 12329878220951183890902577)
                  ·
                    refine ⟨9247408665713387918176933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12329878220951183890902577 9247408665713387918176933)
                    ·
                      refine ⟨1733889124821260234658175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9247408665713387918176933 1733889124821260234658175)
                      ·
                        rfl

theorem cell23_3376737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_3376737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376737 prefixEnd_3376737 := by exact prefixLift 3376737
  have htrace : WordTrace (prefixWord ++ tailWord_3376737) baseStart_3376737 baseEnd_3376737 := by
    simpa [prefixWord, tailWord_3376737, baseEnd_3376737] using wordTrace_append hprefix tailTrace_3376737
  have hstable : (prefixWord ++ tailWord_3376737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376737).length < 2 ^ (prefixWord ++ tailWord_3376737).sum := by decide
  have hdescent : baseEnd_3376737 < baseStart_3376737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376744 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3376744 : Nat := 118140960795 + 3376744 * 2 ^ 59
def prefixEnd_3376744 : Nat := 4983230072969 + 3 ^ 40 * 3376744 * 2
def baseEnd_3376744 : Nat := 1733892719185841707270643

theorem tailTrace_3376744 : CollatzResearch.WordTrace tailWord_3376744 prefixEnd_3376744 1733892719185841707270643 := by
  unfold tailWord_3376744
  simp only [CollatzResearch.WordTrace]
  refine ⟨61579985839320332403360643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82106647785760443204480857 61579985839320332403360643)
  ·
    refine ⟨92369978758980498605040965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61579985839320332403360643 92369978758980498605040965)
    ·
      refine ⟨17319371017308843488445181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92369978758980498605040965 17319371017308843488445181)
      ·
        refine ⟨6494764131490816308166943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17319371017308843488445181 6494764131490816308166943)
        ·
          refine ⟨9742146197236224462250415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494764131490816308166943 9742146197236224462250415)
          ·
            refine ⟨14613219295854336693375623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9742146197236224462250415 14613219295854336693375623)
            ·
              refine ⟨21919828943781505040063435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14613219295854336693375623 21919828943781505040063435)
              ·
                refine ⟨32879743415672257560095153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21919828943781505040063435 32879743415672257560095153)
                ·
                  refine ⟨24659807561754193170071365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32879743415672257560095153 24659807561754193170071365)
                  ·
                    refine ⟨4623713917828911219388381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24659807561754193170071365 4623713917828911219388381)
                    ·
                      refine ⟨1733892719185841707270643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4623713917828911219388381 1733892719185841707270643)
                      ·
                        rfl

theorem cell23_3376744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3376744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376744 prefixEnd_3376744 := by exact prefixLift 3376744
  have htrace : WordTrace (prefixWord ++ tailWord_3376744) baseStart_3376744 baseEnd_3376744 := by
    simpa [prefixWord, tailWord_3376744, baseEnd_3376744] using wordTrace_append hprefix tailTrace_3376744
  have hstable : (prefixWord ++ tailWord_3376744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376744).length < 2 ^ (prefixWord ++ tailWord_3376744).sum := by decide
  have hdescent : baseEnd_3376744 < baseStart_3376744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376754 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3376754 : Nat := 118140960795 + 3376754 * 2 ^ 59
def prefixEnd_3376754 : Nat := 4983230072969 + 3 ^ 40 * 3376754 * 2
def baseEnd_3376754 : Nat := 1733897853992386668145597

theorem tailTrace_3376754 : CollatzResearch.WordTrace tailWord_3376754 prefixEnd_3376754 1733897853992386668145597 := by
  unfold tailWord_3376754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30790084102151109128646329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82106890939069624343056877 30790084102151109128646329)
  ·
    refine ⟨23092563076613331846484747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30790084102151109128646329 23092563076613331846484747)
    ·
      refine ⟨34638844614919997769727121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23092563076613331846484747 34638844614919997769727121)
      ·
        refine ⟨25979133461189998327295341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34638844614919997769727121 25979133461189998327295341)
        ·
          refine ⟨9742175047946249372735753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25979133461189998327295341 9742175047946249372735753)
          ·
            refine ⟨7306631285959687029551815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9742175047946249372735753 7306631285959687029551815)
            ·
              refine ⟨10959946928939530544327723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7306631285959687029551815 10959946928939530544327723)
              ·
                refine ⟨16439920393409295816491585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10959946928939530544327723 16439920393409295816491585)
                ·
                  refine ⟨12329940295056971862368689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16439920393409295816491585 12329940295056971862368689)
                  ·
                    refine ⟨9247455221292728896776517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12329940295056971862368689 9247455221292728896776517)
                    ·
                      refine ⟨1733897853992386668145597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9247455221292728896776517 1733897853992386668145597)
                      ·
                        rfl

theorem cell23_3376754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3376754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376754 prefixEnd_3376754 := by exact prefixLift 3376754
  have htrace : WordTrace (prefixWord ++ tailWord_3376754) baseStart_3376754 baseEnd_3376754 := by
    simpa [prefixWord, tailWord_3376754, baseEnd_3376754] using wordTrace_append hprefix tailTrace_3376754
  have hstable : (prefixWord ++ tailWord_3376754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376754).length < 2 ^ (prefixWord ++ tailWord_3376754).sum := by decide
  have hdescent : baseEnd_3376754 < baseStart_3376754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376758 : List Nat := [5, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2]
def baseStart_3376758 : Nat := 118140960795 + 3376758 * 2 ^ 59
def prefixEnd_3376758 : Nat := 4983230072969 + 3 ^ 40 * 3376758 * 2
def baseEnd_3376758 : Nat := 1733899907915004652495579

theorem tailTrace_3376758 : CollatzResearch.WordTrace tailWord_3376758 prefixEnd_3376758 1733899907915004652495579 := by
  unfold tailWord_3376758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697530143786871574858183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82106988200393296798487285 7697530143786871574858183)
  ·
    refine ⟨11546295215680307362287275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7697530143786871574858183 11546295215680307362287275)
    ·
      refine ⟨17319442823520461043430913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11546295215680307362287275 17319442823520461043430913)
      ·
        refine ⟨12989582117640345782573185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17319442823520461043430913 12989582117640345782573185)
        ·
          refine ⟨9742186588230259336929889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12989582117640345782573185 9742186588230259336929889)
          ·
            refine ⟨7306639941172694502697417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9742186588230259336929889 7306639941172694502697417)
            ·
              refine ⟨5479979955879520877023063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7306639941172694502697417 5479979955879520877023063)
              ·
                refine ⟨8219969933819281315534595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479979955879520877023063 8219969933819281315534595)
                ·
                  refine ⟨12329954900728921973301893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8219969933819281315534595 12329954900728921973301893)
                  ·
                    refine ⟨2311866543886672869994105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12329954900728921973301893 2311866543886672869994105)
                    ·
                      refine ⟨1733899907915004652495579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311866543886672869994105 1733899907915004652495579)
                      ·
                        rfl

theorem cell23_3376758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_3376758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376758 prefixEnd_3376758 := by exact prefixLift 3376758
  have htrace : WordTrace (prefixWord ++ tailWord_3376758) baseStart_3376758 baseEnd_3376758 := by
    simpa [prefixWord, tailWord_3376758, baseEnd_3376758] using wordTrace_append hprefix tailTrace_3376758
  have hstable : (prefixWord ++ tailWord_3376758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376758).length < 2 ^ (prefixWord ++ tailWord_3376758).sum := by decide
  have hdescent : baseEnd_3376758 < baseStart_3376758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376924 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3376924 : Nat := 118140960795 + 3376924 * 2 ^ 59
def prefixEnd_3376924 : Nat := 4983230072969 + 3 ^ 40 * 3376924 * 2
def baseEnd_3376924 : Nat := 1733985145703651003019815

theorem tailTrace_3376924 : CollatzResearch.WordTrace tailWord_3376924 prefixEnd_3376924 1733985145703651003019815 := by
  unfold tailWord_3376924
  simp only [CollatzResearch.WordTrace]
  refine ⟨61583268408994277774136913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82111024545325703698849217 61583268408994277774136913)
  ·
    refine ⟨46187451306745708330602685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61583268408994277774136913 46187451306745708330602685)
    ·
      refine ⟨17320294240029640623976007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46187451306745708330602685 17320294240029640623976007)
      ·
        refine ⟨25980441360044460935964011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17320294240029640623976007 25980441360044460935964011)
        ·
          refine ⟨38970662040066691403946017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25980441360044460935964011 38970662040066691403946017)
          ·
            refine ⟨29227996530050018552959513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38970662040066691403946017 29227996530050018552959513)
            ·
              refine ⟨21920997397537513914719635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29227996530050018552959513 21920997397537513914719635)
              ·
                refine ⟨32881496096306270872079453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21920997397537513914719635 32881496096306270872079453)
                ·
                  refine ⟨12330561036114851577029795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32881496096306270872079453 12330561036114851577029795)
                  ·
                    refine ⟨18495841554172277365544693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12330561036114851577029795 18495841554172277365544693)
                    ·
                      refine ⟨1733985145703651003019815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18495841554172277365544693 1733985145703651003019815)
                      ·
                        rfl

theorem cell23_3376924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3376924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376924 prefixEnd_3376924 := by exact prefixLift 3376924
  have htrace : WordTrace (prefixWord ++ tailWord_3376924) baseStart_3376924 baseEnd_3376924 := by
    simpa [prefixWord, tailWord_3376924, baseEnd_3376924] using wordTrace_append hprefix tailTrace_3376924
  have hstable : (prefixWord ++ tailWord_3376924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376924).length < 2 ^ (prefixWord ++ tailWord_3376924).sum := by decide
  have hdescent : baseEnd_3376924 < baseStart_3376924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376931 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 2, 4]
def baseStart_3376931 : Nat := 118140960795 + 3376931 * 2 ^ 59
def prefixEnd_3376931 : Nat := 4983230072969 + 3 ^ 40 * 3376931 * 2
def baseEnd_3376931 : Nat := 577996246689410825210761

theorem tailTrace_3376931 : CollatzResearch.WordTrace tailWord_3376931 prefixEnd_3376931 577996246689410825210761 := by
  unfold tailWord_3376931
  simp only [CollatzResearch.WordTrace]
  refine ⟨123166792128963195743778647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82111194752642130495852431 123166792128963195743778647)
  ·
    refine ⟨184750188193444793615667971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123166792128963195743778647 184750188193444793615667971)
    ·
      refine ⟨277125282290167190423501957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184750188193444793615667971 277125282290167190423501957)
      ·
        refine ⟨51960990429406348204406617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277125282290167190423501957 51960990429406348204406617)
        ·
          refine ⟨38970742822054761153304963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51960990429406348204406617 38970742822054761153304963)
          ·
            refine ⟨58456114233082141729957445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38970742822054761153304963 58456114233082141729957445)
            ·
              refine ⟨10960521418702901574367021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58456114233082141729957445 10960521418702901574367021)
              ·
                refine ⟨4110195532013588090387633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10960521418702901574367021 4110195532013588090387633)
                ·
                  refine ⟨3082646649010191067790725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4110195532013588090387633 3082646649010191067790725)
                  ·
                    refine ⟨577996246689410825210761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082646649010191067790725 577996246689410825210761)
                    ·
                      rfl

theorem cell23_3376931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 4].length) (baseStart_3376931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376931 prefixEnd_3376931 := by exact prefixLift 3376931
  have htrace : WordTrace (prefixWord ++ tailWord_3376931) baseStart_3376931 baseEnd_3376931 := by
    simpa [prefixWord, tailWord_3376931, baseEnd_3376931] using wordTrace_append hprefix tailTrace_3376931
  have hstable : (prefixWord ++ tailWord_3376931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376931).length < 2 ^ (prefixWord ++ tailWord_3376931).sum := by decide
  have hdescent : baseEnd_3376931 < baseStart_3376931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3376942 : List Nat := [4, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2]
def baseStart_3376942 : Nat := 118140960795 + 3376942 * 2 ^ 59
def prefixEnd_3376942 : Nat := 4983230072969 + 3 ^ 40 * 3376942 * 2
def baseEnd_3376942 : Nat := 1733994388355431932594733

theorem tailTrace_3376942 : CollatzResearch.WordTrace tailWord_3376942 prefixEnd_3376942 1733994388355431932594733 := by
  unfold tailWord_3376942
  simp only [CollatzResearch.WordTrace]
  refine ⟨15395899166490418077803635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82111462221282229748286053 15395899166490418077803635)
  ·
    refine ⟨23093848749735627116705453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15395899166490418077803635 23093848749735627116705453)
    ·
      refine ⟨8660193281150860168764545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23093848749735627116705453 8660193281150860168764545)
      ·
        refine ⟨6495144960863145126573409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8660193281150860168764545 6495144960863145126573409)
        ·
          refine ⟨4871358720647358844930057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6495144960863145126573409 4871358720647358844930057)
          ·
            refine ⟨3653519040485519133697543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4871358720647358844930057 3653519040485519133697543)
            ·
              refine ⟨5480278560728278700546315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653519040485519133697543 5480278560728278700546315)
              ·
                refine ⟨8220417841092418050819473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480278560728278700546315 8220417841092418050819473)
                ·
                  refine ⟨6165313380819313538114605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8220417841092418050819473 6165313380819313538114605)
                  ·
                    refine ⟨2311992517807242576792977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6165313380819313538114605 2311992517807242576792977)
                    ·
                      refine ⟨1733994388355431932594733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2311992517807242576792977 1733994388355431932594733)
                      ·
                        rfl

theorem cell23_3376942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2].length) (baseStart_3376942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3376942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3376942 prefixEnd_3376942 := by exact prefixLift 3376942
  have htrace : WordTrace (prefixWord ++ tailWord_3376942) baseStart_3376942 baseEnd_3376942 := by
    simpa [prefixWord, tailWord_3376942, baseEnd_3376942] using wordTrace_append hprefix tailTrace_3376942
  have hstable : (prefixWord ++ tailWord_3376942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3376942).length < 2 ^ (prefixWord ++ tailWord_3376942).sum := by decide
  have hdescent : baseEnd_3376942 < baseStart_3376942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3376942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377011 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 3, 4, 2]
def baseStart_3377011 : Nat := 118140960795 + 3377011 * 2 ^ 59
def prefixEnd_3377011 : Nat := 4983230072969 + 3 ^ 40 * 3377011 * 2
def baseEnd_3377011 : Nat := 1734029818520592162631915

theorem tailTrace_3377011 : CollatzResearch.WordTrace tailWord_3377011 prefixEnd_3377011 1734029818520592162631915 := by
  unfold tailWord_3377011
  simp only [CollatzResearch.WordTrace]
  refine ⟨123169709968673369406690887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82113139979115579604460591 123169709968673369406690887)
  ·
    refine ⟨184754564953010054110036331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123169709968673369406690887 184754564953010054110036331)
    ·
      refine ⟨277131847429515081165054497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184754564953010054110036331 277131847429515081165054497)
      ·
        refine ⟨207848885572136310873790873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277131847429515081165054497 207848885572136310873790873)
        ·
          refine ⟨155886664179102233155343155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207848885572136310873790873 155886664179102233155343155)
          ·
            refine ⟨233829996268653349733014733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155886664179102233155343155 233829996268653349733014733)
            ·
              refine ⟨87686248600745006149880525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233829996268653349733014733 87686248600745006149880525)
              ·
                refine ⟨32882343225279377306205197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87686248600745006149880525 32882343225279377306205197)
                ·
                  refine ⟨12330878709479766489826949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32882343225279377306205197 12330878709479766489826949)
                  ·
                    refine ⟨2312039758027456216842553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12330878709479766489826949 2312039758027456216842553)
                    ·
                      refine ⟨1734029818520592162631915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312039758027456216842553 1734029818520592162631915)
                      ·
                        rfl

theorem cell23_3377011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 4, 2].length) (baseStart_3377011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377011 prefixEnd_3377011 := by exact prefixLift 3377011
  have htrace : WordTrace (prefixWord ++ tailWord_3377011) baseStart_3377011 baseEnd_3377011 := by
    simpa [prefixWord, tailWord_3377011, baseEnd_3377011] using wordTrace_append hprefix tailTrace_3377011
  have hstable : (prefixWord ++ tailWord_3377011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377011).length < 2 ^ (prefixWord ++ tailWord_3377011).sum := by decide
  have hdescent : baseEnd_3377011 < baseStart_3377011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377045 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_3377045 : Nat := 118140960795 + 3377045 * 2 ^ 59
def prefixEnd_3377045 : Nat := 4983230072969 + 3 ^ 40 * 3377045 * 2
def baseEnd_3377045 : Nat := 1734047276862845029606759

theorem tailTrace_3377045 : CollatzResearch.WordTrace tailWord_3377045 prefixEnd_3377045 1734047276862845029606759 := by
  unfold tailWord_3377045
  simp only [CollatzResearch.WordTrace]
  refine ⟨123170950050550193213428589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82113966700366795475619059 123170950050550193213428589)
  ·
    refine ⟨46189106268956322455035721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123170950050550193213428589 46189106268956322455035721)
    ·
      refine ⟨34641829701717241841276791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46189106268956322455035721 34641829701717241841276791)
      ·
        refine ⟨51962744552575862761915187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34641829701717241841276791 51962744552575862761915187)
        ·
          refine ⟨77944116828863794142872781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51962744552575862761915187 77944116828863794142872781)
          ·
            refine ⟨29229043810823922803577293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77944116828863794142872781 29229043810823922803577293)
            ·
              refine ⟨10960891429058971051341485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29229043810823922803577293 10960891429058971051341485)
              ·
                refine ⟨4110334285897114144253057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10960891429058971051341485 4110334285897114144253057)
                ·
                  refine ⟨3082750714422835608189793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4110334285897114144253057 3082750714422835608189793)
                  ·
                    refine ⟨2312063035817126706142345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3082750714422835608189793 2312063035817126706142345)
                    ·
                      refine ⟨1734047276862845029606759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312063035817126706142345 1734047276862845029606759)
                      ·
                        rfl

theorem cell23_3377045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_3377045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377045 prefixEnd_3377045 := by exact prefixLift 3377045
  have htrace : WordTrace (prefixWord ++ tailWord_3377045) baseStart_3377045 baseEnd_3377045 := by
    simpa [prefixWord, tailWord_3377045, baseEnd_3377045] using wordTrace_append hprefix tailTrace_3377045
  have hstable : (prefixWord ++ tailWord_3377045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377045).length < 2 ^ (prefixWord ++ tailWord_3377045).sum := by decide
  have hdescent : baseEnd_3377045 < baseStart_3377045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377081 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 2, 5]
def baseStart_3377081 : Nat := 118140960795 + 3377081 * 2 ^ 59
def prefixEnd_3377081 : Nat := 4983230072969 + 3 ^ 40 * 3377081 * 2
def baseEnd_3377081 : Nat := 578021920722135629585531

theorem tailTrace_3377081 : CollatzResearch.WordTrace tailWord_3377081 prefixEnd_3377081 578021920722135629585531 := by
  unfold tailWord_3377081
  simp only [CollatzResearch.WordTrace]
  refine ⟨123172263078419771361739097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82114842052279847574492731 123172263078419771361739097)
  ·
    refine ⟨92379197308814828521304323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123172263078419771361739097 92379197308814828521304323)
    ·
      refine ⟨138568795963222242781956485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92379197308814828521304323 138568795963222242781956485)
      ·
        refine ⟨25981649243104170521616841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138568795963222242781956485 25981649243104170521616841)
        ·
          refine ⟨19486236932328127891212631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25981649243104170521616841 19486236932328127891212631)
          ·
            refine ⟨29229355398492191836818947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19486236932328127891212631 29229355398492191836818947)
            ·
              refine ⟨43844033097738287755228421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29229355398492191836818947 43844033097738287755228421)
              ·
                refine ⟨8220756205825928954105329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43844033097738287755228421 8220756205825928954105329)
                ·
                  refine ⟨6165567154369446715578997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8220756205825928954105329 6165567154369446715578997)
                  ·
                    refine ⟨578021920722135629585531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6165567154369446715578997 578021920722135629585531)
                    ·
                      rfl

theorem cell23_3377081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 2, 5].length) (baseStart_3377081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377081 prefixEnd_3377081 := by exact prefixLift 3377081
  have htrace : WordTrace (prefixWord ++ tailWord_3377081) baseStart_3377081 baseEnd_3377081 := by
    simpa [prefixWord, tailWord_3377081, baseEnd_3377081] using wordTrace_append hprefix tailTrace_3377081
  have hstable : (prefixWord ++ tailWord_3377081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377081).length < 2 ^ (prefixWord ++ tailWord_3377081).sum := by decide
  have hdescent : baseEnd_3377081 < baseStart_3377081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377085 : List Nat := [1, 4, 1, 2, 3, 1, 4, 2, 5]
def baseStart_3377085 : Nat := 118140960795 + 3377085 * 2 ^ 59
def prefixEnd_3377085 : Nat := 4983230072969 + 3 ^ 40 * 3377085 * 2
def baseEnd_3377085 : Nat := 192674201787669430345175

theorem tailTrace_3377085 : CollatzResearch.WordTrace tailWord_3377085 prefixEnd_3377085 192674201787669430345175 := by
  unfold tailWord_3377085
  simp only [CollatzResearch.WordTrace]
  refine ⟨123172408970405280044884709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82114939313603520029923139 123172408970405280044884709)
  ·
    refine ⟨23094826681950990008415883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123172408970405280044884709 23094826681950990008415883)
    ·
      refine ⟨34642240022926485012623825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23094826681950990008415883 34642240022926485012623825)
      ·
        refine ⟨25981680017194863759467869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34642240022926485012623825 25981680017194863759467869)
        ·
          refine ⟨9743130006448073909800451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25981680017194863759467869 9743130006448073909800451)
          ·
            refine ⟨14614695009672110864700677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743130006448073909800451 14614695009672110864700677)
            ·
              refine ⟨2740255314313520787131377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14614695009672110864700677 2740255314313520787131377)
              ·
                refine ⟨2055191485735140590348533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740255314313520787131377 2055191485735140590348533)
                ·
                  refine ⟨192674201787669430345175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2055191485735140590348533 192674201787669430345175)
                  ·
                    rfl

theorem cell23_3377085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_3377085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377085 prefixEnd_3377085 := by exact prefixLift 3377085
  have htrace : WordTrace (prefixWord ++ tailWord_3377085) baseStart_3377085 baseEnd_3377085 := by
    simpa [prefixWord, tailWord_3377085, baseEnd_3377085] using wordTrace_append hprefix tailTrace_3377085
  have hstable : (prefixWord ++ tailWord_3377085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377085).length < 2 ^ (prefixWord ++ tailWord_3377085).sum := by decide
  have hdescent : baseEnd_3377085 < baseStart_3377085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377145 : List Nat := [1, 2, 1, 3, 1, 4, 2, 4, 1, 4]
def baseStart_3377145 : Nat := 118140960795 + 3377145 * 2 ^ 59
def prefixEnd_3377145 : Nat := 4983230072969 + 3 ^ 40 * 3377145 * 2
def baseEnd_3377145 : Nat := 578032874976098212785433

theorem tailTrace_3377145 : CollatzResearch.WordTrace tailWord_3377145 prefixEnd_3377145 578032874976098212785433 := by
  unfold tailWord_3377145
  simp only [CollatzResearch.WordTrace]
  refine ⟨123174597350187910292068889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82116398233458606861379259 123174597350187910292068889)
  ·
    refine ⟨92380948012640932719051667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123174597350187910292068889 92380948012640932719051667)
    ·
      refine ⟨138571422018961399078577501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92380948012640932719051667 138571422018961399078577501)
      ·
        refine ⟨51964283257110524654466563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138571422018961399078577501 51964283257110524654466563)
        ·
          refine ⟨77946424885665786981699845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51964283257110524654466563 77946424885665786981699845)
          ·
            refine ⟨14614954666062335059068721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77946424885665786981699845 14614954666062335059068721)
            ·
              refine ⟨10961215999546751294301541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14614954666062335059068721 10961215999546751294301541)
              ·
                refine ⟨2055227999915015867681539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10961215999546751294301541 2055227999915015867681539)
                ·
                  refine ⟨3082841999872523801522309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055227999915015867681539 3082841999872523801522309)
                  ·
                    refine ⟨578032874976098212785433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3082841999872523801522309 578032874976098212785433)
                    ·
                      rfl

theorem cell23_3377145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 1, 4].length) (baseStart_3377145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377145 prefixEnd_3377145 := by exact prefixLift 3377145
  have htrace : WordTrace (prefixWord ++ tailWord_3377145) baseStart_3377145 baseEnd_3377145 := by
    simpa [prefixWord, tailWord_3377145, baseEnd_3377145] using wordTrace_append hprefix tailTrace_3377145
  have hstable : (prefixWord ++ tailWord_3377145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377145).length < 2 ^ (prefixWord ++ tailWord_3377145).sum := by decide
  have hdescent : baseEnd_3377145 < baseStart_3377145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377171 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 3, 5]
def baseStart_3377171 : Nat := 118140960795 + 3377171 * 2 ^ 59
def prefixEnd_3377171 : Nat := 4983230072969 + 3 ^ 40 * 3377171 * 2
def baseEnd_3377171 : Nat := 578037325141770512210393

theorem tailTrace_3377171 : CollatzResearch.WordTrace tailWord_3377171 prefixEnd_3377171 578037325141770512210393 := by
  unfold tailWord_3377171
  simp only [CollatzResearch.WordTrace]
  refine ⟨123175545648093716732515367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82117030432062477821676911 123175545648093716732515367)
  ·
    refine ⟨184763318472140575098773051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123175545648093716732515367 184763318472140575098773051)
    ·
      refine ⟨277144977708210862648159577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184763318472140575098773051 277144977708210862648159577)
      ·
        refine ⟨207858733281158146986119683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277144977708210862648159577 207858733281158146986119683)
        ·
          refine ⟨311788099921737220479179525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207858733281158146986119683 311788099921737220479179525)
          ·
            refine ⟨58460268735325728839846161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311788099921737220479179525 58460268735325728839846161)
            ·
              refine ⟨43845201551494296629884621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58460268735325728839846161 43845201551494296629884621)
              ·
                refine ⟨16441950581810361236206733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43845201551494296629884621 16441950581810361236206733)
                ·
                  refine ⟨6165731468178885463577525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16441950581810361236206733 6165731468178885463577525)
                  ·
                    refine ⟨578037325141770512210393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6165731468178885463577525 578037325141770512210393)
                    ·
                      rfl

theorem cell23_3377171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 5].length) (baseStart_3377171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377171 prefixEnd_3377171 := by exact prefixLift 3377171
  have htrace : WordTrace (prefixWord ++ tailWord_3377171) baseStart_3377171 baseEnd_3377171 := by
    simpa [prefixWord, tailWord_3377171, baseEnd_3377171] using wordTrace_append hprefix tailTrace_3377171
  have hstable : (prefixWord ++ tailWord_3377171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377171).length < 2 ^ (prefixWord ++ tailWord_3377171).sum := by decide
  have hdescent : baseEnd_3377171 < baseStart_3377171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377202 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3]
def baseStart_3377202 : Nat := 118140960795 + 3377202 * 2 ^ 59
def prefixEnd_3377202 : Nat := 4983230072969 + 3 ^ 40 * 3377202 * 2
def baseEnd_3377202 : Nat := 1734127893325600915343537

theorem tailTrace_3377202 : CollatzResearch.WordTrace tailWord_3377202 prefixEnd_3377202 1734127893325600915343537 := by
  unfold tailWord_3377202
  simp only [CollatzResearch.WordTrace]
  refine ⟨30794169077745352256723465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82117784207320939351262573 30794169077745352256723465)
  ·
    refine ⟨23095626808309014192542599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30794169077745352256723465 23095626808309014192542599)
    ·
      refine ⟨34643440212463521288813899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23095626808309014192542599 34643440212463521288813899)
      ·
        refine ⟨51965160318695281933220849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34643440212463521288813899 51965160318695281933220849)
        ·
          refine ⟨38973870239021461449915637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51965160318695281933220849 38973870239021461449915637)
          ·
            refine ⟨3653800334908262010929591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38973870239021461449915637 3653800334908262010929591)
            ·
              refine ⟨5480700502362393016394387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653800334908262010929591 5480700502362393016394387)
              ·
                refine ⟨8221050753543589524591581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480700502362393016394387 8221050753543589524591581)
                ·
                  refine ⟨3082894032578846071721843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8221050753543589524591581 3082894032578846071721843)
                  ·
                    refine ⟨4624341048868269107582765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3082894032578846071721843 4624341048868269107582765)
                    ·
                      refine ⟨1734127893325600915343537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4624341048868269107582765 1734127893325600915343537)
                      ·
                        rfl

theorem cell23_3377202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3].length) (baseStart_3377202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377202 prefixEnd_3377202 := by exact prefixLift 3377202
  have htrace : WordTrace (prefixWord ++ tailWord_3377202) baseStart_3377202 baseEnd_3377202 := by
    simpa [prefixWord, tailWord_3377202, baseEnd_3377202] using wordTrace_append hprefix tailTrace_3377202
  have hstable : (prefixWord ++ tailWord_3377202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377202).length < 2 ^ (prefixWord ++ tailWord_3377202).sum := by decide
  have hdescent : baseEnd_3377202 < baseStart_3377202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377225 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 5, 2, 2]
def baseStart_3377225 : Nat := 118140960795 + 3377225 * 2 ^ 59
def prefixEnd_3377225 : Nat := 4983230072969 + 3 ^ 40 * 3377225 * 2
def baseEnd_3377225 : Nat := 1734139703380654325355931

theorem tailTrace_3377225 : CollatzResearch.WordTrace tailWord_3377225 prefixEnd_3377225 1734139703380654325355931 := by
  unfold tailWord_3377225
  simp only [CollatzResearch.WordTrace]
  refine ⟨123177515189898083954981129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82118343459932055969987419 123177515189898083954981129)
  ·
    refine ⟨92383136392423562966235847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123177515189898083954981129 92383136392423562966235847)
    ·
      refine ⟨138574704588635344449353771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92383136392423562966235847 138574704588635344449353771)
      ·
        refine ⟨207862056882953016674030657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138574704588635344449353771 207862056882953016674030657)
        ·
          refine ⟨155896542662214762505522993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207862056882953016674030657 155896542662214762505522993)
          ·
            refine ⟨116922406996661071879142245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155896542662214762505522993 116922406996661071879142245)
            ·
              refine ⟨21922951311873950977339171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116922406996661071879142245 21922951311873950977339171)
              ·
                refine ⟨32884426967810926466008757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21922951311873950977339171 32884426967810926466008757)
                ·
                  refine ⟨3082915028232274356188321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32884426967810926466008757 3082915028232274356188321)
                  ·
                    refine ⟨2312186271174205767141241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3082915028232274356188321 2312186271174205767141241)
                    ·
                      refine ⟨1734139703380654325355931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312186271174205767141241 1734139703380654325355931)
                      ·
                        rfl

theorem cell23_3377225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 5, 2, 2].length) (baseStart_3377225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377225 prefixEnd_3377225 := by exact prefixLift 3377225
  have htrace : WordTrace (prefixWord ++ tailWord_3377225) baseStart_3377225 baseEnd_3377225 := by
    simpa [prefixWord, tailWord_3377225, baseEnd_3377225] using wordTrace_append hprefix tailTrace_3377225
  have hstable : (prefixWord ++ tailWord_3377225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377225).length < 2 ^ (prefixWord ++ tailWord_3377225).sum := by decide
  have hdescent : baseEnd_3377225 < baseStart_3377225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377308 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_3377308 : Nat := 118140960795 + 3377308 * 2 ^ 59
def prefixEnd_3377308 : Nat := 4983230072969 + 3 ^ 40 * 3377308 * 2
def baseEnd_3377308 : Nat := 578060774091659166872683

theorem tailTrace_3377308 : CollatzResearch.WordTrace tailWord_3377308 prefixEnd_3377308 578060774091659166872683 := by
  unfold tailWord_3377308
  simp only [CollatzResearch.WordTrace]
  refine ⟨61590271224298694565126289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82120361632398259420168385 61590271224298694565126289)
  ·
    refine ⟨46192703418224020923844717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61590271224298694565126289 46192703418224020923844717)
    ·
      refine ⟨17322263781834007846441769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46192703418224020923844717 17322263781834007846441769)
      ·
        refine ⟨12991697836375505884831327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17322263781834007846441769 12991697836375505884831327)
        ·
          refine ⟨19487546754563258827246991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12991697836375505884831327 19487546754563258827246991)
          ·
            refine ⟨29231320131844888240870487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19487546754563258827246991 29231320131844888240870487)
            ·
              refine ⟨43846980197767332361305731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29231320131844888240870487 43846980197767332361305731)
              ·
                refine ⟨65770470296650998541958597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43846980197767332361305731 65770470296650998541958597)
                ·
                  refine ⟨12331963180622062226617237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65770470296650998541958597 12331963180622062226617237)
                  ·
                    refine ⟨578060774091659166872683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12331963180622062226617237 578060774091659166872683)
                    ·
                      rfl

theorem cell23_3377308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3377308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377308 prefixEnd_3377308 := by exact prefixLift 3377308
  have htrace : WordTrace (prefixWord ++ tailWord_3377308) baseStart_3377308 baseEnd_3377308 := by
    simpa [prefixWord, tailWord_3377308, baseEnd_3377308] using wordTrace_append hprefix tailTrace_3377308
  have hstable : (prefixWord ++ tailWord_3377308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377308).length < 2 ^ (prefixWord ++ tailWord_3377308).sum := by decide
  have hdescent : baseEnd_3377308 < baseStart_3377308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377309 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_3377309 : Nat := 118140960795 + 3377309 * 2 ^ 59
def prefixEnd_3377309 : Nat := 4983230072969 + 3 ^ 40 * 3377309 * 2
def baseEnd_3377309 : Nat := 1734182835755631996705545

theorem tailTrace_3377309 : CollatzResearch.WordTrace tailWord_3377309 prefixEnd_3377309 1734182835755631996705545 := by
  unfold tailWord_3377309
  simp only [CollatzResearch.WordTrace]
  refine ⟨123180578921593766301038981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82120385947729177534025987 123180578921593766301038981)
  ·
    refine ⟨23096358547798831181444809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123180578921593766301038981 23096358547798831181444809)
    ·
      refine ⟨17322268910849123386083607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23096358547798831181444809 17322268910849123386083607)
      ·
        refine ⟨25983403366273685079125411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17322268910849123386083607 25983403366273685079125411)
        ·
          refine ⟨38975105049410527618688117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25983403366273685079125411 38975105049410527618688117)
          ·
            refine ⟨3653916098382236964252011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38975105049410527618688117 3653916098382236964252011)
            ·
              refine ⟨5480874147573355446378017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653916098382236964252011 5480874147573355446378017)
              ·
                refine ⟨4110655610680016584783513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5480874147573355446378017 4110655610680016584783513)
                ·
                  refine ⟨3082991708010012438587635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4110655610680016584783513 3082991708010012438587635)
                  ·
                    refine ⟨4624487562015018657881453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3082991708010012438587635 4624487562015018657881453)
                    ·
                      refine ⟨1734182835755631996705545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4624487562015018657881453 1734182835755631996705545)
                      ·
                        rfl

theorem cell23_3377309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_3377309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377309 prefixEnd_3377309 := by exact prefixLift 3377309
  have htrace : WordTrace (prefixWord ++ tailWord_3377309) baseStart_3377309 baseEnd_3377309 := by
    simpa [prefixWord, tailWord_3377309, baseEnd_3377309] using wordTrace_append hprefix tailTrace_3377309
  have hstable : (prefixWord ++ tailWord_3377309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377309).length < 2 ^ (prefixWord ++ tailWord_3377309).sum := by decide
  have hdescent : baseEnd_3377309 < baseStart_3377309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377325 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3377325 : Nat := 118140960795 + 3377325 * 2 ^ 59
def prefixEnd_3377325 : Nat := 4983230072969 + 3 ^ 40 * 3377325 * 2
def baseEnd_3377325 : Nat := 578063683815367978035157

theorem tailTrace_3377325 : CollatzResearch.WordTrace tailWord_3377325 prefixEnd_3377325 578063683815367978035157 := by
  unfold tailWord_3377325
  simp only [CollatzResearch.WordTrace]
  refine ⟨123181162489535801033621429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82120774993023867355747619 123181162489535801033621429)
  ·
    refine ⟨11548233983393981346902009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123181162489535801033621429 11548233983393981346902009)
    ·
      refine ⟨8661175487545486010176507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11548233983393981346902009 8661175487545486010176507)
      ·
        refine ⟨12991763231318229015264761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8661175487545486010176507 12991763231318229015264761)
        ·
          refine ⟨9743822423488671761448571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12991763231318229015264761 9743822423488671761448571)
          ·
            refine ⟨14615733635233007642172857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743822423488671761448571 14615733635233007642172857)
            ·
              refine ⟨10961800226424755731629643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14615733635233007642172857 10961800226424755731629643)
              ·
                refine ⟨16442700339637133597444465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10961800226424755731629643 16442700339637133597444465)
                ·
                  refine ⟨12332025254727850198083349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16442700339637133597444465 12332025254727850198083349)
                  ·
                    refine ⟨578063683815367978035157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12332025254727850198083349 578063683815367978035157)
                    ·
                      rfl

theorem cell23_3377325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3377325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377325 prefixEnd_3377325 := by exact prefixLift 3377325
  have htrace : WordTrace (prefixWord ++ tailWord_3377325) baseStart_3377325 baseEnd_3377325 := by
    simpa [prefixWord, tailWord_3377325, baseEnd_3377325] using wordTrace_append hprefix tailTrace_3377325
  have hstable : (prefixWord ++ tailWord_3377325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377325).length < 2 ^ (prefixWord ++ tailWord_3377325).sum := by decide
  have hdescent : baseEnd_3377325 < baseStart_3377325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377326 : List Nat := [4, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3377326 : Nat := 118140960795 + 3377326 * 2 ^ 59
def prefixEnd_3377326 : Nat := 4983230072969 + 3 ^ 40 * 3377326 * 2
def baseEnd_3377326 : Nat := 1734191564926758430192967

theorem tailTrace_3377326 : CollatzResearch.WordTrace tailWord_3377326 prefixEnd_3377326 1734191564926758430192967 := by
  unfold tailWord_3377326
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397649870316522275550979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82120799308354785469605221 15397649870316522275550979)
  ·
    refine ⟨23096474805474783413326469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15397649870316522275550979 23096474805474783413326469)
    ·
      refine ⟨4330589026026521889998713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23096474805474783413326469 4330589026026521889998713)
      ·
        refine ⟨3247941769519891417499035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4330589026026521889998713 3247941769519891417499035)
        ·
          refine ⟨4871912654279837126248553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247941769519891417499035 4871912654279837126248553)
          ·
            refine ⟨3653934490709877844686415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4871912654279837126248553 3653934490709877844686415)
            ·
              refine ⟨5480901736064816767029623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653934490709877844686415 5480901736064816767029623)
              ·
                refine ⟨8221352604097225150544435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5480901736064816767029623 8221352604097225150544435)
                ·
                  refine ⟨12332028906145837725816653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8221352604097225150544435 12332028906145837725816653)
                  ·
                    refine ⟨4624510839804689147181245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12332028906145837725816653 4624510839804689147181245)
                    ·
                      refine ⟨1734191564926758430192967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4624510839804689147181245 1734191564926758430192967)
                      ·
                        rfl

theorem cell23_3377326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3377326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377326 prefixEnd_3377326 := by exact prefixLift 3377326
  have htrace : WordTrace (prefixWord ++ tailWord_3377326) baseStart_3377326 baseEnd_3377326 := by
    simpa [prefixWord, tailWord_3377326, baseEnd_3377326] using wordTrace_append hprefix tailTrace_3377326
  have hstable : (prefixWord ++ tailWord_3377326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377326).length < 2 ^ (prefixWord ++ tailWord_3377326).sum := by decide
  have hdescent : baseEnd_3377326 < baseStart_3377326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377338 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_3377338 : Nat := 118140960795 + 3377338 * 2 ^ 59
def prefixEnd_3377338 : Nat := 4983230072969 + 3 ^ 40 * 3377338 * 2
def baseEnd_3377338 : Nat := 192688636299401375915879

theorem tailTrace_3377338 : CollatzResearch.WordTrace tailWord_3377338 prefixEnd_3377338 192688636299401375915879 := by
  unfold tailWord_3377338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795409159622176063461167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82121091092325802835896445 30795409159622176063461167)
  ·
    refine ⟨46193113739433264095191751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30795409159622176063461167 46193113739433264095191751)
    ·
      refine ⟨69289670609149896142787627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46193113739433264095191751 69289670609149896142787627)
      ·
        refine ⟨103934505913724844214181441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69289670609149896142787627 103934505913724844214181441)
        ·
          refine ⟨77950879435293633160636081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103934505913724844214181441 77950879435293633160636081)
          ·
            refine ⟨58463159576470224870477061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77950879435293633160636081 58463159576470224870477061)
            ·
              refine ⟨10961842420588167163214449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58463159576470224870477061 10961842420588167163214449)
              ·
                refine ⟨8221381815441125372410837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10961842420588167163214449 8221381815441125372410837)
                ·
                  refine ⟨192688636299401375915879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8221381815441125372410837 192688636299401375915879)
                  ·
                    rfl

theorem cell23_3377338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_3377338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377338 prefixEnd_3377338 := by exact prefixLift 3377338
  have htrace : WordTrace (prefixWord ++ tailWord_3377338) baseStart_3377338 baseEnd_3377338 := by
    simpa [prefixWord, tailWord_3377338, baseEnd_3377338] using wordTrace_append hprefix tailTrace_3377338
  have hstable : (prefixWord ++ tailWord_3377338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377338).length < 2 ^ (prefixWord ++ tailWord_3377338).sum := by decide
  have hdescent : baseEnd_3377338 < baseStart_3377338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377366 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 4, 2, 2]
def baseStart_3377366 : Nat := 118140960795 + 3377366 * 2 ^ 59
def prefixEnd_3377366 : Nat := 4983230072969 + 3 ^ 40 * 3377366 * 2
def baseEnd_3377366 : Nat := 1734212104152938273692783

theorem tailTrace_3377366 : CollatzResearch.WordTrace tailWord_3377366 prefixEnd_3377366 1734212104152938273692783 := by
  unfold tailWord_3377366
  simp only [CollatzResearch.WordTrace]
  refine ⟨7698916117649204064741497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82121771921591510023909301 7698916117649204064741497)
  ·
    refine ⟨5774187088236903048556123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7698916117649204064741497 5774187088236903048556123)
    ·
      refine ⟨8661280632355354572834185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774187088236903048556123 8661280632355354572834185)
      ·
        refine ⟨6495960474266515929625639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8661280632355354572834185 6495960474266515929625639)
        ·
          refine ⟨9743940711399773894438459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6495960474266515929625639 9743940711399773894438459)
          ·
            refine ⟨14615911067099660841657689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743940711399773894438459 14615911067099660841657689)
            ·
              refine ⟨10961933300324745631243267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14615911067099660841657689 10961933300324745631243267)
              ·
                refine ⟨16442899950487118446864901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10961933300324745631243267 16442899950487118446864901)
                ·
                  refine ⟨3083043740716334708787169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16442899950487118446864901 3083043740716334708787169)
                  ·
                    refine ⟨2312282805537251031590377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083043740716334708787169 2312282805537251031590377)
                    ·
                      refine ⟨1734212104152938273692783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312282805537251031590377 1734212104152938273692783)
                      ·
                        rfl

theorem cell23_3377366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_3377366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377366 prefixEnd_3377366 := by exact prefixLift 3377366
  have htrace : WordTrace (prefixWord ++ tailWord_3377366) baseStart_3377366 baseEnd_3377366 := by
    simpa [prefixWord, tailWord_3377366, baseEnd_3377366] using wordTrace_append hprefix tailTrace_3377366
  have hstable : (prefixWord ++ tailWord_3377366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377366).length < 2 ^ (prefixWord ++ tailWord_3377366).sum := by decide
  have hdescent : baseEnd_3377366 < baseStart_3377366 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377375 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 2, 5, 2]
def baseStart_3377375 : Nat := 118140960795 + 3377375 * 2 ^ 59
def prefixEnd_3377375 : Nat := 4983230072969 + 3 ^ 40 * 3377375 * 2
def baseEnd_3377375 : Nat := 1734216725478828738480241

theorem tailTrace_3377375 : CollatzResearch.WordTrace tailWord_3377375 prefixEnd_3377375 1734216725478828738480241 := by
  unfold tailWord_3377375
  simp only [CollatzResearch.WordTrace]
  refine ⟨123182986139354659572941579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82121990759569773048627719 123182986139354659572941579)
  ·
    refine ⟨184774479209031989359412369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123182986139354659572941579 184774479209031989359412369)
    ·
      refine ⟨138580859406773992019559277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184774479209031989359412369 138580859406773992019559277)
      ·
        refine ⟨51967822277540247007334729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138580859406773992019559277 51967822277540247007334729)
        ·
          refine ⟨38975866708155185255501047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51967822277540247007334729 38975866708155185255501047)
          ·
            refine ⟨58463800062232777883251571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38975866708155185255501047 58463800062232777883251571)
            ·
              refine ⟨87695700093349166824877357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58463800062232777883251571 87695700093349166824877357)
              ·
                refine ⟨32885887535005937559329009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87695700093349166824877357 32885887535005937559329009)
                ·
                  refine ⟨24664415651254453169496757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32885887535005937559329009 24664415651254453169496757)
                  ·
                    refine ⟨2312288967305104984640321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24664415651254453169496757 2312288967305104984640321)
                    ·
                      refine ⟨1734216725478828738480241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312288967305104984640321 1734216725478828738480241)
                      ·
                        rfl

theorem cell23_3377375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_3377375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377375 prefixEnd_3377375 := by exact prefixLift 3377375
  have htrace : WordTrace (prefixWord ++ tailWord_3377375) baseStart_3377375 baseEnd_3377375 := by
    simpa [prefixWord, tailWord_3377375, baseEnd_3377375] using wordTrace_append hprefix tailTrace_3377375
  have hstable : (prefixWord ++ tailWord_3377375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377375).length < 2 ^ (prefixWord ++ tailWord_3377375).sum := by decide
  have hdescent : baseEnd_3377375 < baseStart_3377375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377383 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3377383 : Nat := 118140960795 + 3377383 * 2 ^ 59
def prefixEnd_3377383 : Nat := 4983230072969 + 3 ^ 40 * 3377383 * 2
def baseEnd_3377383 : Nat := 1734220833324064707180205

theorem tailTrace_3377383 : CollatzResearch.WordTrace tailWord_3377383 prefixEnd_3377383 1734220833324064707180205 := by
  unfold tailWord_3377383
  simp only [CollatzResearch.WordTrace]
  refine ⟨123183277923325676939232803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82122185282217117959488535 123183277923325676939232803)
  ·
    refine ⟨184774916884988515408849205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123183277923325676939232803 184774916884988515408849205)
    ·
      refine ⟨17322648457967673319579613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184774916884988515408849205 17322648457967673319579613)
      ·
        refine ⟨6495993171737877494842355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17322648457967673319579613 6495993171737877494842355)
        ·
          refine ⟨9743989757606816242263533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6495993171737877494842355 9743989757606816242263533)
          ·
            refine ⟨3653996159102556090848825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9743989757606816242263533 3653996159102556090848825)
            ·
              refine ⟨2740497119326917068136619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3653996159102556090848825 2740497119326917068136619)
              ·
                refine ⟨4110745678990375602204929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740497119326917068136619 4110745678990375602204929)
                ·
                  refine ⟨3083059259242781701653697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4110745678990375602204929 3083059259242781701653697)
                  ·
                    refine ⟨2312294444432086276240273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083059259242781701653697 2312294444432086276240273)
                    ·
                      refine ⟨1734220833324064707180205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312294444432086276240273 1734220833324064707180205)
                      ·
                        rfl

theorem cell23_3377383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3377383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377383 prefixEnd_3377383 := by exact prefixLift 3377383
  have htrace : WordTrace (prefixWord ++ tailWord_3377383) baseStart_3377383 baseEnd_3377383 := by
    simpa [prefixWord, tailWord_3377383, baseEnd_3377383] using wordTrace_append hprefix tailTrace_3377383
  have hstable : (prefixWord ++ tailWord_3377383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377383).length < 2 ^ (prefixWord ++ tailWord_3377383).sum := by decide
  have hdescent : baseEnd_3377383 < baseStart_3377383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377422 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2]
def baseStart_3377422 : Nat := 118140960795 + 3377422 * 2 ^ 59
def prefixEnd_3377422 : Nat := 4983230072969 + 3 ^ 40 * 3377422 * 2
def baseEnd_3377422 : Nat := 1734240859069590054592525

theorem tailTrace_3377422 : CollatzResearch.WordTrace tailWord_3377422 prefixEnd_3377422 1734240859069590054592525 := by
  unfold tailWord_3377422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398087546273048324987815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82123133580122924399935013 15398087546273048324987815)
  ·
    refine ⟨23097131319409572487481723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15398087546273048324987815 23097131319409572487481723)
    ·
      refine ⟨34645696979114358731222585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23097131319409572487481723 34645696979114358731222585)
      ·
        refine ⟨25984272734335769048416939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34645696979114358731222585 25984272734335769048416939)
        ·
          refine ⟨38976409101503653572625409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25984272734335769048416939 38976409101503653572625409)
          ·
            refine ⟨29232306826127740179469057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38976409101503653572625409 29232306826127740179469057)
            ·
              refine ⟨21924230119595805134601793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29232306826127740179469057 21924230119595805134601793)
              ·
                refine ⟨16443172589696853850951345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21924230119595805134601793 16443172589696853850951345)
                ·
                  refine ⟨12332379442272640388213509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16443172589696853850951345 12332379442272640388213509)
                  ·
                    refine ⟨2312321145426120072790033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12332379442272640388213509 2312321145426120072790033)
                    ·
                      refine ⟨1734240859069590054592525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312321145426120072790033 1734240859069590054592525)
                      ·
                        rfl

theorem cell23_3377422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_3377422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377422 prefixEnd_3377422 := by exact prefixLift 3377422
  have htrace : WordTrace (prefixWord ++ tailWord_3377422) baseStart_3377422 baseEnd_3377422 := by
    simpa [prefixWord, tailWord_3377422, baseEnd_3377422] using wordTrace_append hprefix tailTrace_3377422
  have hstable : (prefixWord ++ tailWord_3377422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377422).length < 2 ^ (prefixWord ++ tailWord_3377422).sum := by decide
  have hdescent : baseEnd_3377422 < baseStart_3377422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377489 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 3]
def baseStart_3377489 : Nat := 118140960795 + 3377489 * 2 ^ 59
def prefixEnd_3377489 : Nat := 4983230072969 + 3 ^ 40 * 3377489 * 2
def baseEnd_3377489 : Nat := 1734275262273441292454717

theorem tailTrace_3377489 : CollatzResearch.WordTrace tailWord_3377489 prefixEnd_3377489 1734275262273441292454717 := by
  unfold tailWord_3377489
  simp only [CollatzResearch.WordTrace]
  refine ⟨123187144060941657042591521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82124762707294438028394347 123187144060941657042591521)
  ·
    refine ⟨92390358045706242781943641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123187144060941657042591521 92390358045706242781943641)
    ·
      refine ⟨69292768534279682086457731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92390358045706242781943641 69292768534279682086457731)
      ·
        refine ⟨103939152801419523129686597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69292768534279682086457731 103939152801419523129686597)
        ·
          refine ⟨19488591150266160586816237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103939152801419523129686597 19488591150266160586816237)
          ·
            refine ⟨7308221681349810220056089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19488591150266160586816237 7308221681349810220056089)
            ·
              refine ⟨5481166261012357665042067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7308221681349810220056089 5481166261012357665042067)
              ·
                refine ⟨8221749391518536497563101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481166261012357665042067 8221749391518536497563101)
                ·
                  refine ⟨3083156021819451186586163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8221749391518536497563101 3083156021819451186586163)
                  ·
                    refine ⟨4624734032729176779879245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3083156021819451186586163 4624734032729176779879245)
                    ·
                      refine ⟨1734275262273441292454717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4624734032729176779879245 1734275262273441292454717)
                      ·
                        rfl

theorem cell23_3377489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_3377489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377489 prefixEnd_3377489 := by exact prefixLift 3377489
  have htrace : WordTrace (prefixWord ++ tailWord_3377489) baseStart_3377489 baseEnd_3377489 := by
    simpa [prefixWord, tailWord_3377489, baseEnd_3377489] using wordTrace_append hprefix tailTrace_3377489
  have hstable : (prefixWord ++ tailWord_3377489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377489).length < 2 ^ (prefixWord ++ tailWord_3377489).sum := by decide
  have hdescent : baseEnd_3377489 < baseStart_3377489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377522 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 4, 4]
def baseStart_3377522 : Nat := 118140960795 + 3377522 * 2 ^ 59
def prefixEnd_3377522 : Nat := 4983230072969 + 3 ^ 40 * 3377522 * 2
def baseEnd_3377522 : Nat := 578097402378346554447355

theorem tailTrace_3377522 : CollatzResearch.WordTrace tailWord_3377522 prefixEnd_3377522 578097402378346554447355 := by
  unfold tailWord_3377522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30797086917455525919635705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82125565113214735785695213 30797086917455525919635705)
  ·
    refine ⟨23097815188091644439726779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30797086917455525919635705 23097815188091644439726779)
    ·
      refine ⟨34646722782137466659590169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23097815188091644439726779 34646722782137466659590169)
      ·
        refine ⟨25985042086603099994692627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34646722782137466659590169 25985042086603099994692627)
        ·
          refine ⟨38977563129904649992038941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25985042086603099994692627 38977563129904649992038941)
          ·
            refine ⟨14616586173714243747014603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38977563129904649992038941 14616586173714243747014603)
            ·
              refine ⟨21924879260571365620521905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14616586173714243747014603 21924879260571365620521905)
              ·
                refine ⟨16443659445428524215391429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21924879260571365620521905 16443659445428524215391429)
                ·
                  refine ⟨3083186146017848290385893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16443659445428524215391429 3083186146017848290385893)
                  ·
                    refine ⟨578097402378346554447355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083186146017848290385893 578097402378346554447355)
                    ·
                      rfl

theorem cell23_3377522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 4, 4].length) (baseStart_3377522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377522 prefixEnd_3377522 := by exact prefixLift 3377522
  have htrace : WordTrace (prefixWord ++ tailWord_3377522) baseStart_3377522 baseEnd_3377522 := by
    simpa [prefixWord, tailWord_3377522, baseEnd_3377522] using wordTrace_append hprefix tailTrace_3377522
  have hstable : (prefixWord ++ tailWord_3377522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377522).length < 2 ^ (prefixWord ++ tailWord_3377522).sum := by decide
  have hdescent : baseEnd_3377522 < baseStart_3377522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377556 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3377556 : Nat := 118140960795 + 3377556 * 2 ^ 59
def prefixEnd_3377556 : Nat := 4983230072969 + 3 ^ 40 * 3377556 * 2
def baseEnd_3377556 : Nat := 578103221825764176772303

theorem tailTrace_3377556 : CollatzResearch.WordTrace tailWord_3377556 prefixEnd_3377556 578103221825764176772303 := by
  unfold tailWord_3377556
  simp only [CollatzResearch.WordTrace]
  refine ⟨61594793875849463742640261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82126391834465951656853681 61594793875849463742640261)
  ·
    refine ⟨11549023851721774451745049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61594793875849463742640261 11549023851721774451745049)
    ·
      refine ⟨8661767888791330838808787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11549023851721774451745049 8661767888791330838808787)
      ·
        refine ⟨12992651833186996258213181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8661767888791330838808787 12992651833186996258213181)
        ·
          refine ⟨4872244437445123596829943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12992651833186996258213181 4872244437445123596829943)
          ·
            refine ⟨7308366656167685395244915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4872244437445123596829943 7308366656167685395244915)
            ·
              refine ⟨10962549984251528092867373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308366656167685395244915 10962549984251528092867373)
              ·
                refine ⟨4110956244094323034825265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10962549984251528092867373 4110956244094323034825265)
                ·
                  refine ⟨3083217183070742276118949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4110956244094323034825265 3083217183070742276118949)
                  ·
                    refine ⟨578103221825764176772303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083217183070742276118949 578103221825764176772303)
                    ·
                      rfl

theorem cell23_3377556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3377556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377556 prefixEnd_3377556 := by exact prefixLift 3377556
  have htrace : WordTrace (prefixWord ++ tailWord_3377556) baseStart_3377556 baseEnd_3377556 := by
    simpa [prefixWord, tailWord_3377556, baseEnd_3377556] using wordTrace_append hprefix tailTrace_3377556
  have hstable : (prefixWord ++ tailWord_3377556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377556).length < 2 ^ (prefixWord ++ tailWord_3377556).sum := by decide
  have hdescent : baseEnd_3377556 < baseStart_3377556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377566 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 3, 2, 3]
def baseStart_3377566 : Nat := 118140960795 + 3377566 * 2 ^ 59
def prefixEnd_3377566 : Nat := 4983230072969 + 3 ^ 40 * 3377566 * 2
def baseEnd_3377566 : Nat := 1734314800283837491191863

theorem tailTrace_3377566 : CollatzResearch.WordTrace tailWord_3377566 prefixEnd_3377566 1734314800283837491191863 := by
  unfold tailWord_3377566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15398744060207837399143069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82126634987775132795429701 15398744060207837399143069)
  ·
    refine ⟨5774529022577939024678651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15398744060207837399143069 5774529022577939024678651)
    ·
      refine ⟨8661793533866908537017977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774529022577939024678651 8661793533866908537017977)
      ·
        refine ⟨6496345150400181402763483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8661793533866908537017977 6496345150400181402763483)
        ·
          refine ⟨9744517725600272104145225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6496345150400181402763483 9744517725600272104145225)
          ·
            refine ⟨7308388294200204078108919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9744517725600272104145225 7308388294200204078108919)
            ·
              refine ⟨10962582441300306117163379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308388294200204078108919 10962582441300306117163379)
              ·
                refine ⟨16443873661950459175745069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10962582441300306117163379 16443873661950459175745069)
                ·
                  refine ⟨6166452623231422190904401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16443873661950459175745069 6166452623231422190904401)
                  ·
                    refine ⟨4624839467423566643178301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166452623231422190904401 4624839467423566643178301)
                    ·
                      refine ⟨1734314800283837491191863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4624839467423566643178301 1734314800283837491191863)
                      ·
                        rfl

theorem cell23_3377566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_3377566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377566 prefixEnd_3377566 := by exact prefixLift 3377566
  have htrace : WordTrace (prefixWord ++ tailWord_3377566) baseStart_3377566 baseEnd_3377566 := by
    simpa [prefixWord, tailWord_3377566, baseEnd_3377566] using wordTrace_append hprefix tailTrace_3377566
  have hstable : (prefixWord ++ tailWord_3377566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377566).length < 2 ^ (prefixWord ++ tailWord_3377566).sum := by decide
  have hdescent : baseEnd_3377566 < baseStart_3377566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377596 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3377596 : Nat := 118140960795 + 3377596 * 2 ^ 59
def prefixEnd_3377596 : Nat := 4983230072969 + 3 ^ 40 * 3377596 * 2
def baseEnd_3377596 : Nat := 1734330204703472373816725

theorem tailTrace_3377596 : CollatzResearch.WordTrace tailWord_3377596 prefixEnd_3377596 1734330204703472373816725 := by
  unfold tailWord_3377596
  simp only [CollatzResearch.WordTrace]
  refine ⟨61595523335777007158368321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82127364447702676211157761 61595523335777007158368321)
  ·
    refine ⟨46196642501832755368776241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61595523335777007158368321 46196642501832755368776241)
    ·
      refine ⟨34647481876374566526582181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46196642501832755368776241 34647481876374566526582181)
      ·
        refine ⟨6496402851820231223734159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34647481876374566526582181 6496402851820231223734159)
        ·
          refine ⟨9744604277730346835601239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6496402851820231223734159 9744604277730346835601239)
          ·
            refine ⟨14616906416595520253401859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9744604277730346835601239 14616906416595520253401859)
            ·
              refine ⟨21925359624893280380102789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14616906416595520253401859 21925359624893280380102789)
              ·
                refine ⟨4111004929667490071269273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21925359624893280380102789 4111004929667490071269273)
                ·
                  refine ⟨3083253697250617553451955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4111004929667490071269273 3083253697250617553451955)
                  ·
                    refine ⟨4624880545875926330177933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3083253697250617553451955 4624880545875926330177933)
                    ·
                      refine ⟨1734330204703472373816725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4624880545875926330177933 1734330204703472373816725)
                      ·
                        rfl

theorem cell23_3377596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3377596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377596 prefixEnd_3377596 := by exact prefixLift 3377596
  have htrace : WordTrace (prefixWord ++ tailWord_3377596) baseStart_3377596 baseEnd_3377596 := by
    simpa [prefixWord, tailWord_3377596, baseEnd_3377596] using wordTrace_append hprefix tailTrace_3377596
  have hstable : (prefixWord ++ tailWord_3377596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377596).length < 2 ^ (prefixWord ++ tailWord_3377596).sum := by decide
  have hdescent : baseEnd_3377596 < baseStart_3377596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377746 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 2, 2, 3]
def baseStart_3377746 : Nat := 118140960795 + 3377746 * 2 ^ 59
def prefixEnd_3377746 : Nat := 4983230072969 + 3 ^ 40 * 3377746 * 2
def baseEnd_3377746 : Nat := 1734407226801646786941035

theorem tailTrace_3377746 : CollatzResearch.WordTrace tailWord_3377746 prefixEnd_3377746 1734407226801646786941035 := by
  unfold tailWord_3377746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30799129405252647483674273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82131011747340393289798061 30799129405252647483674273)
  ·
    refine ⟨23099347053939485612755705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30799129405252647483674273 23099347053939485612755705)
    ·
      refine ⟨17324510290454614209566779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23099347053939485612755705 17324510290454614209566779)
      ·
        refine ⟨25986765435681921314350169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17324510290454614209566779 25986765435681921314350169)
        ·
          refine ⟨19490074076761440985762627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25986765435681921314350169 19490074076761440985762627)
          ·
            refine ⟨29235111115142161478643941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19490074076761440985762627 29235111115142161478643941)
            ·
              refine ⟨5481583334089155277245739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29235111115142161478643941 5481583334089155277245739)
              ·
                refine ⟨8222375001133732915868609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481583334089155277245739 8222375001133732915868609)
                ·
                  refine ⟨6166781250850299686901457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8222375001133732915868609 6166781250850299686901457)
                  ·
                    refine ⟨4625085938137724765176093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166781250850299686901457 4625085938137724765176093)
                    ·
                      refine ⟨1734407226801646786941035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625085938137724765176093 1734407226801646786941035)
                      ·
                        rfl

theorem cell23_3377746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_3377746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377746 prefixEnd_3377746 := by exact prefixLift 3377746
  have htrace : WordTrace (prefixWord ++ tailWord_3377746) baseStart_3377746 baseEnd_3377746 := by
    simpa [prefixWord, tailWord_3377746, baseEnd_3377746] using wordTrace_append hprefix tailTrace_3377746
  have hstable : (prefixWord ++ tailWord_3377746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377746).length < 2 ^ (prefixWord ++ tailWord_3377746).sum := by decide
  have hdescent : baseEnd_3377746 < baseStart_3377746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377769 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 3, 5, 2]
def baseStart_3377769 : Nat := 118140960795 + 3377769 * 2 ^ 59
def prefixEnd_3377769 : Nat := 4983230072969 + 3 ^ 40 * 3377769 * 2
def baseEnd_3377769 : Nat := 1734419036856700196953429

theorem tailTrace_3377769 : CollatzResearch.WordTrace tailWord_3377769 prefixEnd_3377769 1734419036856700196953429 := by
  unfold tailWord_3377769
  simp only [CollatzResearch.WordTrace]
  refine ⟨123197356499927264862784361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82131570999951509908522907 123197356499927264862784361)
  ·
    refine ⟨92398017374945448647088271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123197356499927264862784361 92398017374945448647088271)
    ·
      refine ⟨138597026062418172970632407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92398017374945448647088271 138597026062418172970632407)
      ·
        refine ⟨207895539093627259455948611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138597026062418172970632407 207895539093627259455948611)
        ·
          refine ⟨311843308640440889183922917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207895539093627259455948611 311843308640440889183922917)
          ·
            refine ⟨58470620370082666721985547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311843308640440889183922917 58470620370082666721985547)
            ·
              refine ⟨87705930555124000082978321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58470620370082666721985547 87705930555124000082978321)
              ·
                refine ⟨65779447916343000062233741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87705930555124000082978321 65779447916343000062233741)
                ·
                  refine ⟨24667292968628625023337653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65779447916343000062233741 24667292968628625023337653)
                  ·
                    refine ⟨2312558715808933595937905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24667292968628625023337653 2312558715808933595937905)
                    ·
                      refine ⟨1734419036856700196953429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312558715808933595937905 1734419036856700196953429)
                      ·
                        rfl

theorem cell23_3377769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 5, 2].length) (baseStart_3377769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377769 prefixEnd_3377769 := by exact prefixLift 3377769
  have htrace : WordTrace (prefixWord ++ tailWord_3377769) baseStart_3377769 baseEnd_3377769 := by
    simpa [prefixWord, tailWord_3377769, baseEnd_3377769] using wordTrace_append hprefix tailTrace_3377769
  have hstable : (prefixWord ++ tailWord_3377769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377769).length < 2 ^ (prefixWord ++ tailWord_3377769).sum := by decide
  have hdescent : baseEnd_3377769 < baseStart_3377769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377794 : List Nat := [3, 4, 3, 1, 2, 1, 1, 1, 2, 1, 4]
def baseStart_3377794 : Nat := 118140960795 + 3377794 * 2 ^ 59
def prefixEnd_3377794 : Nat := 4983230072969 + 3 ^ 40 * 3377794 * 2
def baseEnd_3377794 : Nat := 1734431873873062599140815

theorem tailTrace_3377794 : CollatzResearch.WordTrace tailWord_3377794 prefixEnd_3377794 1734431873873062599140815 := by
  unfold tailWord_3377794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30799567081209173533111109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82132178883224462754962957 30799567081209173533111109)
  ·
    refine ⟨5774918827726720037458333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30799567081209173533111109 5774918827726720037458333)
    ·
      refine ⟨2165594560397520014046875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5774918827726720037458333 2165594560397520014046875)
      ·
        refine ⟨3248391840596280021070313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165594560397520014046875 3248391840596280021070313)
        ·
          refine ⟨2436293880447210015802735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3248391840596280021070313 2436293880447210015802735)
          ·
            refine ⟨3654440820670815023704103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436293880447210015802735 3654440820670815023704103)
            ·
              refine ⟨5481661231006222535556155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654440820670815023704103 5481661231006222535556155)
              ·
                refine ⟨8222491846509333803334233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481661231006222535556155 8222491846509333803334233)
                ·
                  refine ⟨6166868884882000352500675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8222491846509333803334233 6166868884882000352500675)
                  ·
                    refine ⟨9250303327323000528751013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6166868884882000352500675 9250303327323000528751013)
                    ·
                      refine ⟨1734431873873062599140815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9250303327323000528751013 1734431873873062599140815)
                      ·
                        rfl

theorem cell23_3377794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_3377794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377794 prefixEnd_3377794 := by exact prefixLift 3377794
  have htrace : WordTrace (prefixWord ++ tailWord_3377794) baseStart_3377794 baseEnd_3377794 := by
    simpa [prefixWord, tailWord_3377794, baseEnd_3377794] using wordTrace_append hprefix tailTrace_3377794
  have hstable : (prefixWord ++ tailWord_3377794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377794).length < 2 ^ (prefixWord ++ tailWord_3377794).sum := by decide
  have hdescent : baseEnd_3377794 < baseStart_3377794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377799 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_3377799 : Nat := 118140960795 + 3377799 * 2 ^ 59
def prefixEnd_3377799 : Nat := 4983230072969 + 3 ^ 40 * 3377799 * 2
def baseEnd_3377799 : Nat := 1734434441276335079578291

theorem tailTrace_3377799 : CollatzResearch.WordTrace tailWord_3377799 prefixEnd_3377799 1734434441276335079578291 := by
  unfold tailWord_3377799
  simp only [CollatzResearch.WordTrace]
  refine ⟨123198450689818579986376451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82132300459879053324250967 123198450689818579986376451)
  ·
    refine ⟨184797676034727869979564677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123198450689818579986376451 184797676034727869979564677)
    ·
      refine ⟨34649564256511475621168377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184797676034727869979564677 34649564256511475621168377)
      ·
        refine ⟨25987173192383606715876283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34649564256511475621168377 25987173192383606715876283)
        ·
          refine ⟨38980759788575410073814425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25987173192383606715876283 38980759788575410073814425)
          ·
            refine ⟨29235569841431557555360819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38980759788575410073814425 29235569841431557555360819)
            ·
              refine ⟨43853354762147336333041229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29235569841431557555360819 43853354762147336333041229)
              ·
                refine ⟨16445008035805251124890461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43853354762147336333041229 16445008035805251124890461)
                ·
                  refine ⟨6166878013426969171833923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16445008035805251124890461 6166878013426969171833923)
                  ·
                    refine ⟨9250317020140453757750885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6166878013426969171833923 9250317020140453757750885)
                    ·
                      refine ⟨1734434441276335079578291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9250317020140453757750885 1734434441276335079578291)
                      ·
                        rfl

theorem cell23_3377799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_3377799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377799 prefixEnd_3377799 := by exact prefixLift 3377799
  have htrace : WordTrace (prefixWord ++ tailWord_3377799) baseStart_3377799 baseEnd_3377799 := by
    simpa [prefixWord, tailWord_3377799, baseEnd_3377799] using wordTrace_append hprefix tailTrace_3377799
  have hstable : (prefixWord ++ tailWord_3377799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377799).length < 2 ^ (prefixWord ++ tailWord_3377799).sum := by decide
  have hdescent : baseEnd_3377799 < baseStart_3377799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377810 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 1, 1, 3]
def baseStart_3377810 : Nat := 118140960795 + 3377810 * 2 ^ 59
def prefixEnd_3377810 : Nat := 4983230072969 + 3 ^ 40 * 3377810 * 2
def baseEnd_3377810 : Nat := 1734440089563534536540741

theorem tailTrace_3377810 : CollatzResearch.WordTrace tailWord_3377810 prefixEnd_3377810 1734440089563534536540741 := by
  unfold tailWord_3377810
  simp only [CollatzResearch.WordTrace]
  refine ⟨30799712973194682216256721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82132567928519152576684589 30799712973194682216256721)
  ·
    refine ⟨23099784729896011662192541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30799712973194682216256721 23099784729896011662192541)
    ·
      refine ⟨8662419273711004373322203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23099784729896011662192541 8662419273711004373322203)
      ·
        refine ⟨12993628910566506559983305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8662419273711004373322203 12993628910566506559983305)
        ·
          refine ⟨9745221682924879919987479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12993628910566506559983305 9745221682924879919987479)
          ·
            refine ⟨14617832524387319879981219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9745221682924879919987479 14617832524387319879981219)
            ·
              refine ⟨21926748786580979819971829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14617832524387319879981219 21926748786580979819971829)
              ·
                refine ⟨2055632698741966858122359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21926748786580979819971829 2055632698741966858122359)
                ·
                  refine ⟨3083449048112950287183539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055632698741966858122359 3083449048112950287183539)
                  ·
                    refine ⟨4625173572169425430775309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3083449048112950287183539 4625173572169425430775309)
                    ·
                      refine ⟨1734440089563534536540741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625173572169425430775309 1734440089563534536540741)
                      ·
                        rfl

theorem cell23_3377810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_3377810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377810 prefixEnd_3377810 := by exact prefixLift 3377810
  have htrace : WordTrace (prefixWord ++ tailWord_3377810) baseStart_3377810 baseEnd_3377810 := by
    simpa [prefixWord, tailWord_3377810, baseEnd_3377810] using wordTrace_append hprefix tailTrace_3377810
  have hstable : (prefixWord ++ tailWord_3377810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377810).length < 2 ^ (prefixWord ++ tailWord_3377810).sum := by decide
  have hdescent : baseEnd_3377810 < baseStart_3377810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377816 : List Nat := [2, 1, 2, 4, 1, 1, 3, 3, 1, 1, 4]
def baseStart_3377816 : Nat := 118140960795 + 3377816 * 2 ^ 59
def prefixEnd_3377816 : Nat := 4983230072969 + 3 ^ 40 * 3377816 * 2
def baseEnd_3377816 : Nat := 1734443170447461513065713

theorem tailTrace_3377816 : CollatzResearch.WordTrace tailWord_3377816 prefixEnd_3377816 1734443170447461513065713 := by
  unfold tailWord_3377816
  simp only [CollatzResearch.WordTrace]
  refine ⟨61599535365378495944872651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82132713820504661259830201 61599535365378495944872651)
  ·
    refine ⟨92399303048067743917308977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61599535365378495944872651 92399303048067743917308977)
    ·
      refine ⟨69299477286050807937981733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92399303048067743917308977 69299477286050807937981733)
      ·
        refine ⟨12993651991134526488371575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69299477286050807937981733 12993651991134526488371575)
        ·
          refine ⟨19490477986701789732557363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12993651991134526488371575 19490477986701789732557363)
          ·
            refine ⟨29235716980052684598836045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19490477986701789732557363 29235716980052684598836045)
            ·
              refine ⟨10963393867519756724563517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29235716980052684598836045 10963393867519756724563517)
              ·
                refine ⟨4111272700319908771711319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10963393867519756724563517 4111272700319908771711319)
                ·
                  refine ⟨6166909050479863157566979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111272700319908771711319 6166909050479863157566979)
                  ·
                    refine ⟨9250363575719794736350469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6166909050479863157566979 9250363575719794736350469)
                    ·
                      refine ⟨1734443170447461513065713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9250363575719794736350469 1734443170447461513065713)
                      ·
                        rfl

theorem cell23_3377816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_3377816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377816 prefixEnd_3377816 := by exact prefixLift 3377816
  have htrace : WordTrace (prefixWord ++ tailWord_3377816) baseStart_3377816 baseEnd_3377816 := by
    simpa [prefixWord, tailWord_3377816, baseEnd_3377816] using wordTrace_append hprefix tailTrace_3377816
  have hstable : (prefixWord ++ tailWord_3377816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377816).length < 2 ^ (prefixWord ++ tailWord_3377816).sum := by decide
  have hdescent : baseEnd_3377816 < baseStart_3377816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377843 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 2, 4]
def baseStart_3377843 : Nat := 118140960795 + 3377843 * 2 ^ 59
def prefixEnd_3377843 : Nat := 4983230072969 + 3 ^ 40 * 3377843 * 2
def baseEnd_3377843 : Nat := 578152344808377635809363

theorem tailTrace_3377843 : CollatzResearch.WordTrace tailWord_3377843 prefixEnd_3377843 578152344808377635809363 := by
  unfold tailWord_3377843
  simp only [CollatzResearch.WordTrace]
  refine ⟨123200055501659175500978183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82133370334439450333985455 123200055501659175500978183)
  ·
    refine ⟨184800083252488763251467275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123200055501659175500978183 184800083252488763251467275)
    ·
      refine ⟨277200124878733144877200913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184800083252488763251467275 277200124878733144877200913)
      ·
        refine ⟨207900093659049858657900685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277200124878733144877200913 207900093659049858657900685)
        ·
          refine ⟨77962535122143696996712757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207900093659049858657900685 77962535122143696996712757)
          ·
            refine ⟨7308987667700971593441821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77962535122143696996712757 7308987667700971593441821)
            ·
              refine ⟨2740870375387864347540683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7308987667700971593441821 2740870375387864347540683)
              ·
                refine ⟨4111305563081796521311025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740870375387864347540683 4111305563081796521311025)
                ·
                  refine ⟨3083479172311347390983269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4111305563081796521311025 3083479172311347390983269)
                  ·
                    refine ⟨578152344808377635809363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083479172311347390983269 578152344808377635809363)
                    ·
                      rfl

theorem cell23_3377843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 2, 4].length) (baseStart_3377843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377843 prefixEnd_3377843 := by exact prefixLift 3377843
  have htrace : WordTrace (prefixWord ++ tailWord_3377843) baseStart_3377843 baseEnd_3377843 := by
    simpa [prefixWord, tailWord_3377843, baseEnd_3377843] using wordTrace_append hprefix tailTrace_3377843
  have hstable : (prefixWord ++ tailWord_3377843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377843).length < 2 ^ (prefixWord ++ tailWord_3377843).sum := by decide
  have hdescent : baseEnd_3377843 < baseStart_3377843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377853 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_3377853 : Nat := 118140960795 + 3377853 * 2 ^ 59
def prefixEnd_3377853 : Nat := 4983230072969 + 3 ^ 40 * 3377853 * 2
def baseEnd_3377853 : Nat := 1734462169231677868303043

theorem tailTrace_3377853 : CollatzResearch.WordTrace tailWord_3377853 prefixEnd_3377853 1734462169231677868303043 := by
  unfold tailWord_3377853
  simp only [CollatzResearch.WordTrace]
  refine ⟨123200420231622947208842213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82133613487748631472561475 123200420231622947208842213)
  ·
    refine ⟨23100078793429302601657915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123200420231622947208842213 23100078793429302601657915)
    ·
      refine ⟨34650118190143953902486873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23100078793429302601657915 34650118190143953902486873)
      ·
        refine ⟨25987588642607965426865155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34650118190143953902486873 25987588642607965426865155)
        ·
          refine ⟨38981382963911948140297733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25987588642607965426865155 38981382963911948140297733)
          ·
            refine ⟨7309009305733490276305825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38981382963911948140297733 7309009305733490276305825)
            ·
              refine ⟨5481756979300117707229369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7309009305733490276305825 5481756979300117707229369)
              ·
                refine ⟨4111317734475088280422027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5481756979300117707229369 4111317734475088280422027)
                ·
                  refine ⟨6166976601712632420633041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111317734475088280422027 6166976601712632420633041)
                  ·
                    refine ⟨4625232451284474315474781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6166976601712632420633041 4625232451284474315474781)
                    ·
                      refine ⟨1734462169231677868303043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625232451284474315474781 1734462169231677868303043)
                      ·
                        rfl

theorem cell23_3377853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_3377853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377853 prefixEnd_3377853 := by exact prefixLift 3377853
  have htrace : WordTrace (prefixWord ++ tailWord_3377853) baseStart_3377853 baseEnd_3377853 := by
    simpa [prefixWord, tailWord_3377853, baseEnd_3377853] using wordTrace_append hprefix tailTrace_3377853
  have hstable : (prefixWord ++ tailWord_3377853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377853).length < 2 ^ (prefixWord ++ tailWord_3377853).sum := by decide
  have hdescent : baseEnd_3377853 < baseStart_3377853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377856 : List Nat := [2, 1, 1, 2, 4, 4, 2, 7]
def baseStart_3377856 : Nat := 118140960795 + 3377856 * 2 ^ 59
def prefixEnd_3377856 : Nat := 4983230072969 + 3 ^ 40 * 3377856 * 2
def baseEnd_3377856 : Nat := 64239396654579309502427

theorem tailTrace_3377856 : CollatzResearch.WordTrace tailWord_3377856 prefixEnd_3377856 64239396654579309502427 := by
  unfold tailWord_3377856
  simp only [CollatzResearch.WordTrace]
  refine ⟨61600264825306039360600711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82133686433741385814134281 61600264825306039360600711)
  ·
    refine ⟨92400397237959059040901067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61600264825306039360600711 92400397237959059040901067)
    ·
      refine ⟨138600595856938588561351601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92400397237959059040901067 138600595856938588561351601)
      ·
        refine ⟨103950446892703941421013701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138600595856938588561351601 103950446892703941421013701)
        ·
          refine ⟨19490708792381989016440069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103950446892703941421013701 19490708792381989016440069)
          ·
            refine ⟨3654507898571622940582513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19490708792381989016440069 3654507898571622940582513)
            ·
              refine ⟨2740880923928717205436885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3654507898571622940582513 2740880923928717205436885)
              ·
                refine ⟨64239396654579309502427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2740880923928717205436885 64239396654579309502427)
                ·
                  rfl

theorem cell23_3377856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 7].length) (baseStart_3377856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377856 prefixEnd_3377856 := by exact prefixLift 3377856
  have htrace : WordTrace (prefixWord ++ tailWord_3377856) baseStart_3377856 baseEnd_3377856 := by
    simpa [prefixWord, tailWord_3377856, baseEnd_3377856] using wordTrace_append hprefix tailTrace_3377856
  have hstable : (prefixWord ++ tailWord_3377856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377856).length < 2 ^ (prefixWord ++ tailWord_3377856).sum := by decide
  have hdescent : baseEnd_3377856 < baseStart_3377856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377919 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_3377919 : Nat := 118140960795 + 3377919 * 2 ^ 59
def prefixEnd_3377919 : Nat := 4983230072969 + 3 ^ 40 * 3377919 * 2
def baseEnd_3377919 : Nat := 1734496058954874610077739

theorem tailTrace_3377919 : CollatzResearch.WordTrace tailWord_3377919 prefixEnd_3377919 1734496058954874610077739 := by
  unfold tailWord_3377919
  simp only [CollatzResearch.WordTrace]
  refine ⟨123202827449383840480744811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82135218299589226987163207 123202827449383840480744811)
  ·
    refine ⟨184804241174075760721117217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123202827449383840480744811 184804241174075760721117217)
    ·
      refine ⟨138603180880556820540837913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184804241174075760721117217 138603180880556820540837913)
      ·
        refine ⟨103952385660417615405628435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138603180880556820540837913 103952385660417615405628435)
        ·
          refine ⟨155928578490626423108442653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103952385660417615405628435 155928578490626423108442653)
          ·
            refine ⟨58473216933984908665665995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155928578490626423108442653 58473216933984908665665995)
            ·
              refine ⟨87709825400977362998498993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58473216933984908665665995 87709825400977362998498993)
              ·
                refine ⟨65782369050733022248874245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87709825400977362998498993 65782369050733022248874245)
                ·
                  refine ⟨12334194197012441671663921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65782369050733022248874245 12334194197012441671663921)
                  ·
                    refine ⟨9250645647759331253747941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12334194197012441671663921 9250645647759331253747941)
                    ·
                      refine ⟨1734496058954874610077739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9250645647759331253747941 1734496058954874610077739)
                      ·
                        rfl

theorem cell23_3377919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_3377919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377919 prefixEnd_3377919 := by exact prefixLift 3377919
  have htrace : WordTrace (prefixWord ++ tailWord_3377919) baseStart_3377919 baseEnd_3377919 := by
    simpa [prefixWord, tailWord_3377919, baseEnd_3377919] using wordTrace_append hprefix tailTrace_3377919
  have hstable : (prefixWord ++ tailWord_3377919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377919).length < 2 ^ (prefixWord ++ tailWord_3377919).sum := by decide
  have hdescent : baseEnd_3377919 < baseStart_3377919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3377927 : List Nat := [1, 1, 4, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_3377927 : Nat := 118140960795 + 3377927 * 2 ^ 59
def prefixEnd_3377927 : Nat := 4983230072969 + 3 ^ 40 * 3377927 * 2
def baseEnd_3377927 : Nat := 1734500166800110578777703

theorem tailTrace_3377927 : CollatzResearch.WordTrace tailWord_3377927 prefixEnd_3377927 1734500166800110578777703 := by
  unfold tailWord_3377927
  simp only [CollatzResearch.WordTrace]
  refine ⟨123203119233354857847036035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82135412822236571898024023 123203119233354857847036035)
  ·
    refine ⟨184804678850032286770554053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123203119233354857847036035 184804678850032286770554053)
    ·
      refine ⟨34650877284381053769478885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184804678850032286770554053 34650877284381053769478885)
      ·
        refine ⟨6497039490821447581777291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34650877284381053769478885 6497039490821447581777291)
        ·
          refine ⟨9745559236232171372665937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497039490821447581777291 9745559236232171372665937)
          ·
            refine ⟨7309169427174128529499453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9745559236232171372665937 7309169427174128529499453)
            ·
              refine ⟨2740938535190298198562295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7309169427174128529499453 2740938535190298198562295)
              ·
                refine ⟨4111407802785447297843443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740938535190298198562295 4111407802785447297843443)
                ·
                  refine ⟨6167111704178170946765165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111407802785447297843443 6167111704178170946765165)
                  ·
                    refine ⟨2312666889066814105036937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6167111704178170946765165 2312666889066814105036937)
                    ·
                      refine ⟨1734500166800110578777703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312666889066814105036937 1734500166800110578777703)
                      ·
                        rfl

theorem cell23_3377927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_3377927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3377927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3377927 prefixEnd_3377927 := by exact prefixLift 3377927
  have htrace : WordTrace (prefixWord ++ tailWord_3377927) baseStart_3377927 baseEnd_3377927 := by
    simpa [prefixWord, tailWord_3377927, baseEnd_3377927] using wordTrace_append hprefix tailTrace_3377927
  have hstable : (prefixWord ++ tailWord_3377927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3377927).length < 2 ^ (prefixWord ++ tailWord_3377927).sum := by decide
  have hdescent : baseEnd_3377927 < baseStart_3377927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3377927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378016 : List Nat := [2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3]
def baseStart_3378016 : Nat := 118140960795 + 3378016 * 2 ^ 59
def prefixEnd_3378016 : Nat := 4983230072969 + 3 ^ 40 * 3378016 * 2
def baseEnd_3378016 : Nat := 1734545866578360730564793

theorem tailTrace_3378016 : CollatzResearch.WordTrace tailWord_3378016 prefixEnd_3378016 1734545866578360730564793 := by
  unfold tailWord_3378016
  simp only [CollatzResearch.WordTrace]
  refine ⟨61603182665016213023512951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82137576886688284031350601 61603182665016213023512951)
  ·
    refine ⟨92404773997524319535269427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61603182665016213023512951 92404773997524319535269427)
    ·
      refine ⟨138607160996286479302904141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92404773997524319535269427 138607160996286479302904141)
      ·
        refine ⟨51977685373607429738589053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138607160996286479302904141 51977685373607429738589053)
        ·
          refine ⟨19491632015102786151970895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51977685373607429738589053 19491632015102786151970895)
          ·
            refine ⟨29237448022654179227956343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19491632015102786151970895 29237448022654179227956343)
            ·
              refine ⟨43856172033981268841934515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29237448022654179227956343 43856172033981268841934515)
              ·
                refine ⟨65784258050971903262901773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43856172033981268841934515 65784258050971903262901773)
                ·
                  refine ⟨24669096769114463723588165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65784258050971903262901773 24669096769114463723588165)
                  ·
                    refine ⟨4625455644208961948172781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24669096769114463723588165 4625455644208961948172781)
                    ·
                      refine ⟨1734545866578360730564793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625455644208961948172781 1734545866578360730564793)
                      ·
                        rfl

theorem cell23_3378016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_3378016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378016 prefixEnd_3378016 := by exact prefixLift 3378016
  have htrace : WordTrace (prefixWord ++ tailWord_3378016) baseStart_3378016 baseEnd_3378016 := by
    simpa [prefixWord, tailWord_3378016, baseEnd_3378016] using wordTrace_append hprefix tailTrace_3378016
  have hstable : (prefixWord ++ tailWord_3378016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378016).length < 2 ^ (prefixWord ++ tailWord_3378016).sum := by decide
  have hdescent : baseEnd_3378016 < baseStart_3378016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378023 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3378023 : Nat := 118140960795 + 3378023 * 2 ^ 59
def prefixEnd_3378023 : Nat := 4983230072969 + 3 ^ 40 * 3378023 * 2
def baseEnd_3378023 : Nat := 578183153647647401059087

theorem tailTrace_3378023 : CollatzResearch.WordTrace tailWord_3378023 prefixEnd_3378023 578183153647647401059087 := by
  unfold tailWord_3378023
  simp only [CollatzResearch.WordTrace]
  refine ⟨123206620641007066242530723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82137747094004710828353815 123206620641007066242530723)
  ·
    refine ⟨184809930961510599363796085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123206620641007066242530723 184809930961510599363796085)
    ·
      refine ⟨17325931027641618690355883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184809930961510599363796085 17325931027641618690355883)
      ·
        refine ⟨25988896541462428035533825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17325931027641618690355883 25988896541462428035533825)
        ·
          refine ⟨19491672406096821026650369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25988896541462428035533825 19491672406096821026650369)
          ·
            refine ⟨14618754304572615769987777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19491672406096821026650369 14618754304572615769987777)
            ·
              refine ⟨10964065728429461827490833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14618754304572615769987777 10964065728429461827490833)
              ·
                refine ⟨8223049296322096370618125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10964065728429461827490833 8223049296322096370618125)
                ·
                  refine ⟨3083643486120786138981797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8223049296322096370618125 3083643486120786138981797)
                  ·
                    refine ⟨578183153647647401059087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083643486120786138981797 578183153647647401059087)
                    ·
                      rfl

theorem cell23_3378023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3378023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378023 prefixEnd_3378023 := by exact prefixLift 3378023
  have htrace : WordTrace (prefixWord ++ tailWord_3378023) baseStart_3378023 baseEnd_3378023 := by
    simpa [prefixWord, tailWord_3378023, baseEnd_3378023] using wordTrace_append hprefix tailTrace_3378023
  have hstable : (prefixWord ++ tailWord_3378023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378023).length < 2 ^ (prefixWord ++ tailWord_3378023).sum := by decide
  have hdescent : baseEnd_3378023 < baseStart_3378023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378057 : List Nat := [1, 2, 1, 1, 5, 3, 3, 2, 1, 4]
def baseStart_3378057 : Nat := 118140960795 + 3378057 * 2 ^ 59
def prefixEnd_3378057 : Nat := 4983230072969 + 3 ^ 40 * 3378057 * 2
def baseEnd_3378057 : Nat := 578188973095065023384035

theorem tailTrace_3378057 : CollatzResearch.WordTrace tailWord_3378057 prefixEnd_3378057 578188973095065023384035 := by
  unfold tailWord_3378057
  simp only [CollatzResearch.WordTrace]
  refine ⟨123207860722883890049268425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82138573815255926699512283 123207860722883890049268425)
  ·
    refine ⟨92405895542162917536951319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123207860722883890049268425 92405895542162917536951319)
    ·
      refine ⟨138608843313244376305426979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92405895542162917536951319 138608843313244376305426979)
      ·
        refine ⟨207913264969866564458140469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138608843313244376305426979 207913264969866564458140469)
        ·
          refine ⟨19491868590924990417950669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207913264969866564458140469 19491868590924990417950669)
          ·
            refine ⟨7309450721596871406731501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19491868590924990417950669 7309450721596871406731501)
            ·
              refine ⟨2741044020598826777524313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7309450721596871406731501 2741044020598826777524313)
              ·
                refine ⟨2055783015449120083143235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2741044020598826777524313 2055783015449120083143235)
                ·
                  refine ⟨3083674523173680124714853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055783015449120083143235 3083674523173680124714853)
                  ·
                    refine ⟨578188973095065023384035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3083674523173680124714853 578188973095065023384035)
                    ·
                      rfl

theorem cell23_3378057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 1, 4].length) (baseStart_3378057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378057 prefixEnd_3378057 := by exact prefixLift 3378057
  have htrace : WordTrace (prefixWord ++ tailWord_3378057) baseStart_3378057 baseEnd_3378057 := by
    simpa [prefixWord, tailWord_3378057, baseEnd_3378057] using wordTrace_append hprefix tailTrace_3378057
  have hstable : (prefixWord ++ tailWord_3378057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378057).length < 2 ^ (prefixWord ++ tailWord_3378057).sum := by decide
  have hdescent : baseEnd_3378057 < baseStart_3378057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378073 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 6, 3, 2]
def baseStart_3378073 : Nat := 118140960795 + 3378073 * 2 ^ 59
def prefixEnd_3378073 : Nat := 4983230072969 + 3 ^ 40 * 3378073 * 2
def baseEnd_3378073 : Nat := 1734575134975667007552031

theorem tailTrace_3378073 : CollatzResearch.WordTrace tailWord_3378073 prefixEnd_3378073 1734575134975667007552031 := by
  unfold tailWord_3378073
  simp only [CollatzResearch.WordTrace]
  refine ⟨123208444290825924781850873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82138962860550616521233915 123208444290825924781850873)
  ·
    refine ⟨92406333218119443586388155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123208444290825924781850873 92406333218119443586388155)
    ·
      refine ⟨138609499827179165379582233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92406333218119443586388155 138609499827179165379582233)
      ·
        refine ⟨103957124870384374034686675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138609499827179165379582233 103957124870384374034686675)
        ·
          refine ⟨155935687305576561052030013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103957124870384374034686675 155935687305576561052030013)
          ·
            refine ⟨58475882739591210394511255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155935687305576561052030013 58475882739591210394511255)
            ·
              refine ⟨87713824109386815591766883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58475882739591210394511255 87713824109386815591766883)
              ·
                refine ⟨131570736164080223387650325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87713824109386815591766883 131570736164080223387650325)
                ·
                  refine ⟨6167378257691260471296109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131570736164080223387650325 6167378257691260471296109)
                  ·
                    refine ⟨2312766846634222676736041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6167378257691260471296109 2312766846634222676736041)
                    ·
                      refine ⟨1734575134975667007552031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312766846634222676736041 1734575134975667007552031)
                      ·
                        rfl

theorem cell23_3378073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_3378073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378073 prefixEnd_3378073 := by exact prefixLift 3378073
  have htrace : WordTrace (prefixWord ++ tailWord_3378073) baseStart_3378073 baseEnd_3378073 := by
    simpa [prefixWord, tailWord_3378073, baseEnd_3378073] using wordTrace_append hprefix tailTrace_3378073
  have hstable : (prefixWord ++ tailWord_3378073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378073).length < 2 ^ (prefixWord ++ tailWord_3378073).sum := by decide
  have hdescent : baseEnd_3378073 < baseStart_3378073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378083 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 1, 5]
def baseStart_3378083 : Nat := 118140960795 + 3378083 * 2 ^ 59
def prefixEnd_3378083 : Nat := 4983230072969 + 3 ^ 40 * 3378083 * 2
def baseEnd_3378083 : Nat := 578193423260737322808995

theorem tailTrace_3378083 : CollatzResearch.WordTrace tailWord_3378083 prefixEnd_3378083 578193423260737322808995 := by
  unfold tailWord_3378083
  simp only [CollatzResearch.WordTrace]
  refine ⟨123208809020789696489714903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82139206013859797659809935 123208809020789696489714903)
  ·
    refine ⟨184813213531184544734572355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123208809020789696489714903 184813213531184544734572355)
    ·
      refine ⟨277219820296776817101858533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184813213531184544734572355 277219820296776817101858533)
      ·
        refine ⟨51978716305645653206598475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277219820296776817101858533 51978716305645653206598475)
        ·
          refine ⟨77968074458468479809897713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51978716305645653206598475 77968074458468479809897713)
          ·
            refine ⟨58476055843851359857423285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77968074458468479809897713 58476055843851359857423285)
            ·
              refine ⟨5482130235361064986633433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58476055843851359857423285 5482130235361064986633433)
              ·
                refine ⟨4111597676520798739975075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5482130235361064986633433 4111597676520798739975075)
                ·
                  refine ⟨6167396514781198109962613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111597676520798739975075 6167396514781198109962613)
                  ·
                    refine ⟨578193423260737322808995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6167396514781198109962613 578193423260737322808995)
                    ·
                      rfl

theorem cell23_3378083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 1, 5].length) (baseStart_3378083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378083 prefixEnd_3378083 := by exact prefixLift 3378083
  have htrace : WordTrace (prefixWord ++ tailWord_3378083) baseStart_3378083 baseEnd_3378083 := by
    simpa [prefixWord, tailWord_3378083, baseEnd_3378083] using wordTrace_append hprefix tailTrace_3378083
  have hstable : (prefixWord ++ tailWord_3378083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378083).length < 2 ^ (prefixWord ++ tailWord_3378083).sum := by decide
  have hdescent : baseEnd_3378083 < baseStart_3378083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378103 : List Nat := [1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_3378103 : Nat := 118140960795 + 3378103 * 2 ^ 59
def prefixEnd_3378103 : Nat := 4983230072969 + 3 ^ 40 * 3378103 * 2
def baseEnd_3378103 : Nat := 1734590539395301890176893

theorem tailTrace_3378103 : CollatzResearch.WordTrace tailWord_3378103 prefixEnd_3378103 1734590539395301890176893 := by
  unfold tailWord_3378103
  simp only [CollatzResearch.WordTrace]
  refine ⟨123209538480717239905442963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82139692320478159936961975 123209538480717239905442963)
  ·
    refine ⟨184814307721075859858164445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123209538480717239905442963 184814307721075859858164445)
    ·
      refine ⟨69305365395403447446811667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184814307721075859858164445 69305365395403447446811667)
      ·
        refine ⟨103958048093105171170217501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69305365395403447446811667 103958048093105171170217501)
        ·
          refine ⟨38984268034914439188831563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103958048093105171170217501 38984268034914439188831563)
          ·
            refine ⟨58476402052371658783247345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38984268034914439188831563 58476402052371658783247345)
            ·
              refine ⟨43857301539278744087435509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58476402052371658783247345 43857301539278744087435509)
              ·
                refine ⟨4111622019307382258197079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43857301539278744087435509 4111622019307382258197079)
                ·
                  refine ⟨6167433028961073387295619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111622019307382258197079 6167433028961073387295619)
                  ·
                    refine ⟨9251149543441610080943429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6167433028961073387295619 9251149543441610080943429)
                    ·
                      refine ⟨1734590539395301890176893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9251149543441610080943429 1734590539395301890176893)
                      ·
                        rfl

theorem cell23_3378103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_3378103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378103 prefixEnd_3378103 := by exact prefixLift 3378103
  have htrace : WordTrace (prefixWord ++ tailWord_3378103) baseStart_3378103 baseEnd_3378103 := by
    simpa [prefixWord, tailWord_3378103, baseEnd_3378103] using wordTrace_append hprefix tailTrace_3378103
  have hstable : (prefixWord ++ tailWord_3378103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378103).length < 2 ^ (prefixWord ++ tailWord_3378103).sum := by decide
  have hdescent : baseEnd_3378103 < baseStart_3378103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378123 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 3]
def baseStart_3378123 : Nat := 118140960795 + 3378123 * 2 ^ 59
def prefixEnd_3378123 : Nat := 4983230072969 + 3 ^ 40 * 3378123 * 2
def baseEnd_3378123 : Nat := 1734600809008391811926801

theorem tailTrace_3378123 : CollatzResearch.WordTrace tailWord_3378123 prefixEnd_3378123 1734600809008391811926801 := by
  unfold tailWord_3378123
  simp only [CollatzResearch.WordTrace]
  refine ⟨123210267940644783321171023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82140178627096522214114015 123210267940644783321171023)
  ·
    refine ⟨184815401910967174981756535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123210267940644783321171023 184815401910967174981756535)
    ·
      refine ⟨277223102866450762472634803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184815401910967174981756535 277223102866450762472634803)
      ·
        refine ⟨415834654299676143708952205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277223102866450762472634803 415834654299676143708952205)
        ·
          refine ⟨155937995362378553890857077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415834654299676143708952205 155937995362378553890857077)
          ·
            refine ⟨14619187065222989427267851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155937995362378553890857077 14619187065222989427267851)
            ·
              refine ⟨21928780597834484140901777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619187065222989427267851 21928780597834484140901777)
              ·
                refine ⟨16446585448375863105676333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21928780597834484140901777 16446585448375863105676333)
                ·
                  refine ⟨6167469543140948664628625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16446585448375863105676333 6167469543140948664628625)
                  ·
                    refine ⟨4625602157355711498471469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6167469543140948664628625 4625602157355711498471469)
                    ·
                      refine ⟨1734600809008391811926801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625602157355711498471469 1734600809008391811926801)
                      ·
                        rfl

theorem cell23_3378123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 3, 2, 3].length) (baseStart_3378123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378123 prefixEnd_3378123 := by exact prefixLift 3378123
  have htrace : WordTrace (prefixWord ++ tailWord_3378123) baseStart_3378123 baseEnd_3378123 := by
    simpa [prefixWord, tailWord_3378123, baseEnd_3378123] using wordTrace_append hprefix tailTrace_3378123
  have hstable : (prefixWord ++ tailWord_3378123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378123).length < 2 ^ (prefixWord ++ tailWord_3378123).sum := by decide
  have hdescent : baseEnd_3378123 < baseStart_3378123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378130 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 1, 6]
def baseStart_3378130 : Nat := 118140960795 + 3378130 * 2 ^ 59
def prefixEnd_3378130 : Nat := 4983230072969 + 3 ^ 40 * 3378130 * 2
def baseEnd_3378130 : Nat := 578201467790991094846423

theorem tailTrace_3378130 : CollatzResearch.WordTrace tailWord_3378130 prefixEnd_3378130 578201467790991094846423 := by
  unfold tailWord_3378130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30802630812904855879168961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82140348834412949011117229 30802630812904855879168961)
  ·
    refine ⟨23101973109678641909376721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30802630812904855879168961 23101973109678641909376721)
    ·
      refine ⟨17326479832258981432032541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23101973109678641909376721 17326479832258981432032541)
      ·
        refine ⟨6497429937097118037012203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17326479832258981432032541 6497429937097118037012203)
        ·
          refine ⟨9746144905645677055518305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497429937097118037012203 9746144905645677055518305)
          ·
            refine ⟨7309608679234257791638729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746144905645677055518305 7309608679234257791638729)
            ·
              refine ⟨5482206509425693343729047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7309608679234257791638729 5482206509425693343729047)
              ·
                refine ⟨8223309764138540015593571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482206509425693343729047 8223309764138540015593571)
                ·
                  refine ⟨12334964646207810023390357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8223309764138540015593571 12334964646207810023390357)
                  ·
                    refine ⟨578201467790991094846423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12334964646207810023390357 578201467790991094846423)
                    ·
                      rfl

theorem cell23_3378130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_3378130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378130 prefixEnd_3378130 := by exact prefixLift 3378130
  have htrace : WordTrace (prefixWord ++ tailWord_3378130) baseStart_3378130 baseEnd_3378130 := by
    simpa [prefixWord, tailWord_3378130, baseEnd_3378130] using wordTrace_append hprefix tailTrace_3378130
  have hstable : (prefixWord ++ tailWord_3378130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378130).length < 2 ^ (prefixWord ++ tailWord_3378130).sum := by decide
  have hdescent : baseEnd_3378130 < baseStart_3378130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378137 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 3, 2, 2]
def baseStart_3378137 : Nat := 118140960795 + 3378137 * 2 ^ 59
def prefixEnd_3378137 : Nat := 4983230072969 + 3 ^ 40 * 3378137 * 2
def baseEnd_3378137 : Nat := 1734607997737554757151737

theorem tailTrace_3378137 : CollatzResearch.WordTrace tailWord_3378137 prefixEnd_3378137 1734607997737554757151737 := by
  unfold tailWord_3378137
  simp only [CollatzResearch.WordTrace]
  refine ⟨123210778562594063712180665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82140519041729375808120443 123210778562594063712180665)
  ·
    refine ⟨92408083921945547784135499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123210778562594063712180665 92408083921945547784135499)
    ·
      refine ⟨138612125882918321676203249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92408083921945547784135499 138612125882918321676203249)
      ·
        refine ⟨103959094412188741257152437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138612125882918321676203249 103959094412188741257152437)
        ·
          refine ⟨9746165101142694492858041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103959094412188741257152437 9746165101142694492858041)
          ·
            refine ⟨7309623825857020869643531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746165101142694492858041 7309623825857020869643531)
            ·
              refine ⟨10964435738785531304465297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309623825857020869643531 10964435738785531304465297)
              ·
                refine ⟨8223326804089148478348973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10964435738785531304465297 8223326804089148478348973)
                ·
                  refine ⟨3083747551533430679380865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8223326804089148478348973 3083747551533430679380865)
                  ·
                    refine ⟨2312810663650073009535649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083747551533430679380865 2312810663650073009535649)
                    ·
                      refine ⟨1734607997737554757151737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312810663650073009535649 1734607997737554757151737)
                      ·
                        rfl

theorem cell23_3378137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_3378137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378137 prefixEnd_3378137 := by exact prefixLift 3378137
  have htrace : WordTrace (prefixWord ++ tailWord_3378137) baseStart_3378137 baseEnd_3378137 := by
    simpa [prefixWord, tailWord_3378137, baseEnd_3378137] using wordTrace_append hprefix tailTrace_3378137
  have hstable : (prefixWord ++ tailWord_3378137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378137).length < 2 ^ (prefixWord ++ tailWord_3378137).sum := by decide
  have hdescent : baseEnd_3378137 < baseStart_3378137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378154 : List Nat := [3, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_3378154 : Nat := 118140960795 + 3378154 * 2 ^ 59
def prefixEnd_3378154 : Nat := 4983230072969 + 3 ^ 40 * 3378154 * 2
def baseEnd_3378154 : Nat := 1734616726908681190639159

theorem tailTrace_3378154 : CollatzResearch.WordTrace tailWord_3378154 prefixEnd_3378154 1734616726908681190639159 := by
  unfold tailWord_3378154
  simp only [CollatzResearch.WordTrace]
  refine ⟨30802849650883118903887379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82140932402354983743699677 30802849650883118903887379)
  ·
    refine ⟨46204274476324678355831069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30802849650883118903887379 46204274476324678355831069)
    ·
      refine ⟨17326602928621754383436651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46204274476324678355831069 17326602928621754383436651)
      ·
        refine ⟨25989904392932631575154977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17326602928621754383436651 25989904392932631575154977)
        ·
          refine ⟨19492428294699473681366233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25989904392932631575154977 19492428294699473681366233)
          ·
            refine ⟨14619321221024605261024675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19492428294699473681366233 14619321221024605261024675)
            ·
              refine ⟨21928981831536907891537013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619321221024605261024675 21928981831536907891537013)
              ·
                refine ⟨2055842046706585114831595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21928981831536907891537013 2055842046706585114831595)
                ·
                  refine ⟨3083763070059877672247393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055842046706585114831595 3083763070059877672247393)
                  ·
                    refine ⟨2312822302544908254185545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083763070059877672247393 2312822302544908254185545)
                    ·
                      refine ⟨1734616726908681190639159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312822302544908254185545 1734616726908681190639159)
                      ·
                        rfl

theorem cell23_3378154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_3378154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378154 prefixEnd_3378154 := by exact prefixLift 3378154
  have htrace : WordTrace (prefixWord ++ tailWord_3378154) baseStart_3378154 baseEnd_3378154 := by
    simpa [prefixWord, tailWord_3378154, baseEnd_3378154] using wordTrace_append hprefix tailTrace_3378154
  have hstable : (prefixWord ++ tailWord_3378154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378154).length < 2 ^ (prefixWord ++ tailWord_3378154).sum := by decide
  have hdescent : baseEnd_3378154 < baseStart_3378154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378197 : List Nat := [1, 3, 2, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_3378197 : Nat := 118140960795 + 3378197 * 2 ^ 59
def prefixEnd_3378197 : Nat := 4983230072969 + 3 ^ 40 * 3378197 * 2
def baseEnd_3378197 : Nat := 1734638806576824522401461

theorem tailTrace_3378197 : CollatzResearch.WordTrace tailWord_3378197 prefixEnd_3378197 1734638806576824522401461 := by
  unfold tailWord_3378197
  simp only [CollatzResearch.WordTrace]
  refine ⟨123212966942376693959364845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82141977961584462639576563 123212966942376693959364845)
  ·
    refine ⟨46204862603391260234761817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123212966942376693959364845 46204862603391260234761817)
    ·
      refine ⟨34653646952543445176071363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46204862603391260234761817 34653646952543445176071363)
      ·
        refine ⟨51980470428815167764107045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34653646952543445176071363 51980470428815167764107045)
        ·
          refine ⟨9746338205402843955770071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51980470428815167764107045 9746338205402843955770071)
          ·
            refine ⟨14619507308104265933655107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746338205402843955770071 14619507308104265933655107)
            ·
              refine ⟨21929260962156398900482661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14619507308104265933655107 21929260962156398900482661)
              ·
                refine ⟨4111736430404324793840499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21929260962156398900482661 4111736430404324793840499)
                ·
                  refine ⟨6167604645606487190760749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4111736430404324793840499 6167604645606487190760749)
                  ·
                    refine ⟨2312851742102432696535281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6167604645606487190760749 2312851742102432696535281)
                    ·
                      refine ⟨1734638806576824522401461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312851742102432696535281 1734638806576824522401461)
                      ·
                        rfl

theorem cell23_3378197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_3378197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378197 prefixEnd_3378197 := by exact prefixLift 3378197
  have htrace : WordTrace (prefixWord ++ tailWord_3378197) baseStart_3378197 baseEnd_3378197 := by
    simpa [prefixWord, tailWord_3378197, baseEnd_3378197] using wordTrace_append hprefix tailTrace_3378197
  have hstable : (prefixWord ++ tailWord_3378197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378197).length < 2 ^ (prefixWord ++ tailWord_3378197).sum := by decide
  have hdescent : baseEnd_3378197 < baseStart_3378197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378213 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3378213 : Nat := 118140960795 + 3378213 * 2 ^ 59
def prefixEnd_3378213 : Nat := 4983230072969 + 3 ^ 40 * 3378213 * 2
def baseEnd_3378213 : Nat := 1734647022267296459801387

theorem tailTrace_3378213 : CollatzResearch.WordTrace tailWord_3378213 prefixEnd_3378213 1734647022267296459801387 := by
  unfold tailWord_3378213
  simp only [CollatzResearch.WordTrace]
  refine ⟨123213550510318728691947293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82142367006879152461298195 123213550510318728691947293)
  ·
    refine ⟨46205081441369523259480235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123213550510318728691947293 46205081441369523259480235)
    ·
      refine ⟨69307622162054284889220353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46205081441369523259480235 69307622162054284889220353)
      ·
        refine ⟨51980716621540713666915265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69307622162054284889220353 51980716621540713666915265)
        ·
          refine ⟨38985537466155535250186449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51980716621540713666915265 38985537466155535250186449)
          ·
            refine ⟨29239153099616651437639837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38985537466155535250186449 29239153099616651437639837)
            ·
              refine ⟨10964682412356244289114939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29239153099616651437639837 10964682412356244289114939)
              ·
                refine ⟨16447023618534366433672409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10964682412356244289114939 16447023618534366433672409)
                ·
                  refine ⟨12335267713900774825254307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16447023618534366433672409 12335267713900774825254307)
                  ·
                    refine ⟨18502901570851162237881461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12335267713900774825254307 18502901570851162237881461)
                    ·
                      refine ⟨1734647022267296459801387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18502901570851162237881461 1734647022267296459801387)
                      ·
                        rfl

theorem cell23_3378213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3378213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378213 prefixEnd_3378213 := by exact prefixLift 3378213
  have htrace : WordTrace (prefixWord ++ tailWord_3378213) baseStart_3378213 baseEnd_3378213 := by
    simpa [prefixWord, tailWord_3378213, baseEnd_3378213] using wordTrace_append hprefix tailTrace_3378213
  have hstable : (prefixWord ++ tailWord_3378213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378213).length < 2 ^ (prefixWord ++ tailWord_3378213).sum := by decide
  have hdescent : baseEnd_3378213 < baseStart_3378213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378227 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 2, 2, 2]
def baseStart_3378227 : Nat := 118140960795 + 3378227 * 2 ^ 59
def prefixEnd_3378227 : Nat := 4983230072969 + 3 ^ 40 * 3378227 * 2
def baseEnd_3378227 : Nat := 1734654210996459405026323

theorem tailTrace_3378227 : CollatzResearch.WordTrace tailWord_3378227 prefixEnd_3378227 1734654210996459405026323 := by
  unfold tailWord_3378227
  simp only [CollatzResearch.WordTrace]
  refine ⟨123214061132268009082956935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82142707421512006055304623 123214061132268009082956935)
  ·
    refine ⟨184821091698402013624435403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123214061132268009082956935 184821091698402013624435403)
    ·
      refine ⟨277231637547603020436653105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184821091698402013624435403 277231637547603020436653105)
      ·
        refine ⟨207923728160702265327489829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277231637547603020436653105 207923728160702265327489829)
        ·
          refine ⟨38985699030131674748904343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207923728160702265327489829 38985699030131674748904343)
          ·
            refine ⟨58478548545197512123356515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38985699030131674748904343 58478548545197512123356515)
            ·
              refine ⟨87717822817796268185034773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58478548545197512123356515 87717822817796268185034773)
              ·
                refine ⟨4111772944584200071173505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87717822817796268185034773 4111772944584200071173505)
                ·
                  refine ⟨3083829708438150053380129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4111772944584200071173505 3083829708438150053380129)
                  ·
                    refine ⟨2312872281328612540035097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083829708438150053380129 2312872281328612540035097)
                    ·
                      refine ⟨1734654210996459405026323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312872281328612540035097 1734654210996459405026323)
                      ·
                        rfl

theorem cell23_3378227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 2, 2, 2].length) (baseStart_3378227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378227 prefixEnd_3378227 := by exact prefixLift 3378227
  have htrace : WordTrace (prefixWord ++ tailWord_3378227) baseStart_3378227 baseEnd_3378227 := by
    simpa [prefixWord, tailWord_3378227, baseEnd_3378227] using wordTrace_append hprefix tailTrace_3378227
  have hstable : (prefixWord ++ tailWord_3378227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378227).length < 2 ^ (prefixWord ++ tailWord_3378227).sum := by decide
  have hdescent : baseEnd_3378227 < baseStart_3378227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378243 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 3]
def baseStart_3378243 : Nat := 118140960795 + 3378243 * 2 ^ 59
def prefixEnd_3378243 : Nat := 4983230072969 + 3 ^ 40 * 3378243 * 2
def baseEnd_3378243 : Nat := 1734662426686931342426249

theorem tailTrace_3378243 : CollatzResearch.WordTrace tailWord_3378243 prefixEnd_3378243 1734662426686931342426249 := by
  unfold tailWord_3378243
  simp only [CollatzResearch.WordTrace]
  refine ⟨123214644700210043815539383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82143096466806695877026255 123214644700210043815539383)
  ·
    refine ⟨184821967050315065723309075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123214644700210043815539383 184821967050315065723309075)
    ·
      refine ⟨277232950575472598584963613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184821967050315065723309075 277232950575472598584963613)
      ·
        refine ⟨103962356465802224469361355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277232950575472598584963613 103962356465802224469361355)
        ·
          refine ⟨155943534698703336704042033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103962356465802224469361355 155943534698703336704042033)
          ·
            refine ⟨116957651024027502528031525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155943534698703336704042033 116957651024027502528031525)
            ·
              refine ⟨21929559567005156724005911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116957651024027502528031525 21929559567005156724005911)
              ·
                refine ⟨32894339350507735086008867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21929559567005156724005911 32894339350507735086008867)
                ·
                  refine ⟨49341509025761602629013301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32894339350507735086008867 49341509025761602629013301)
                  ·
                    refine ⟨4625766471165150246469997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49341509025761602629013301 4625766471165150246469997)
                    ·
                      refine ⟨1734662426686931342426249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625766471165150246469997 1734662426686931342426249)
                      ·
                        rfl

theorem cell23_3378243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_3378243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378243 prefixEnd_3378243 := by exact prefixLift 3378243
  have htrace : WordTrace (prefixWord ++ tailWord_3378243) baseStart_3378243 baseEnd_3378243 := by
    simpa [prefixWord, tailWord_3378243, baseEnd_3378243] using wordTrace_append hprefix tailTrace_3378243
  have hstable : (prefixWord ++ tailWord_3378243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378243).length < 2 ^ (prefixWord ++ tailWord_3378243).sum := by decide
  have hdescent : baseEnd_3378243 < baseStart_3378243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378273 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_3378273 : Nat := 118140960795 + 3378273 * 2 ^ 59
def prefixEnd_3378273 : Nat := 4983230072969 + 3 ^ 40 * 3378273 * 2
def baseEnd_3378273 : Nat := 1734677831106566225051111

theorem tailTrace_3378273 : CollatzResearch.WordTrace tailWord_3378273 prefixEnd_3378273 1734677831106566225051111 := by
  unfold tailWord_3378273
  simp only [CollatzResearch.WordTrace]
  refine ⟨123215738890101358939131473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82143825926734239292754315 123215738890101358939131473)
  ·
    refine ⟨92411804167576019204348605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123215738890101358939131473 92411804167576019204348605)
    ·
      refine ⟨34654426562841007201630727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92411804167576019204348605 34654426562841007201630727)
      ·
        refine ⟨51981639844261510802446091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34654426562841007201630727 51981639844261510802446091)
        ·
          refine ⟨77972459766392266203669137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51981639844261510802446091 77972459766392266203669137)
          ·
            refine ⟨58479344824794199652751853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77972459766392266203669137 58479344824794199652751853)
            ·
              refine ⟨21929754309297824869781945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58479344824794199652751853 21929754309297824869781945)
              ·
                refine ⟨16447315731973368652336459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21929754309297824869781945 16447315731973368652336459)
                ·
                  refine ⟨24670973597960052978504689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16447315731973368652336459 24670973597960052978504689)
                  ·
                    refine ⟨18503230198470039733878517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24670973597960052978504689 18503230198470039733878517)
                    ·
                      refine ⟨1734677831106566225051111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18503230198470039733878517 1734677831106566225051111)
                      ·
                        rfl

theorem cell23_3378273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_3378273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378273 prefixEnd_3378273 := by exact prefixLift 3378273
  have htrace : WordTrace (prefixWord ++ tailWord_3378273) baseStart_3378273 baseEnd_3378273 := by
    simpa [prefixWord, tailWord_3378273, baseEnd_3378273] using wordTrace_append hprefix tailTrace_3378273
  have hstable : (prefixWord ++ tailWord_3378273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378273).length < 2 ^ (prefixWord ++ tailWord_3378273).sum := by decide
  have hdescent : baseEnd_3378273 < baseStart_3378273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378320 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3]
def baseStart_3378320 : Nat := 118140960795 + 3378320 * 2 ^ 59
def prefixEnd_3378320 : Nat := 4983230072969 + 3 ^ 40 * 3378320 * 2
def baseEnd_3378320 : Nat := 1734701964697327541163395

theorem tailTrace_3378320 : CollatzResearch.WordTrace tailWord_3378320 prefixEnd_3378320 1734701964697327541163395 := by
  unfold tailWord_3378320
  simp only [CollatzResearch.WordTrace]
  refine ⟨61608726560465542983046207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82144968747287390644061609 61608726560465542983046207)
  ·
    refine ⟨92413089840698314474569311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61608726560465542983046207 92413089840698314474569311)
    ·
      refine ⟨138619634761047471711853967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92413089840698314474569311 138619634761047471711853967)
      ·
        refine ⟨207929452141571207567780951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138619634761047471711853967 207929452141571207567780951)
        ·
          refine ⟨311894178212356811351671427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207929452141571207567780951 311894178212356811351671427)
          ·
            refine ⟨467841267318535217027507141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311894178212356811351671427 467841267318535217027507141)
            ·
              refine ⟨87720237622225353192657589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 467841267318535217027507141 87720237622225353192657589)
              ·
                refine ⟨8223772277083626861811649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87720237622225353192657589 8223772277083626861811649)
                ·
                  refine ⟨6167829207812720146358737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8223772277083626861811649 6167829207812720146358737)
                  ·
                    refine ⟨4625871905859540109769053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6167829207812720146358737 4625871905859540109769053)
                    ·
                      refine ⟨1734701964697327541163395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625871905859540109769053 1734701964697327541163395)
                      ·
                        rfl

theorem cell23_3378320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 2, 2, 3].length) (baseStart_3378320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378320 prefixEnd_3378320 := by exact prefixLift 3378320
  have htrace : WordTrace (prefixWord ++ tailWord_3378320) baseStart_3378320 baseEnd_3378320 := by
    simpa [prefixWord, tailWord_3378320, baseEnd_3378320] using wordTrace_append hprefix tailTrace_3378320
  have hstable : (prefixWord ++ tailWord_3378320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378320).length < 2 ^ (prefixWord ++ tailWord_3378320).sum := by decide
  have hdescent : baseEnd_3378320 < baseStart_3378320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378330 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3378330 : Nat := 118140960795 + 3378330 * 2 ^ 59
def prefixEnd_3378330 : Nat := 4983230072969 + 3 ^ 40 * 3378330 * 2
def baseEnd_3378330 : Nat := 1734707099503872502038349

theorem tailTrace_3378330 : CollatzResearch.WordTrace tailWord_3378330 prefixEnd_3378330 1734707099503872502038349 := by
  unfold tailWord_3378330
  simp only [CollatzResearch.WordTrace]
  refine ⟨30804454462723714418489111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82145211900596571782637629 30804454462723714418489111)
  ·
    refine ⟨46206681694085571627733667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30804454462723714418489111 46206681694085571627733667)
    ·
      refine ⟨69310022541128357441600501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46206681694085571627733667 69310022541128357441600501)
      ·
        refine ⟨6497814613230783510150047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69310022541128357441600501 6497814613230783510150047)
        ·
          refine ⟨9746721919846175265225071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497814613230783510150047 9746721919846175265225071)
          ·
            refine ⟨14620082879769262897837607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746721919846175265225071 14620082879769262897837607)
            ·
              refine ⟨21930124319653894346756411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14620082879769262897837607 21930124319653894346756411)
              ·
                refine ⟨32895186479480841520134617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21930124319653894346756411 32895186479480841520134617)
                ·
                  refine ⟨24671389859610631140100963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32895186479480841520134617 24671389859610631140100963)
                  ·
                    refine ⟨37007084789415946710151445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24671389859610631140100963 37007084789415946710151445)
                    ·
                      refine ⟨1734707099503872502038349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37007084789415946710151445 1734707099503872502038349)
                      ·
                        rfl

theorem cell23_3378330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3378330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378330 prefixEnd_3378330 := by exact prefixLift 3378330
  have htrace : WordTrace (prefixWord ++ tailWord_3378330) baseStart_3378330 baseEnd_3378330 := by
    simpa [prefixWord, tailWord_3378330, baseEnd_3378330] using wordTrace_append hprefix tailTrace_3378330
  have hstable : (prefixWord ++ tailWord_3378330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378330).length < 2 ^ (prefixWord ++ tailWord_3378330).sum := by decide
  have hdescent : baseEnd_3378330 < baseStart_3378330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378334 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 2, 4, 2]
def baseStart_3378334 : Nat := 118140960795 + 3378334 * 2 ^ 59
def prefixEnd_3378334 : Nat := 4983230072969 + 3 ^ 40 * 3378334 * 2
def baseEnd_3378334 : Nat := 1734709153426490486388331

theorem tailTrace_3378334 : CollatzResearch.WordTrace tailWord_3378334 prefixEnd_3378334 1734709153426490486388331 := by
  unfold tailWord_3378334
  simp only [CollatzResearch.WordTrace]
  refine ⟨15402245467860045794637757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82145309161920244238068037 15402245467860045794637757)
  ·
    refine ⟨5775842050447517172989159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15402245467860045794637757 5775842050447517172989159)
    ·
      refine ⟨8663763075671275759483739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5775842050447517172989159 8663763075671275759483739)
      ·
        refine ⟨12995644613506913639225609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8663763075671275759483739 12995644613506913639225609)
        ·
          refine ⟨9746733460130185229419207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12995644613506913639225609 9746733460130185229419207)
          ·
            refine ⟨14620100190195277844128811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9746733460130185229419207 14620100190195277844128811)
            ·
              refine ⟨21930150285292916766193217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14620100190195277844128811 21930150285292916766193217)
              ·
                refine ⟨16447612713969687574644913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21930150285292916766193217 16447612713969687574644913)
                ·
                  refine ⟨12335709535477265680983685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16447612713969687574644913 12335709535477265680983685)
                  ·
                    refine ⟨2312945537901987315184441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12335709535477265680983685 2312945537901987315184441)
                    ·
                      refine ⟨1734709153426490486388331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2312945537901987315184441 1734709153426490486388331)
                      ·
                        rfl

theorem cell23_3378334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_3378334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378334 prefixEnd_3378334 := by exact prefixLift 3378334
  have htrace : WordTrace (prefixWord ++ tailWord_3378334) baseStart_3378334 baseEnd_3378334 := by
    simpa [prefixWord, tailWord_3378334, baseEnd_3378334] using wordTrace_append hprefix tailTrace_3378334
  have hstable : (prefixWord ++ tailWord_3378334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378334).length < 2 ^ (prefixWord ++ tailWord_3378334).sum := by decide
  have hdescent : baseEnd_3378334 < baseStart_3378334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378340 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 8]
def baseStart_3378340 : Nat := 118140960795 + 3378340 * 2 ^ 59
def prefixEnd_3378340 : Nat := 4983230072969 + 3 ^ 40 * 3378340 * 2
def baseEnd_3378340 : Nat := 192745803812268606990367

theorem tailTrace_3378340 : CollatzResearch.WordTrace tailWord_3378340 prefixEnd_3378340 192745803812268606990367 := by
  unfold tailWord_3378340
  simp only [CollatzResearch.WordTrace]
  refine ⟨61609091290429314690910237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82145455053905752921213649 61609091290429314690910237)
  ·
    refine ⟨23103409233910993009091339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61609091290429314690910237 23103409233910993009091339)
    ·
      refine ⟨34655113850866489513637009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23103409233910993009091339 34655113850866489513637009)
      ·
        refine ⟨25991335388149867135227757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34655113850866489513637009 25991335388149867135227757)
        ·
          refine ⟨9746750770556200175710409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25991335388149867135227757 9746750770556200175710409)
          ·
            refine ⟨7310063077917150131782807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746750770556200175710409 7310063077917150131782807)
            ·
              refine ⟨10965094616875725197674211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310063077917150131782807 10965094616875725197674211)
              ·
                refine ⟨16447641925313587796511317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10965094616875725197674211 16447641925313587796511317)
                ·
                  refine ⟨192745803812268606990367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16447641925313587796511317 192745803812268606990367)
                  ·
                    rfl

theorem cell23_3378340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_3378340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378340 prefixEnd_3378340 := by exact prefixLift 3378340
  have htrace : WordTrace (prefixWord ++ tailWord_3378340) baseStart_3378340 baseEnd_3378340 := by
    simpa [prefixWord, tailWord_3378340, baseEnd_3378340] using wordTrace_append hprefix tailTrace_3378340
  have hstable : (prefixWord ++ tailWord_3378340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378340).length < 2 ^ (prefixWord ++ tailWord_3378340).sum := by decide
  have hdescent : baseEnd_3378340 < baseStart_3378340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378367 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 3]
def baseStart_3378367 : Nat := 118140960795 + 3378367 * 2 ^ 59
def prefixEnd_3378367 : Nat := 4983230072969 + 3 ^ 40 * 3378367 * 2
def baseEnd_3378367 : Nat := 1734726098288088857275679

theorem tailTrace_3378367 : CollatzResearch.WordTrace tailWord_3378367 prefixEnd_3378367 1734726098288088857275679 := by
  unfold tailWord_3378367
  simp only [CollatzResearch.WordTrace]
  refine ⟨123219167351760812993053355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82146111567840541995368903 123219167351760812993053355)
  ·
    refine ⟨184828751027641219489580033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123219167351760812993053355 184828751027641219489580033)
    ·
      refine ⟨138621563270730914617185025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184828751027641219489580033 138621563270730914617185025)
      ·
        refine ⟨103966172453048185962888769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138621563270730914617185025 103966172453048185962888769)
        ·
          refine ⟨77974629339786139472166577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103966172453048185962888769 77974629339786139472166577)
          ·
            refine ⟨58480972004839604604124933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77974629339786139472166577 58480972004839604604124933)
            ·
              refine ⟨10965182250907425863273425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58480972004839604604124933 10965182250907425863273425)
              ·
                refine ⟨8223886688180569397455069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965182250907425863273425 8223886688180569397455069)
                ·
                  refine ⟨3083957508067713524045651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8223886688180569397455069 3083957508067713524045651)
                  ·
                    refine ⟨4625936262101570286068477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3083957508067713524045651 4625936262101570286068477)
                    ·
                      refine ⟨1734726098288088857275679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4625936262101570286068477 1734726098288088857275679)
                      ·
                        rfl

theorem cell23_3378367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_3378367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378367 prefixEnd_3378367 := by exact prefixLift 3378367
  have htrace : WordTrace (prefixWord ++ tailWord_3378367) baseStart_3378367 baseEnd_3378367 := by
    simpa [prefixWord, tailWord_3378367, baseEnd_3378367] using wordTrace_append hprefix tailTrace_3378367
  have hstable : (prefixWord ++ tailWord_3378367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378367).length < 2 ^ (prefixWord ++ tailWord_3378367).sum := by decide
  have hdescent : baseEnd_3378367 < baseStart_3378367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378434 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3378434 : Nat := 118140960795 + 3378434 * 2 ^ 59
def prefixEnd_3378434 : Nat := 4983230072969 + 3 ^ 40 * 3378434 * 2
def baseEnd_3378434 : Nat := 578253500497313365045957

theorem tailTrace_3378434 : CollatzResearch.WordTrace tailWord_3378434 prefixEnd_3378434 578253500497313365045957 := by
  unfold tailWord_3378434
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805402760629520858935589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82147740695012055623828237 30805402760629520858935589)
  ·
    refine ⟨5776013017618035161050423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30805402760629520858935589 5776013017618035161050423)
    ·
      refine ⟨8664019526427052741575635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776013017618035161050423 8664019526427052741575635)
      ·
        refine ⟨12996029289640579112363453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8664019526427052741575635 12996029289640579112363453)
        ·
          refine ⟨4873510983615217167136295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12996029289640579112363453 4873510983615217167136295)
          ·
            refine ⟨7310266475422825750704443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873510983615217167136295 7310266475422825750704443)
            ·
              refine ⟨10965399713134238626056665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310266475422825750704443 10965399713134238626056665)
              ·
                refine ⟨8224049784850678969542499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10965399713134238626056665 8224049784850678969542499)
                ·
                  refine ⟨12336074677276018454313749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224049784850678969542499 12336074677276018454313749)
                  ·
                    refine ⟨578253500497313365045957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12336074677276018454313749 578253500497313365045957)
                    ·
                      rfl

theorem cell23_3378434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3378434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378434 prefixEnd_3378434 := by exact prefixLift 3378434
  have htrace : WordTrace (prefixWord ++ tailWord_3378434) baseStart_3378434 baseEnd_3378434 := by
    simpa [prefixWord, tailWord_3378434, baseEnd_3378434] using wordTrace_append hprefix tailTrace_3378434
  have hstable : (prefixWord ++ tailWord_3378434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378434).length < 2 ^ (prefixWord ++ tailWord_3378434).sum := by decide
  have hdescent : baseEnd_3378434 < baseStart_3378434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378441 : List Nat := [1, 2, 1, 1, 3, 3, 2, 5, 1, 2, 2]
def baseStart_3378441 : Nat := 118140960795 + 3378441 * 2 ^ 59
def prefixEnd_3378441 : Nat := 4983230072969 + 3 ^ 40 * 3378441 * 2
def baseEnd_3378441 : Nat := 1734764095856521567750339

theorem tailTrace_3378441 : CollatzResearch.WordTrace tailWord_3378441 prefixEnd_3378441 1734764095856521567750339 := by
  unfold tailWord_3378441
  simp only [CollatzResearch.WordTrace]
  refine ⟨123221866353492723631247177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82147910902328482420831451 123221866353492723631247177)
  ·
    refine ⟨92416399765119542723435383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123221866353492723631247177 92416399765119542723435383)
    ·
      refine ⟨138624599647679314085153075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92416399765119542723435383 138624599647679314085153075)
      ·
        refine ⟨207936899471518971127729613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138624599647679314085153075 207936899471518971127729613)
        ·
          refine ⟨77976337301819614172898605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207936899471518971127729613 77976337301819614172898605)
          ·
            refine ⟨29241126488182355314836977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77976337301819614172898605 29241126488182355314836977)
            ·
              refine ⟨21930844866136766486127733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29241126488182355314836977 21930844866136766486127733)
              ·
                refine ⟨2056016706200321858074475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21930844866136766486127733 2056016706200321858074475)
                ·
                  refine ⟨3084025059300482787111713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056016706200321858074475 3084025059300482787111713)
                  ·
                    refine ⟨2313018794475362090333785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084025059300482787111713 2313018794475362090333785)
                    ·
                      refine ⟨1734764095856521567750339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313018794475362090333785 1734764095856521567750339)
                      ·
                        rfl

theorem cell23_3378441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 5, 1, 2, 2].length) (baseStart_3378441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378441 prefixEnd_3378441 := by exact prefixLift 3378441
  have htrace : WordTrace (prefixWord ++ tailWord_3378441) baseStart_3378441 baseEnd_3378441 := by
    simpa [prefixWord, tailWord_3378441, baseEnd_3378441] using wordTrace_append hprefix tailTrace_3378441
  have hstable : (prefixWord ++ tailWord_3378441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378441).length < 2 ^ (prefixWord ++ tailWord_3378441).sum := by decide
  have hdescent : baseEnd_3378441 < baseStart_3378441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378458 : List Nat := [3, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2]
def baseStart_3378458 : Nat := 118140960795 + 3378458 * 2 ^ 59
def prefixEnd_3378458 : Nat := 4983230072969 + 3 ^ 40 * 3378458 * 2
def baseEnd_3378458 : Nat := 1734772825027648001237761

theorem tailTrace_3378458 : CollatzResearch.WordTrace tailWord_3378458 prefixEnd_3378458 1734772825027648001237761 := by
  unfold tailWord_3378458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805621598607783883654007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82148324262954090356410685 30805621598607783883654007)
  ·
    refine ⟨46208432397911675825481011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30805621598607783883654007 46208432397911675825481011)
    ·
      refine ⟨69312648596867513738221517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46208432397911675825481011 69312648596867513738221517)
      ·
        refine ⟨25992243223825317651833069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69312648596867513738221517 25992243223825317651833069)
        ·
          refine ⟨9747091208934494119437401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25992243223825317651833069 9747091208934494119437401)
          ·
            refine ⟨7310318406700870589578051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9747091208934494119437401 7310318406700870589578051)
            ·
              refine ⟨10965477610051305884367077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7310318406700870589578051 10965477610051305884367077)
              ·
                refine ⟨2056027051884619853318827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10965477610051305884367077 2056027051884619853318827)
                ·
                  refine ⟨3084040577826929779978241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056027051884619853318827 3084040577826929779978241)
                  ·
                    refine ⟨2313030433370197334983681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084040577826929779978241 2313030433370197334983681)
                    ·
                      refine ⟨1734772825027648001237761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313030433370197334983681 1734772825027648001237761)
                      ·
                        rfl

theorem cell23_3378458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_3378458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378458 prefixEnd_3378458 := by exact prefixLift 3378458
  have htrace : WordTrace (prefixWord ++ tailWord_3378458) baseStart_3378458 baseEnd_3378458 := by
    simpa [prefixWord, tailWord_3378458, baseEnd_3378458] using wordTrace_append hprefix tailTrace_3378458
  have hstable : (prefixWord ++ tailWord_3378458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378458).length < 2 ^ (prefixWord ++ tailWord_3378458).sum := by decide
  have hdescent : baseEnd_3378458 < baseStart_3378458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378460 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_3378460 : Nat := 118140960795 + 3378460 * 2 ^ 59
def prefixEnd_3378460 : Nat := 4983230072969 + 3 ^ 40 * 3378460 * 2
def baseEnd_3378460 : Nat := 578257950662985664470917

theorem tailTrace_3378460 : CollatzResearch.WordTrace tailWord_3378460 prefixEnd_3378460 578257950662985664470917 := by
  unfold tailWord_3378460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61611279670211944938094417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82148372893615926584125889 61611279670211944938094417)
  ·
    refine ⟨46208459752658958703570813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61611279670211944938094417 46208459752658958703570813)
    ·
      refine ⟨17328172407247109513839055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46208459752658958703570813 17328172407247109513839055)
      ·
        refine ⟨25992258610870664270758583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17328172407247109513839055 25992258610870664270758583)
        ·
          refine ⟨38988387916305996406137875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25992258610870664270758583 38988387916305996406137875)
          ·
            refine ⟨58482581874458994609206813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38988387916305996406137875 58482581874458994609206813)
            ·
              refine ⟨21930968202922122978452555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58482581874458994609206813 21930968202922122978452555)
              ·
                refine ⟨32896452304383184467678833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21930968202922122978452555 32896452304383184467678833)
                ·
                  refine ⟨24672339228287388350759125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32896452304383184467678833 24672339228287388350759125)
                  ·
                    refine ⟨578257950662985664470917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24672339228287388350759125 578257950662985664470917)
                    ·
                      rfl

theorem cell23_3378460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_3378460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378460 prefixEnd_3378460 := by exact prefixLift 3378460
  have htrace : WordTrace (prefixWord ++ tailWord_3378460) baseStart_3378460 baseEnd_3378460 := by
    simpa [prefixWord, tailWord_3378460, baseEnd_3378460] using wordTrace_append hprefix tailTrace_3378460
  have hstable : (prefixWord ++ tailWord_3378460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378460).length < 2 ^ (prefixWord ++ tailWord_3378460).sum := by decide
  have hdescent : baseEnd_3378460 < baseStart_3378460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378464 : List Nat := [2, 1, 1, 5, 4, 1, 1, 8]
def baseStart_3378464 : Nat := 118140960795 + 3378464 * 2 ^ 59
def prefixEnd_3378464 : Nat := 4983230072969 + 3 ^ 40 * 3378464 * 2
def baseEnd_3378464 : Nat := 64250959478206480657879

theorem tailTrace_3378464 : CollatzResearch.WordTrace tailWord_3378464 prefixEnd_3378464 64250959478206480657879 := by
  unfold tailWord_3378464
  simp only [CollatzResearch.WordTrace]
  refine ⟨61611352616204699279667223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82148470154939599039556297 61611352616204699279667223)
  ·
    refine ⟨92417028924307048919500835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61611352616204699279667223 92417028924307048919500835)
    ·
      refine ⟨138625543386460573379251253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92417028924307048919500835 138625543386460573379251253)
      ·
        refine ⟨12996144692480678754304805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138625543386460573379251253 12996144692480678754304805)
        ·
          refine ⟨2436777129840127266432151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12996144692480678754304805 2436777129840127266432151)
          ·
            refine ⟨3655165694760190899648227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436777129840127266432151 3655165694760190899648227)
            ·
              refine ⟨5482748542140286349472341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655165694760190899648227 5482748542140286349472341)
              ·
                refine ⟨64250959478206480657879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5482748542140286349472341 64250959478206480657879)
                ·
                  rfl

theorem cell23_3378464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 8].length) (baseStart_3378464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378464 prefixEnd_3378464 := by exact prefixLift 3378464
  have htrace : WordTrace (prefixWord ++ tailWord_3378464) baseStart_3378464 baseEnd_3378464 := by
    simpa [prefixWord, tailWord_3378464, baseEnd_3378464] using wordTrace_append hprefix tailTrace_3378464
  have hstable : (prefixWord ++ tailWord_3378464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378464).length < 2 ^ (prefixWord ++ tailWord_3378464).sum := by decide
  have hdescent : baseEnd_3378464 < baseStart_3378464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378474 : List Nat := [3, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3378474 : Nat := 118140960795 + 3378474 * 2 ^ 59
def prefixEnd_3378474 : Nat := 4983230072969 + 3 ^ 40 * 3378474 * 2
def baseEnd_3378474 : Nat := 1734781040718119938637687

theorem tailTrace_3378474 : CollatzResearch.WordTrace tailWord_3378474 prefixEnd_3378474 1734781040718119938637687 := by
  unfold tailWord_3378474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805767490593292566799619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82148713308248780178132317 30805767490593292566799619)
  ·
    refine ⟨46208651235889938850199429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30805767490593292566799619 46208651235889938850199429)
    ·
      refine ⟨8664122106729363534412393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46208651235889938850199429 8664122106729363534412393)
      ·
        refine ⟨6498091580047022650809295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8664122106729363534412393 6498091580047022650809295)
        ·
          refine ⟨9747137370070533976213943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498091580047022650809295 9747137370070533976213943)
          ·
            refine ⟨14620706055105800964320915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9747137370070533976213943 14620706055105800964320915)
            ·
              refine ⟨21931059082658701446481373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14620706055105800964320915 21931059082658701446481373)
              ·
                refine ⟨8224147155997013042430515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21931059082658701446481373 8224147155997013042430515)
                ·
                  refine ⟨12336220733995519563645773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224147155997013042430515 12336220733995519563645773)
                  ·
                    refine ⟨4626082775248319836367165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12336220733995519563645773 4626082775248319836367165)
                    ·
                      refine ⟨1734781040718119938637687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4626082775248319836367165 1734781040718119938637687)
                      ·
                        rfl

theorem cell23_3378474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3378474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378474 prefixEnd_3378474 := by exact prefixLift 3378474
  have htrace : WordTrace (prefixWord ++ tailWord_3378474) baseStart_3378474 baseEnd_3378474 := by
    simpa [prefixWord, tailWord_3378474, baseEnd_3378474] using wordTrace_append hprefix tailTrace_3378474
  have hstable : (prefixWord ++ tailWord_3378474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378474).length < 2 ^ (prefixWord ++ tailWord_3378474).sum := by decide
  have hdescent : baseEnd_3378474 < baseStart_3378474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378480 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_3378480 : Nat := 118140960795 + 3378480 * 2 ^ 59
def prefixEnd_3378480 : Nat := 4983230072969 + 3 ^ 40 * 3378480 * 2
def baseEnd_3378480 : Nat := 1734784121602046915162659

theorem tailTrace_3378480 : CollatzResearch.WordTrace tailWord_3378480 prefixEnd_3378480 1734784121602046915162659 := by
  unfold tailWord_3378480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61611644400175716645958447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82148859200234288861277929 61611644400175716645958447)
  ·
    refine ⟨92417466600263574968937671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61611644400175716645958447 92417466600263574968937671)
    ·
      refine ⟨138626199900395362453406507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92417466600263574968937671 138626199900395362453406507)
      ·
        refine ⟨207939299850593043680109761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138626199900395362453406507 207939299850593043680109761)
        ·
          refine ⟨155954474887944782760082321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207939299850593043680109761 155954474887944782760082321)
          ·
            refine ⟨116965856165958587070061741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155954474887944782760082321 116965856165958587070061741)
            ·
              refine ⟨43862196062234470151273153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116965856165958587070061741 43862196062234470151273153)
              ·
                refine ⟨32896647046675852613454865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43862196062234470151273153 32896647046675852613454865)
                ·
                  refine ⟨24672485285006889460091149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32896647046675852613454865 24672485285006889460091149)
                  ·
                    refine ⟨9252181981877583547534181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24672485285006889460091149 9252181981877583547534181)
                    ·
                      refine ⟨1734784121602046915162659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9252181981877583547534181 1734784121602046915162659)
                      ·
                        rfl

theorem cell23_3378480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_3378480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378480 prefixEnd_3378480 := by exact prefixLift 3378480
  have htrace : WordTrace (prefixWord ++ tailWord_3378480) baseStart_3378480 baseEnd_3378480 := by
    simpa [prefixWord, tailWord_3378480, baseEnd_3378480] using wordTrace_append hprefix tailTrace_3378480
  have hstable : (prefixWord ++ tailWord_3378480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378480).length < 2 ^ (prefixWord ++ tailWord_3378480).sum := by decide
  have hdescent : baseEnd_3378480 < baseStart_3378480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378490 : List Nat := [3, 1, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_3378490 : Nat := 118140960795 + 3378490 * 2 ^ 59
def prefixEnd_3378490 : Nat := 4983230072969 + 3 ^ 40 * 3378490 * 2
def baseEnd_3378490 : Nat := 578263085469530625345871

theorem tailTrace_3378490 : CollatzResearch.WordTrace tailWord_3378490 prefixEnd_3378490 578263085469530625345871 := by
  unfold tailWord_3378490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805913382578801249945231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82149102353543469999853949 30805913382578801249945231)
  ·
    refine ⟨46208870073868201874917847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30805913382578801249945231 46208870073868201874917847)
    ·
      refine ⟨69313305110802302812376771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46208870073868201874917847 69313305110802302812376771)
      ·
        refine ⟨103969957666203454218565157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69313305110802302812376771 103969957666203454218565157)
        ·
          refine ⟨19494367062413147665980967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103969957666203454218565157 19494367062413147665980967)
          ·
            refine ⟨29241550593619721498971451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19494367062413147665980967 29241550593619721498971451)
            ·
              refine ⟨43862325890429582248457177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29241550593619721498971451 43862325890429582248457177)
              ·
                refine ⟨32896744417822186686342883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43862325890429582248457177 32896744417822186686342883)
                ·
                  refine ⟨49345116626733280029514325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32896744417822186686342883 49345116626733280029514325)
                  ·
                    refine ⟨578263085469530625345871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49345116626733280029514325 578263085469530625345871)
                    ·
                      rfl

theorem cell23_3378490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_3378490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378490 prefixEnd_3378490 := by exact prefixLift 3378490
  have htrace : WordTrace (prefixWord ++ tailWord_3378490) baseStart_3378490 baseEnd_3378490 := by
    simpa [prefixWord, tailWord_3378490, baseEnd_3378490] using wordTrace_append hprefix tailTrace_3378490
  have hstable : (prefixWord ++ tailWord_3378490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378490).length < 2 ^ (prefixWord ++ tailWord_3378490).sum := by decide
  have hdescent : baseEnd_3378490 < baseStart_3378490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378502 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_3378502 : Nat := 118140960795 + 3378502 * 2 ^ 59
def prefixEnd_3378502 : Nat := 4983230072969 + 3 ^ 40 * 3378502 * 2
def baseEnd_3378502 : Nat := 578265139392148609695853

theorem tailTrace_3378502 : CollatzResearch.WordTrace tailWord_3378502 prefixEnd_3378502 578265139392148609695853 := by
  unfold tailWord_3378502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3850752850195991595288055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82149394137514487366145173 3850752850195991595288055)
  ·
    refine ⟨5776129275293987392932083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3850752850195991595288055 5776129275293987392932083)
    ·
      refine ⟨8664193912940981089398125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776129275293987392932083 8664193912940981089398125)
      ·
        refine ⟨3249072717352867908524297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8664193912940981089398125 3249072717352867908524297)
        ·
          refine ⟨2436804538014650931393223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3249072717352867908524297 2436804538014650931393223)
          ·
            refine ⟨3655206807021976397089835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436804538014650931393223 3655206807021976397089835)
            ·
              refine ⟨5482810210532964595634753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655206807021976397089835 5482810210532964595634753)
              ·
                refine ⟨4112107657899723446726065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5482810210532964595634753 4112107657899723446726065)
                ·
                  refine ⟨3084080743424792585044549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112107657899723446726065 3084080743424792585044549)
                  ·
                    refine ⟨578265139392148609695853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084080743424792585044549 578265139392148609695853)
                    ·
                      rfl

theorem cell23_3378502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_3378502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378502 prefixEnd_3378502 := by exact prefixLift 3378502
  have htrace : WordTrace (prefixWord ++ tailWord_3378502) baseStart_3378502 baseEnd_3378502 := by
    simpa [prefixWord, tailWord_3378502, baseEnd_3378502] using wordTrace_append hprefix tailTrace_3378502
  have hstable : (prefixWord ++ tailWord_3378502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378502).length < 2 ^ (prefixWord ++ tailWord_3378502).sum := by decide
  have hdescent : baseEnd_3378502 < baseStart_3378502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378525 : List Nat := [1, 4, 5, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_3378525 : Nat := 118140960795 + 3378525 * 2 ^ 59
def prefixEnd_3378525 : Nat := 4983230072969 + 3 ^ 40 * 3378525 * 2
def baseEnd_3378525 : Nat := 1734807228231499239099953

theorem tailTrace_3378525 : CollatzResearch.WordTrace tailWord_3378525 prefixEnd_3378525 1734807228231499239099953 := by
  unfold tailWord_3378525
  simp only [CollatzResearch.WordTrace]
  refine ⟨123224930085188405977305029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82149953390125603984870019 123224930085188405977305029)
  ·
    refine ⟨23104674390972826120744693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123224930085188405977305029 23104674390972826120744693)
    ·
      refine ⟨2166063224153702448819815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23104674390972826120744693 2166063224153702448819815)
      ·
        refine ⟨3249094836230553673229723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166063224153702448819815 3249094836230553673229723)
        ·
          refine ⟨4873642254345830509844585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249094836230553673229723 4873642254345830509844585)
          ·
            refine ⟨3655231690759372882383439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873642254345830509844585 3655231690759372882383439)
            ·
              refine ⟨5482847536139059323575159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655231690759372882383439 5482847536139059323575159)
              ·
                refine ⟨8224271304208588985362739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482847536139059323575159 8224271304208588985362739)
                ·
                  refine ⟨12336406956312883478044109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224271304208588985362739 12336406956312883478044109)
                  ·
                    refine ⟨4626152608617331304266541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12336406956312883478044109 4626152608617331304266541)
                    ·
                      refine ⟨1734807228231499239099953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4626152608617331304266541 1734807228231499239099953)
                      ·
                        rfl

theorem cell23_3378525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_3378525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378525 prefixEnd_3378525 := by exact prefixLift 3378525
  have htrace : WordTrace (prefixWord ++ tailWord_3378525) baseStart_3378525 baseEnd_3378525 := by
    simpa [prefixWord, tailWord_3378525, baseEnd_3378525] using wordTrace_append hprefix tailTrace_3378525
  have hstable : (prefixWord ++ tailWord_3378525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378525).length < 2 ^ (prefixWord ++ tailWord_3378525).sum := by decide
  have hdescent : baseEnd_3378525 < baseStart_3378525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378531 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 1, 4, 2]
def baseStart_3378531 : Nat := 118140960795 + 3378531 * 2 ^ 59
def prefixEnd_3378531 : Nat := 4983230072969 + 3 ^ 40 * 3378531 * 2
def baseEnd_3378531 : Nat := 1734810309115426215624925

theorem tailTrace_3378531 : CollatzResearch.WordTrace tailWord_3378531 prefixEnd_3378531 1734810309115426215624925 := by
  unfold tailWord_3378531
  simp only [CollatzResearch.WordTrace]
  refine ⟨123225148923166669002023447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82150099282111112668015631 123225148923166669002023447)
  ·
    refine ⟨184837723384750003503035171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123225148923166669002023447 184837723384750003503035171)
    ·
      refine ⟨277256585077125005254552757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184837723384750003503035171 277256585077125005254552757)
      ·
        refine ⟨25992804850980469242614321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277256585077125005254552757 25992804850980469242614321)
        ·
          refine ⟨19494603638235351931960741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25992804850980469242614321 19494603638235351931960741)
          ·
            refine ⟨3655238182169128487242639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19494603638235351931960741 3655238182169128487242639)
            ·
              refine ⟨5482857273253692730863959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655238182169128487242639 5482857273253692730863959)
              ·
                refine ⟨8224285909880539096295939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5482857273253692730863959 8224285909880539096295939)
                ·
                  refine ⟨12336428864820808644443909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8224285909880539096295939 12336428864820808644443909)
                  ·
                    refine ⟨2313080412153901620833233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12336428864820808644443909 2313080412153901620833233)
                    ·
                      refine ⟨1734810309115426215624925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313080412153901620833233 1734810309115426215624925)
                      ·
                        rfl

theorem cell23_3378531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_3378531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378531 prefixEnd_3378531 := by exact prefixLift 3378531
  have htrace : WordTrace (prefixWord ++ tailWord_3378531) baseStart_3378531 baseEnd_3378531 := by
    simpa [prefixWord, tailWord_3378531, baseEnd_3378531] using wordTrace_append hprefix tailTrace_3378531
  have hstable : (prefixWord ++ tailWord_3378531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378531).length < 2 ^ (prefixWord ++ tailWord_3378531).sum := by decide
  have hdescent : baseEnd_3378531 < baseStart_3378531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378560 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_3378560 : Nat := 118140960795 + 3378560 * 2 ^ 59
def prefixEnd_3378560 : Nat := 4983230072969 + 3 ^ 40 * 3378560 * 2
def baseEnd_3378560 : Nat := 1734825200054406602162291

theorem tailTrace_3378560 : CollatzResearch.WordTrace tailWord_3378560 prefixEnd_3378560 1734825200054406602162291 := by
  unfold tailWord_3378560
  simp only [CollatzResearch.WordTrace]
  refine ⟨61613103320030803477414567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82150804426707737969886089 61613103320030803477414567)
  ·
    refine ⟨92419654980046205216121851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61613103320030803477414567 92419654980046205216121851)
    ·
      refine ⟨138629482470069307824182777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92419654980046205216121851 138629482470069307824182777)
      ·
        refine ⟨103972111852551980868137083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138629482470069307824182777 103972111852551980868137083)
        ·
          refine ⟨155958167778827971302205625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103972111852551980868137083 155958167778827971302205625)
          ·
            refine ⟨116968625834120978476654219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155958167778827971302205625 116968625834120978476654219)
            ·
              refine ⟨175452938751181467714981329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116968625834120978476654219 175452938751181467714981329)
              ·
                refine ⟨131589704063386100786235997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175452938751181467714981329 131589704063386100786235997)
                ·
                  refine ⟨49346139023769787794838499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131589704063386100786235997 49346139023769787794838499)
                  ·
                    refine ⟨74019208535654681692257749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49346139023769787794838499 74019208535654681692257749)
                    ·
                      refine ⟨1734825200054406602162291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74019208535654681692257749 1734825200054406602162291)
                      ·
                        rfl

theorem cell23_3378560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_3378560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378560 prefixEnd_3378560 := by exact prefixLift 3378560
  have htrace : WordTrace (prefixWord ++ tailWord_3378560) baseStart_3378560 baseEnd_3378560 := by
    simpa [prefixWord, tailWord_3378560, baseEnd_3378560] using wordTrace_append hprefix tailTrace_3378560
  have hstable : (prefixWord ++ tailWord_3378560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378560).length < 2 ^ (prefixWord ++ tailWord_3378560).sum := by decide
  have hdescent : baseEnd_3378560 < baseStart_3378560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378567 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 4, 5]
def baseStart_3378567 : Nat := 118140960795 + 3378567 * 2 ^ 59
def prefixEnd_3378567 : Nat := 4983230072969 + 3 ^ 40 * 3378567 * 2
def baseEnd_3378567 : Nat := 578276264806329358258253

theorem tailTrace_3378567 : CollatzResearch.WordTrace tailWord_3378567 prefixEnd_3378567 578276264806329358258253 := by
  unfold tailWord_3378567
  simp only [CollatzResearch.WordTrace]
  refine ⟨123226461951036247150333955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82150974634024164766889303 123226461951036247150333955)
  ·
    refine ⟨184839692926554370725500933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123226461951036247150333955 184839692926554370725500933)
    ·
      refine ⟨34657442423728944511031425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184839692926554370725500933 34657442423728944511031425)
      ·
        refine ⟨25993081817796708383273569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34657442423728944511031425 25993081817796708383273569)
        ·
          refine ⟨19494811363347531287455177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25993081817796708383273569 19494811363347531287455177)
          ·
            refine ⟨14621108522510648465591383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19494811363347531287455177 14621108522510648465591383)
            ·
              refine ⟨21931662783765972698387075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14621108522510648465591383 21931662783765972698387075)
              ·
                refine ⟨32897494175648959047580613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21931662783765972698387075 32897494175648959047580613)
                ·
                  refine ⟨6168280157934179821421365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32897494175648959047580613 6168280157934179821421365)
                  ·
                    refine ⟨578276264806329358258253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6168280157934179821421365 578276264806329358258253)
                    ·
                      rfl

theorem cell23_3378567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_3378567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378567 prefixEnd_3378567 := by exact prefixLift 3378567
  have htrace : WordTrace (prefixWord ++ tailWord_3378567) baseStart_3378567 baseEnd_3378567 := by
    simpa [prefixWord, tailWord_3378567, baseEnd_3378567] using wordTrace_append hprefix tailTrace_3378567
  have hstable : (prefixWord ++ tailWord_3378567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378567).length < 2 ^ (prefixWord ++ tailWord_3378567).sum := by decide
  have hdescent : baseEnd_3378567 < baseStart_3378567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378607 : List Nat := [1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 3]
def baseStart_3378607 : Nat := 118140960795 + 3378607 * 2 ^ 59
def prefixEnd_3378607 : Nat := 4983230072969 + 3 ^ 40 * 3378607 * 2
def baseEnd_3378607 : Nat := 1734849333645167918274575

theorem tailTrace_3378607 : CollatzResearch.WordTrace tailWord_3378607 prefixEnd_3378607 1734849333645167918274575 := by
  unfold tailWord_3378607
  simp only [CollatzResearch.WordTrace]
  refine ⟨123227920870891333981790075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82151947247260889321193383 123227920870891333981790075)
  ·
    refine ⟨184841881306337000972685113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123227920870891333981790075 184841881306337000972685113)
    ·
      refine ⟨138631410979752750729513835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184841881306337000972685113 138631410979752750729513835)
      ·
        refine ⟨207947116469629126094270753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138631410979752750729513835 207947116469629126094270753)
        ·
          refine ⟨155960337352221844570703065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207947116469629126094270753 155960337352221844570703065)
          ·
            refine ⟨116970253014166383428027299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155960337352221844570703065 116970253014166383428027299)
            ·
              refine ⟨175455379521249575142040949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116970253014166383428027299 175455379521249575142040949)
              ·
                refine ⟨16448941830117147669566339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175455379521249575142040949 16448941830117147669566339)
                ·
                  refine ⟨24673412745175721504349509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16448941830117147669566339 24673412745175721504349509)
                  ·
                    refine ⟨4626264889720447782065533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24673412745175721504349509 4626264889720447782065533)
                    ·
                      refine ⟨1734849333645167918274575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4626264889720447782065533 1734849333645167918274575)
                      ·
                        rfl

theorem cell23_3378607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 3].length) (baseStart_3378607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378607 prefixEnd_3378607 := by exact prefixLift 3378607
  have htrace : WordTrace (prefixWord ++ tailWord_3378607) baseStart_3378607 baseEnd_3378607 := by
    simpa [prefixWord, tailWord_3378607, baseEnd_3378607] using wordTrace_append hprefix tailTrace_3378607
  have hstable : (prefixWord ++ tailWord_3378607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378607).length < 2 ^ (prefixWord ++ tailWord_3378607).sum := by decide
  have hdescent : baseEnd_3378607 < baseStart_3378607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378624 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3]
def baseStart_3378624 : Nat := 118140960795 + 3378624 * 2 ^ 59
def prefixEnd_3378624 : Nat := 4983230072969 + 3 ^ 40 * 3378624 * 2
def baseEnd_3378624 : Nat := 1734858062816294351761997

theorem tailTrace_3378624 : CollatzResearch.WordTrace tailWord_3378624 prefixEnd_3378624 1734858062816294351761997 := by
  unfold tailWord_3378624
  simp only [CollatzResearch.WordTrace]
  refine ⟨61614270455914872942579463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82152360607886497256772617 61614270455914872942579463)
  ·
    refine ⟨92421405683872309413869195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61614270455914872942579463 92421405683872309413869195)
    ·
      refine ⟨138632108525808464120803793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92421405683872309413869195 138632108525808464120803793)
      ·
        refine ⟨103974081394356348090602845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138632108525808464120803793 103974081394356348090602845)
        ·
          refine ⟨38990280522883630533976067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103974081394356348090602845 38990280522883630533976067)
          ·
            refine ⟨58485420784325445800964101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38990280522883630533976067 58485420784325445800964101)
            ·
              refine ⟨10966016397061021087680769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58485420784325445800964101 10966016397061021087680769)
              ·
                refine ⟨8224512297795765815760577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10966016397061021087680769 8224512297795765815760577)
                ·
                  refine ⟨6168384223346824361820433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8224512297795765815760577 6168384223346824361820433)
                  ·
                    refine ⟨4626288167510118271365325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6168384223346824361820433 4626288167510118271365325)
                    ·
                      refine ⟨1734858062816294351761997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4626288167510118271365325 1734858062816294351761997)
                      ·
                        rfl

theorem cell23_3378624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 3].length) (baseStart_3378624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378624 prefixEnd_3378624 := by exact prefixLift 3378624
  have htrace : WordTrace (prefixWord ++ tailWord_3378624) baseStart_3378624 baseEnd_3378624 := by
    simpa [prefixWord, tailWord_3378624, baseEnd_3378624] using wordTrace_append hprefix tailTrace_3378624
  have hstable : (prefixWord ++ tailWord_3378624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378624).length < 2 ^ (prefixWord ++ tailWord_3378624).sum := by decide
  have hdescent : baseEnd_3378624 < baseStart_3378624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378627 : List Nat := [1, 1, 1, 3, 1, 1, 5, 4, 6]
def baseStart_3378627 : Nat := 118140960795 + 3378627 * 2 ^ 59
def prefixEnd_3378627 : Nat := 4983230072969 + 3 ^ 40 * 3378627 * 2
def baseEnd_3378627 : Nat := 192762178139806426669387

theorem tailTrace_3378627 : CollatzResearch.WordTrace tailWord_3378627 prefixEnd_3378627 192762178139806426669387 := by
  unfold tailWord_3378627
  simp only [CollatzResearch.WordTrace]
  refine ⟨123228650330818877397518135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82152433553879251598345423 123228650330818877397518135)
  ·
    refine ⟨184842975496228316096277203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123228650330818877397518135 184842975496228316096277203)
    ·
      refine ⟨277264463244342474144415805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184842975496228316096277203 277264463244342474144415805)
      ·
        refine ⟨103974173716628427804155927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277264463244342474144415805 103974173716628427804155927)
        ·
          refine ⟨155961260574942641706233891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103974173716628427804155927 155961260574942641706233891)
          ·
            refine ⟨233941890862413962559350837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155961260574942641706233891 233941890862413962559350837)
            ·
              refine ⟨21932052268351308989939141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233941890862413962559350837 21932052268351308989939141)
              ·
                refine ⟨4112259800315870435613589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21932052268351308989939141 4112259800315870435613589)
                ·
                  refine ⟨192762178139806426669387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4112259800315870435613589 192762178139806426669387)
                  ·
                    rfl

theorem cell23_3378627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 4, 6].length) (baseStart_3378627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378627 prefixEnd_3378627 := by exact prefixLift 3378627
  have htrace : WordTrace (prefixWord ++ tailWord_3378627) baseStart_3378627 baseEnd_3378627 := by
    simpa [prefixWord, tailWord_3378627, baseEnd_3378627] using wordTrace_append hprefix tailTrace_3378627
  have hstable : (prefixWord ++ tailWord_3378627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378627).length < 2 ^ (prefixWord ++ tailWord_3378627).sum := by decide
  have hdescent : baseEnd_3378627 < baseStart_3378627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378631 : List Nat := [1, 1, 4, 1, 1, 3, 3, 4, 1, 4]
def baseStart_3378631 : Nat := 118140960795 + 3378631 * 2 ^ 59
def prefixEnd_3378631 : Nat := 4983230072969 + 3 ^ 40 * 3378631 * 2
def baseEnd_3378631 : Nat := 578287219060291941458155

theorem tailTrace_3378631 : CollatzResearch.WordTrace tailWord_3378631 prefixEnd_3378631 578287219060291941458155 := by
  unfold tailWord_3378631
  simp only [CollatzResearch.WordTrace]
  refine ⟨123228796222804386080663747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82152530815202924053775831 123228796222804386080663747)
  ·
    refine ⟨184843194334206579120995621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123228796222804386080663747 184843194334206579120995621)
    ·
      refine ⟨34658098937663733585186679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184843194334206579120995621 34658098937663733585186679)
      ·
        refine ⟨51987148406495600377780019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34658098937663733585186679 51987148406495600377780019)
        ·
          refine ⟨77980722609743400566670029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51987148406495600377780019 77980722609743400566670029)
          ·
            refine ⟨29242770978653775212501261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77980722609743400566670029 29242770978653775212501261)
            ·
              refine ⟨10966039116995165704687973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29242770978653775212501261 10966039116995165704687973)
              ·
                refine ⟨2056132334436593569628995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10966039116995165704687973 2056132334436593569628995)
                ·
                  refine ⟨3084198501654890354443493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056132334436593569628995 3084198501654890354443493)
                  ·
                    refine ⟨578287219060291941458155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084198501654890354443493 578287219060291941458155)
                    ·
                      rfl

theorem cell23_3378631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_3378631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378631 prefixEnd_3378631 := by exact prefixLift 3378631
  have htrace : WordTrace (prefixWord ++ tailWord_3378631) baseStart_3378631 baseEnd_3378631 := by
    simpa [prefixWord, tailWord_3378631, baseEnd_3378631] using wordTrace_append hprefix tailTrace_3378631
  have hstable : (prefixWord ++ tailWord_3378631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378631).length < 2 ^ (prefixWord ++ tailWord_3378631).sum := by decide
  have hdescent : baseEnd_3378631 < baseStart_3378631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378734 : List Nat := [4, 1, 3, 1, 2, 1, 11]
def baseStart_3378734 : Nat := 118140960795 + 3378734 * 2 ^ 59
def prefixEnd_3378734 : Nat := 4983230072969 + 3 ^ 40 * 3378734 * 2
def baseEnd_3378734 : Nat := 21418698094917147177611

theorem tailTrace_3378734 : CollatzResearch.WordTrace tailWord_3378734 prefixEnd_3378734 21418698094917147177611 := by
  unfold tailWord_3378734
  simp only [CollatzResearch.WordTrace]
  refine ⟨15404069117678904333957907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82155035294287489781108837 15404069117678904333957907)
  ·
    refine ⟨23106103676518356500936861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15404069117678904333957907 23106103676518356500936861)
    ·
      refine ⟨8664788878694383687851323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23106103676518356500936861 8664788878694383687851323)
      ·
        refine ⟨12997183318041575531776985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8664788878694383687851323 12997183318041575531776985)
        ·
          refine ⟨9747887488531181648832739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12997183318041575531776985 9747887488531181648832739)
          ·
            refine ⟨14621831232796772473249109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9747887488531181648832739 14621831232796772473249109)
            ·
              refine ⟨21418698094917147177611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14621831232796772473249109 21418698094917147177611)
              ·
                rfl

theorem cell23_3378734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 11].length) (baseStart_3378734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378734 prefixEnd_3378734 := by exact prefixLift 3378734
  have htrace : WordTrace (prefixWord ++ tailWord_3378734) baseStart_3378734 baseEnd_3378734 := by
    simpa [prefixWord, tailWord_3378734, baseEnd_3378734] using wordTrace_append hprefix tailTrace_3378734
  have hstable : (prefixWord ++ tailWord_3378734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378734).length < 2 ^ (prefixWord ++ tailWord_3378734).sum := by decide
  have hdescent : baseEnd_3378734 < baseStart_3378734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378745 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3378745 : Nat := 118140960795 + 3378745 * 2 ^ 59
def prefixEnd_3378745 : Nat := 4983230072969 + 3 ^ 40 * 3378745 * 2
def baseEnd_3378745 : Nat := 1734920193975488378348941

theorem tailTrace_3378745 : CollatzResearch.WordTrace tailWord_3378745 prefixEnd_3378745 1734920193975488378348941 := by
  unfold tailWord_3378745
  simp only [CollatzResearch.WordTrace]
  refine ⟨123232954144391383550313689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82155302762927589033542459 123232954144391383550313689)
  ·
    refine ⟨92424715608293537662735267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123232954144391383550313689 92424715608293537662735267)
    ·
      refine ⟨138637073412440306494102901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92424715608293537662735267 138637073412440306494102901)
      ·
        refine ⟨12997225632416278733822147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138637073412440306494102901 12997225632416278733822147)
        ·
          refine ⟨19495838448624418100733221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12997225632416278733822147 19495838448624418100733221)
          ·
            refine ⟨3655469709117078393887479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19495838448624418100733221 3655469709117078393887479)
            ·
              refine ⟨5483204563675617590831219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655469709117078393887479 5483204563675617590831219)
              ·
                refine ⟨8224806845513426386246829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483204563675617590831219 8224806845513426386246829)
                ·
                  refine ⟨3084302567067534894842561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8224806845513426386246829 3084302567067534894842561)
                  ·
                    refine ⟨2313226925300651171131921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084302567067534894842561 2313226925300651171131921)
                    ·
                      refine ⟨1734920193975488378348941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313226925300651171131921 1734920193975488378348941)
                      ·
                        rfl

theorem cell23_3378745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3378745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378745 prefixEnd_3378745 := by exact prefixLift 3378745
  have htrace : WordTrace (prefixWord ++ tailWord_3378745) baseStart_3378745 baseEnd_3378745 := by
    simpa [prefixWord, tailWord_3378745, baseEnd_3378745] using wordTrace_append hprefix tailTrace_3378745
  have hstable : (prefixWord ++ tailWord_3378745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378745).length < 2 ^ (prefixWord ++ tailWord_3378745).sum := by decide
  have hdescent : baseEnd_3378745 < baseStart_3378745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378767 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_3378767 : Nat := 118140960795 + 3378767 * 2 ^ 59
def prefixEnd_3378767 : Nat := 4983230072969 + 3 ^ 40 * 3378767 * 2
def baseEnd_3378767 : Nat := 1734931490549887292273839

theorem tailTrace_3378767 : CollatzResearch.WordTrace tailWord_3378767 prefixEnd_3378767 1734931490549887292273839 := by
  unfold tailWord_3378767
  simp only [CollatzResearch.WordTrace]
  refine ⟨123233756550311681307614555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82155837700207787538409703 123233756550311681307614555)
  ·
    refine ⟨184850634825467521961421833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123233756550311681307614555 184850634825467521961421833)
    ·
      refine ⟨138637976119100641471066375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184850634825467521961421833 138637976119100641471066375)
      ·
        refine ⟨207956964178650962206599563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138637976119100641471066375 207956964178650962206599563)
        ·
          refine ⟨311935446267976443309899345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207956964178650962206599563 311935446267976443309899345)
          ·
            refine ⟨233951584700982332482424509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311935446267976443309899345 233951584700982332482424509)
            ·
              refine ⟨87731844262868374680909191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233951584700982332482424509 87731844262868374680909191)
              ·
                refine ⟨131597766394302562021363787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87731844262868374680909191 131597766394302562021363787)
                ·
                  refine ⟨197396649591453843032045681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131597766394302562021363787 197396649591453843032045681)
                  ·
                    refine ⟨148047487193590382274034261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 197396649591453843032045681 148047487193590382274034261)
                    ·
                      refine ⟨1734931490549887292273839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 148047487193590382274034261 1734931490549887292273839)
                      ·
                        rfl

theorem cell23_3378767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_3378767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378767 prefixEnd_3378767 := by exact prefixLift 3378767
  have htrace : WordTrace (prefixWord ++ tailWord_3378767) baseStart_3378767 baseEnd_3378767 := by
    simpa [prefixWord, tailWord_3378767, baseEnd_3378767] using wordTrace_append hprefix tailTrace_3378767
  have hstable : (prefixWord ++ tailWord_3378767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378767).length < 2 ^ (prefixWord ++ tailWord_3378767).sum := by decide
  have hdescent : baseEnd_3378767 < baseStart_3378767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378852 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 2, 2, 2]
def baseStart_3378852 : Nat := 118140960795 + 3378852 * 2 ^ 59
def prefixEnd_3378852 : Nat := 4983230072969 + 3 ^ 40 * 3378852 * 2
def baseEnd_3378852 : Nat := 1734975136405519459710949

theorem tailTrace_3378852 : CollatzResearch.WordTrace tailWord_3378852 prefixEnd_3378852 1734975136405519459710949 := by
  unfold tailWord_3378852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61618428377501870412229405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82157904503335827216305873 61618428377501870412229405)
  ·
    refine ⟨23106910641563201404586027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61618428377501870412229405 23106910641563201404586027)
    ·
      refine ⟨34660365962344802106879041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23106910641563201404586027 34660365962344802106879041)
      ·
        refine ⟨25995274471758601580159281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34660365962344802106879041 25995274471758601580159281)
        ·
          refine ⟨19496455853818951185119461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25995274471758601580159281 19496455853818951185119461)
          ·
            refine ⟨3655585472591053347209899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19496455853818951185119461 3655585472591053347209899)
            ·
              refine ⟨5483378208886580020814849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655585472591053347209899 5483378208886580020814849)
              ·
                refine ⟨4112533656664935015611137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483378208886580020814849 4112533656664935015611137)
                ·
                  refine ⟨3084400242498701261708353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112533656664935015611137 3084400242498701261708353)
                  ·
                    refine ⟨2313300181874025946281265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084400242498701261708353 2313300181874025946281265)
                    ·
                      refine ⟨1734975136405519459710949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313300181874025946281265 1734975136405519459710949)
                      ·
                        rfl

theorem cell23_3378852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_3378852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378852 prefixEnd_3378852 := by exact prefixLift 3378852
  have htrace : WordTrace (prefixWord ++ tailWord_3378852) baseStart_3378852 baseEnd_3378852 := by
    simpa [prefixWord, tailWord_3378852, baseEnd_3378852] using wordTrace_append hprefix tailTrace_3378852
  have hstable : (prefixWord ++ tailWord_3378852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378852).length < 2 ^ (prefixWord ++ tailWord_3378852).sum := by decide
  have hdescent : baseEnd_3378852 < baseStart_3378852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378864 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_3378864 : Nat := 118140960795 + 3378864 * 2 ^ 59
def prefixEnd_3378864 : Nat := 4983230072969 + 3 ^ 40 * 3378864 * 2
def baseEnd_3378864 : Nat := 1734981298173373412760893

theorem tailTrace_3378864 : CollatzResearch.WordTrace tailWord_3378864 prefixEnd_3378864 1734981298173373412760893 := by
  unfold tailWord_3378864
  simp only [CollatzResearch.WordTrace]
  refine ⟨61618647215480133436947823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82158196287306844582597097 61618647215480133436947823)
  ·
    refine ⟨92427970823220200155421735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61618647215480133436947823 92427970823220200155421735)
    ·
      refine ⟨138641956234830300233132603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92427970823220200155421735 138641956234830300233132603)
      ·
        refine ⟨207962934352245450349698905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138641956234830300233132603 207962934352245450349698905)
        ·
          refine ⟨155972200764184087762274179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207962934352245450349698905 155972200764184087762274179)
          ·
            refine ⟨233958301146276131643411269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155972200764184087762274179 233958301146276131643411269)
            ·
              refine ⟨43867181464926774683139613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233958301146276131643411269 43867181464926774683139613)
              ·
                refine ⟨16450193049347540506177355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43867181464926774683139613 16450193049347540506177355)
                ·
                  refine ⟨24675289574021310759266033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16450193049347540506177355 24675289574021310759266033)
                  ·
                    refine ⟨18506467180515983069449525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24675289574021310759266033 18506467180515983069449525)
                    ·
                      refine ⟨1734981298173373412760893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18506467180515983069449525 1734981298173373412760893)
                      ·
                        rfl

theorem cell23_3378864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_3378864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378864 prefixEnd_3378864 := by exact prefixLift 3378864
  have htrace : WordTrace (prefixWord ++ tailWord_3378864) baseStart_3378864 baseEnd_3378864 := by
    simpa [prefixWord, tailWord_3378864, baseEnd_3378864] using wordTrace_append hprefix tailTrace_3378864
  have hstable : (prefixWord ++ tailWord_3378864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378864).length < 2 ^ (prefixWord ++ tailWord_3378864).sum := by decide
  have hdescent : baseEnd_3378864 < baseStart_3378864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378869 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3378869 : Nat := 118140960795 + 3378869 * 2 ^ 59
def prefixEnd_3378869 : Nat := 4983230072969 + 3 ^ 40 * 3378869 * 2
def baseEnd_3378869 : Nat := 1734983865576645893198371

theorem tailTrace_3378869 : CollatzResearch.WordTrace tailWord_3378869 prefixEnd_3378869 1734983865576645893198371 := by
  unfold tailWord_3378869
  simp only [CollatzResearch.WordTrace]
  refine ⟨123237476795942152727827661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82158317863961435151885107 123237476795942152727827661)
  ·
    refine ⟨46214053798478307272935373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123237476795942152727827661 46214053798478307272935373)
    ·
      refine ⟨17330270174429365227350765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46214053798478307272935373 17330270174429365227350765)
      ·
        refine ⟨6498851315411011960256537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17330270174429365227350765 6498851315411011960256537)
        ·
          refine ⟨4874138486558258970192403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6498851315411011960256537 4874138486558258970192403)
          ·
            refine ⟨7311207729837388455288605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874138486558258970192403 7311207729837388455288605)
            ·
              refine ⟨2741702898689020670733227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7311207729837388455288605 2741702898689020670733227)
              ·
                refine ⟨4112554348033531006099841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741702898689020670733227 4112554348033531006099841)
                ·
                  refine ⟨3084415761025148254574881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112554348033531006099841 3084415761025148254574881)
                  ·
                    refine ⟨2313311820768861190931161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084415761025148254574881 2313311820768861190931161)
                    ·
                      refine ⟨1734983865576645893198371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313311820768861190931161 1734983865576645893198371)
                      ·
                        rfl

theorem cell23_3378869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3378869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378869 prefixEnd_3378869 := by exact prefixLift 3378869
  have htrace : WordTrace (prefixWord ++ tailWord_3378869) baseStart_3378869 baseEnd_3378869 := by
    simpa [prefixWord, tailWord_3378869, baseEnd_3378869] using wordTrace_append hprefix tailTrace_3378869
  have hstable : (prefixWord ++ tailWord_3378869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378869).length < 2 ^ (prefixWord ++ tailWord_3378869).sum := by decide
  have hdescent : baseEnd_3378869 < baseStart_3378869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378891 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 6, 2]
def baseStart_3378891 : Nat := 118140960795 + 3378891 * 2 ^ 59
def prefixEnd_3378891 : Nat := 4983230072969 + 3 ^ 40 * 3378891 * 2
def baseEnd_3378891 : Nat := 1734995162151044807123269

theorem tailTrace_3378891 : CollatzResearch.WordTrace tailWord_3378891 prefixEnd_3378891 1734995162151044807123269 := by
  unfold tailWord_3378891
  simp only [CollatzResearch.WordTrace]
  refine ⟨123238279201862450485128527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82158852801241633656752351 123238279201862450485128527)
  ·
    refine ⟨184857418802793675727692791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123238279201862450485128527 184857418802793675727692791)
    ·
      refine ⟨277286128204190513591539187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184857418802793675727692791 277286128204190513591539187)
      ·
        refine ⟨415929192306285770387308781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277286128204190513591539187 415929192306285770387308781)
        ·
          refine ⟨155973447114857163895240793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 415929192306285770387308781 155973447114857163895240793)
          ·
            refine ⟨116980085336142872921430595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155973447114857163895240793 116980085336142872921430595)
            ·
              refine ⟨175470128004214309382145893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116980085336142872921430595 175470128004214309382145893)
              ·
                refine ⟨32900649000790183009152355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175470128004214309382145893 32900649000790183009152355)
                ·
                  refine ⟨49350973501185274513728533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32900649000790183009152355 49350973501185274513728533)
                  ·
                    refine ⟨2313326882868059742831025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49350973501185274513728533 2313326882868059742831025)
                    ·
                      refine ⟨1734995162151044807123269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313326882868059742831025 1734995162151044807123269)
                      ·
                        rfl

theorem cell23_3378891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6, 2].length) (baseStart_3378891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378891 prefixEnd_3378891 := by exact prefixLift 3378891
  have htrace : WordTrace (prefixWord ++ tailWord_3378891) baseStart_3378891 baseEnd_3378891 := by
    simpa [prefixWord, tailWord_3378891, baseEnd_3378891] using wordTrace_append hprefix tailTrace_3378891
  have hstable : (prefixWord ++ tailWord_3378891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378891).length < 2 ^ (prefixWord ++ tailWord_3378891).sum := by decide
  have hdescent : baseEnd_3378891 < baseStart_3378891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378892 : List Nat := [2, 2, 1, 5, 3, 1, 1, 3, 5]
def baseStart_3378892 : Nat := 118140960795 + 3378892 * 2 ^ 59
def prefixEnd_3378892 : Nat := 4983230072969 + 3 ^ 40 * 3378892 * 2
def baseEnd_3378892 : Nat := 192777297292411033690085

theorem tailTrace_3378892 : CollatzResearch.WordTrace tailWord_3378892 prefixEnd_3378892 192777297292411033690085 := by
  unfold tailWord_3378892
  simp only [CollatzResearch.WordTrace]
  refine ⟨61619157837429413827957465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82158877116572551770609953 61619157837429413827957465)
  ·
    refine ⟨46214368378072060370968099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61619157837429413827957465 46214368378072060370968099)
    ·
      refine ⟨69321552567108090556452149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46214368378072060370968099 69321552567108090556452149)
      ·
        refine ⟨6498895553166383489667389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69321552567108090556452149 6498895553166383489667389)
        ·
          refine ⟨2437085832437393808625271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6498895553166383489667389 2437085832437393808625271)
          ·
            refine ⟨3655628748656090712937907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437085832437393808625271 3655628748656090712937907)
            ·
              refine ⟨5483443122984136069406861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655628748656090712937907 5483443122984136069406861)
              ·
                refine ⟨2056291171119051026027573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5483443122984136069406861 2056291171119051026027573)
                ·
                  refine ⟨192777297292411033690085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056291171119051026027573 192777297292411033690085)
                  ·
                    rfl

theorem cell23_3378892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_3378892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378892 prefixEnd_3378892 := by exact prefixLift 3378892
  have htrace : WordTrace (prefixWord ++ tailWord_3378892) baseStart_3378892 baseEnd_3378892 := by
    simpa [prefixWord, tailWord_3378892, baseEnd_3378892] using wordTrace_append hprefix tailTrace_3378892
  have hstable : (prefixWord ++ tailWord_3378892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378892).length < 2 ^ (prefixWord ++ tailWord_3378892).sum := by decide
  have hdescent : baseEnd_3378892 < baseStart_3378892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3378944 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 2, 9]
def baseStart_3378944 : Nat := 118140960795 + 3378944 * 2 ^ 59
def prefixEnd_3378944 : Nat := 4983230072969 + 3 ^ 40 * 3378944 * 2
def baseEnd_3378944 : Nat := 578340792208577699920175

theorem tailTrace_3378944 : CollatzResearch.WordTrace tailWord_3378944 prefixEnd_3378944 578340792208577699920175 := by
  unfold tailWord_3378944
  simp only [CollatzResearch.WordTrace]
  refine ⟨61620106135335220268403943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82160141513780293691205257 61620106135335220268403943)
  ·
    refine ⟨92430159203002830402605915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61620106135335220268403943 92430159203002830402605915)
    ·
      refine ⟨138645238804504245603908873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92430159203002830402605915 138645238804504245603908873)
      ·
        refine ⟨103983929103378184202931655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138645238804504245603908873 103983929103378184202931655)
        ·
          refine ⟨155975893655067276304397483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103983929103378184202931655 155975893655067276304397483)
          ·
            refine ⟨233963840482600914456596225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155975893655067276304397483 233963840482600914456596225)
            ·
              refine ⟨175472880361950685842447169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233963840482600914456596225 175472880361950685842447169)
              ·
                refine ⟨131604660271463014381835377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175472880361950685842447169 131604660271463014381835377)
                ·
                  refine ⟨98703495203597260786376533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131604660271463014381835377 98703495203597260786376533)
                  ·
                    refine ⟨578340792208577699920175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 98703495203597260786376533 578340792208577699920175)
                    ·
                      rfl

theorem cell23_3378944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_3378944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3378944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3378944 prefixEnd_3378944 := by exact prefixLift 3378944
  have htrace : WordTrace (prefixWord ++ tailWord_3378944) baseStart_3378944 baseEnd_3378944 := by
    simpa [prefixWord, tailWord_3378944, baseEnd_3378944] using wordTrace_append hprefix tailTrace_3378944
  have hstable : (prefixWord ++ tailWord_3378944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3378944).length < 2 ^ (prefixWord ++ tailWord_3378944).sum := by decide
  have hdescent : baseEnd_3378944 < baseStart_3378944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3378944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379002 : List Nat := [3, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2]
def baseStart_3379002 : Nat := 118140960795 + 3379002 * 2 ^ 59
def prefixEnd_3379002 : Nat := 4983230072969 + 3 ^ 40 * 3379002 * 2
def baseEnd_3379002 : Nat := 1735052158503693872835259

theorem tailTrace_3379002 : CollatzResearch.WordTrace tailWord_3379002 prefixEnd_3379002 1735052158503693872835259 := by
  unfold tailWord_3379002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30810581926115079110604815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82161551802973544294946173 30810581926115079110604815)
  ·
    refine ⟨46215872889172618665907223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30810581926115079110604815 46215872889172618665907223)
    ·
      refine ⟨69323809333758927998860835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46215872889172618665907223 69323809333758927998860835)
      ·
        refine ⟨103985714000638391998291253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69323809333758927998860835 103985714000638391998291253)
        ·
          refine ⟨9748660687559849249839805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103985714000638391998291253 9748660687559849249839805)
          ·
            refine ⟨3655747757834943468689927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9748660687559849249839805 3655747757834943468689927)
            ·
              refine ⟨5483621636752415203034891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655747757834943468689927 5483621636752415203034891)
              ·
                refine ⟨8225432455128622804552337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483621636752415203034891 8225432455128622804552337)
                ·
                  refine ⟨6169074341346467103414253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8225432455128622804552337 6169074341346467103414253)
                  ·
                    refine ⟨2313402878004925163780345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6169074341346467103414253 2313402878004925163780345)
                    ·
                      refine ⟨1735052158503693872835259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313402878004925163780345 1735052158503693872835259)
                      ·
                        rfl

theorem cell23_3379002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2].length) (baseStart_3379002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379002 prefixEnd_3379002 := by exact prefixLift 3379002
  have htrace : WordTrace (prefixWord ++ tailWord_3379002) baseStart_3379002 baseEnd_3379002 := by
    simpa [prefixWord, tailWord_3379002, baseEnd_3379002] using wordTrace_append hprefix tailTrace_3379002
  have hstable : (prefixWord ++ tailWord_3379002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379002).length < 2 ^ (prefixWord ++ tailWord_3379002).sum := by decide
  have hdescent : baseEnd_3379002 < baseStart_3379002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379015 : List Nat := [1, 1, 4, 1, 2, 1, 6, 1, 1, 1, 4]
def baseStart_3379015 : Nat := 118140960795 + 3379015 * 2 ^ 59
def prefixEnd_3379015 : Nat := 4983230072969 + 3 ^ 40 * 3379015 * 2
def baseEnd_3379015 : Nat := 1735058833752202321972699

theorem tailTrace_3379015 : CollatzResearch.WordTrace tailWord_3379015 prefixEnd_3379015 1735058833752202321972699 := by
  unfold tailWord_3379015
  simp only [CollatzResearch.WordTrace]
  refine ⟨123242801853413219662642499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82161867902275479775094999 123242801853413219662642499)
  ·
    refine ⟨184864202780119829493963749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123242801853413219662642499 184864202780119829493963749)
    ·
      refine ⟨34662038021272468030118203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184864202780119829493963749 34662038021272468030118203)
      ·
        refine ⟨51993057031908702045177305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34662038021272468030118203 51993057031908702045177305)
        ·
          refine ⟨38994792773931526533882979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51993057031908702045177305 38994792773931526533882979)
          ·
            refine ⟨58492189160897289800824469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38994792773931526533882979 58492189160897289800824469)
            ·
              refine ⟨2741821366917060459413647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58492189160897289800824469 2741821366917060459413647)
              ·
                refine ⟨4112732050375590689120471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741821366917060459413647 4112732050375590689120471)
                ·
                  refine ⟨6169098075563386033680707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112732050375590689120471 6169098075563386033680707)
                  ·
                    refine ⟨9253647113345079050521061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6169098075563386033680707 9253647113345079050521061)
                    ·
                      refine ⟨1735058833752202321972699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9253647113345079050521061 1735058833752202321972699)
                      ·
                        rfl

theorem cell23_3379015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_3379015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379015 prefixEnd_3379015 := by exact prefixLift 3379015
  have htrace : WordTrace (prefixWord ++ tailWord_3379015) baseStart_3379015 baseEnd_3379015 := by
    simpa [prefixWord, tailWord_3379015, baseEnd_3379015] using wordTrace_append hprefix tailTrace_3379015
  have hstable : (prefixWord ++ tailWord_3379015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379015).length < 2 ^ (prefixWord ++ tailWord_3379015).sum := by decide
  have hdescent : baseEnd_3379015 < baseStart_3379015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379025 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 2, 4]
def baseStart_3379025 : Nat := 118140960795 + 3379025 * 2 ^ 59
def prefixEnd_3379025 : Nat := 4983230072969 + 3 ^ 40 * 3379025 * 2
def baseEnd_3379025 : Nat := 578354656186249094282551

theorem tailTrace_3379025 : CollatzResearch.WordTrace tailWord_3379025 prefixEnd_3379025 578354656186249094282551 := by
  unfold tailWord_3379025
  simp only [CollatzResearch.WordTrace]
  refine ⟨123243166583376991370506529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82162111055584660913671019 123243166583376991370506529)
  ·
    refine ⟨92432374937532743527879897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123243166583376991370506529 92432374937532743527879897)
    ·
      refine ⟨69324281203149557645909923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92432374937532743527879897 69324281203149557645909923)
      ·
        refine ⟨103986421804724336468864885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69324281203149557645909923 103986421804724336468864885)
        ·
          refine ⟨9748727044192906543956083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103986421804724336468864885 9748727044192906543956083)
          ·
            refine ⟨14623090566289359815934125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9748727044192906543956083 14623090566289359815934125)
            ·
              refine ⟨5483658962358509930975297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14623090566289359815934125 5483658962358509930975297)
              ·
                refine ⟨4112744221768882448231473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5483658962358509930975297 4112744221768882448231473)
                ·
                  refine ⟨3084558166326661836173605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4112744221768882448231473 3084558166326661836173605)
                  ·
                    refine ⟨578354656186249094282551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084558166326661836173605 578354656186249094282551)
                    ·
                      rfl

theorem cell23_3379025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_3379025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379025 prefixEnd_3379025 := by exact prefixLift 3379025
  have htrace : WordTrace (prefixWord ++ tailWord_3379025) baseStart_3379025 baseEnd_3379025 := by
    simpa [prefixWord, tailWord_3379025, baseEnd_3379025] using wordTrace_append hprefix tailTrace_3379025
  have hstable : (prefixWord ++ tailWord_3379025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379025).length < 2 ^ (prefixWord ++ tailWord_3379025).sum := by decide
  have hdescent : baseEnd_3379025 < baseStart_3379025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379071 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 4]
def baseStart_3379071 : Nat := 118140960795 + 3379071 * 2 ^ 59
def prefixEnd_3379071 : Nat := 4983230072969 + 3 ^ 40 * 3379071 * 2
def baseEnd_3379071 : Nat := 1735087588668854102872441

theorem tailTrace_3379071 : CollatzResearch.WordTrace tailWord_3379071 prefixEnd_3379071 1735087588668854102872441 := by
  unfold tailWord_3379071
  simp only [CollatzResearch.WordTrace]
  refine ⟨123244844341210341226681067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82163229560806894151120711 123244844341210341226681067)
  ·
    refine ⟨184867266511815511840021601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123244844341210341226681067 184867266511815511840021601)
    ·
      refine ⟨138650449883861633880016201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184867266511815511840021601 138650449883861633880016201)
      ·
        refine ⟨103987837412896225410012151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138650449883861633880016201 103987837412896225410012151)
        ·
          refine ⟨155981756119344338115018227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103987837412896225410012151 155981756119344338115018227)
          ·
            refine ⟨233972634179016507172527341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155981756119344338115018227 233972634179016507172527341)
            ·
              refine ⟨87739737817131190189697753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233972634179016507172527341 87739737817131190189697753)
              ·
                refine ⟨65804803362848392642273315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87739737817131190189697753 65804803362848392642273315)
                ·
                  refine ⟨98707205044272588963409973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65804803362848392642273315 98707205044272588963409973)
                  ·
                    refine ⟨9253800472900555215319685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98707205044272588963409973 9253800472900555215319685)
                    ·
                      refine ⟨1735087588668854102872441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9253800472900555215319685 1735087588668854102872441)
                      ·
                        rfl

theorem cell23_3379071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 4].length) (baseStart_3379071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379071 prefixEnd_3379071 := by exact prefixLift 3379071
  have htrace : WordTrace (prefixWord ++ tailWord_3379071) baseStart_3379071 baseEnd_3379071 := by
    simpa [prefixWord, tailWord_3379071, baseEnd_3379071] using wordTrace_append hprefix tailTrace_3379071
  have hstable : (prefixWord ++ tailWord_3379071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379071).length < 2 ^ (prefixWord ++ tailWord_3379071).sum := by decide
  have hdescent : baseEnd_3379071 < baseStart_3379071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379108 : List Nat := [2, 3, 1, 2, 1, 3, 1, 2, 2, 1, 5]
def baseStart_3379108 : Nat := 118140960795 + 3379108 * 2 ^ 59
def prefixEnd_3379108 : Nat := 4983230072969 + 3 ^ 40 * 3379108 * 2
def baseEnd_3379108 : Nat := 1735106587453070458109771

theorem tailTrace_3379108 : CollatzResearch.WordTrace tailWord_3379108 prefixEnd_3379108 1735106587453070458109771 := by
  unfold tailWord_3379108
  simp only [CollatzResearch.WordTrace]
  refine ⟨61623096921038148272888989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82164129228050864363851985 61623096921038148272888989)
  ·
    refine ⟨23108661345389305602333371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61623096921038148272888989 23108661345389305602333371)
    ·
      refine ⟨34662992018083958403500057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23108661345389305602333371 34662992018083958403500057)
      ·
        refine ⟨25997244013562968802625043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34662992018083958403500057 25997244013562968802625043)
        ·
          refine ⟨38995866020344453203937565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25997244013562968802625043 38995866020344453203937565)
          ·
            refine ⟨14623449757629169951476587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38995866020344453203937565 14623449757629169951476587)
            ·
              refine ⟨21935174636443754927214881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14623449757629169951476587 21935174636443754927214881)
              ·
                refine ⟨16451380977332816195411161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21935174636443754927214881 16451380977332816195411161)
                ·
                  refine ⟨12338535732999612146558371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16451380977332816195411161 12338535732999612146558371)
                  ·
                    refine ⟨18507803599499418219837557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12338535732999612146558371 18507803599499418219837557)
                    ·
                      refine ⟨1735106587453070458109771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18507803599499418219837557 1735106587453070458109771)
                      ·
                        rfl

theorem cell23_3379108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_3379108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379108 prefixEnd_3379108 := by exact prefixLift 3379108
  have htrace : WordTrace (prefixWord ++ tailWord_3379108) baseStart_3379108 baseEnd_3379108 := by
    simpa [prefixWord, tailWord_3379108, baseEnd_3379108] using wordTrace_append hprefix tailTrace_3379108
  have hstable : (prefixWord ++ tailWord_3379108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379108).length < 2 ^ (prefixWord ++ tailWord_3379108).sum := by decide
  have hdescent : baseEnd_3379108 < baseStart_3379108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379175 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3379175 : Nat := 118140960795 + 3379175 * 2 ^ 59
def prefixEnd_3379175 : Nat := 4983230072969 + 3 ^ 40 * 3379175 * 2
def baseEnd_3379175 : Nat := 578380330218973898657321

theorem tailTrace_3379175 : CollatzResearch.WordTrace tailWord_3379175 prefixEnd_3379175 578380330218973898657321 := by
  unfold tailWord_3379175
  simp only [CollatzResearch.WordTrace]
  refine ⟨123248637532833566988466979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82165758355222377992311319 123248637532833566988466979)
  ·
    refine ⟨184872956299250350482700469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123248637532833566988466979 184872956299250350482700469)
    ·
      refine ⟨17331839653054720357753169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184872956299250350482700469 17331839653054720357753169)
      ·
        refine ⟨12998879739791040268314877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17331839653054720357753169 12998879739791040268314877)
        ·
          refine ⟨4874579902421640100618079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12998879739791040268314877 4874579902421640100618079)
          ·
            refine ⟨7311869853632460150927119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874579902421640100618079 7311869853632460150927119)
            ·
              refine ⟨10967804780448690226390679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7311869853632460150927119 10967804780448690226390679)
              ·
                refine ⟨16451707170673035339586019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10967804780448690226390679 16451707170673035339586019)
                ·
                  refine ⟨24677560756009553009379029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16451707170673035339586019 24677560756009553009379029)
                  ·
                    refine ⟨578380330218973898657321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24677560756009553009379029 578380330218973898657321)
                    ·
                      rfl

theorem cell23_3379175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3379175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379175 prefixEnd_3379175 := by exact prefixLift 3379175
  have htrace : WordTrace (prefixWord ++ tailWord_3379175) baseStart_3379175 baseEnd_3379175 := by
    simpa [prefixWord, tailWord_3379175, baseEnd_3379175] using wordTrace_append hprefix tailTrace_3379175
  have hstable : (prefixWord ++ tailWord_3379175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379175).length < 2 ^ (prefixWord ++ tailWord_3379175).sum := by decide
  have hdescent : baseEnd_3379175 < baseStart_3379175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379195 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 2, 4, 2]
def baseStart_3379195 : Nat := 118140960795 + 3379195 * 2 ^ 59
def prefixEnd_3379195 : Nat := 4983230072969 + 3 ^ 40 * 3379195 * 2
def baseEnd_3379195 : Nat := 1735151260270011617721871

theorem tailTrace_3379195 : CollatzResearch.WordTrace tailWord_3379195 prefixEnd_3379195 1735151260270011617721871 := by
  unfold tailWord_3379195
  simp only [CollatzResearch.WordTrace]
  refine ⟨123249366992761110404195039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82166244661840740269463359 123249366992761110404195039)
  ·
    refine ⟨184874050489141665606292559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123249366992761110404195039 184874050489141665606292559)
    ·
      refine ⟨277311075733712498409438839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184874050489141665606292559 277311075733712498409438839)
      ·
        refine ⟨415966613600568747614158259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277311075733712498409438839 415966613600568747614158259)
        ·
          refine ⟨623949920400853121421237389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 415966613600568747614158259 623949920400853121421237389)
          ·
            refine ⟨233981220150319920532964021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 623949920400853121421237389 233981220150319920532964021)
            ·
              refine ⟨21935739389092492549965377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233981220150319920532964021 21935739389092492549965377)
              ·
                refine ⟨16451804541819369412474033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21935739389092492549965377 16451804541819369412474033)
                ·
                  refine ⟨12338853406364527059355525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16451804541819369412474033 12338853406364527059355525)
                  ·
                    refine ⟨2313535013693348823629161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12338853406364527059355525 2313535013693348823629161)
                    ·
                      refine ⟨1735151260270011617721871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313535013693348823629161 1735151260270011617721871)
                      ·
                        rfl

theorem cell23_3379195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 4, 2].length) (baseStart_3379195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379195 prefixEnd_3379195 := by exact prefixLift 3379195
  have htrace : WordTrace (prefixWord ++ tailWord_3379195) baseStart_3379195 baseEnd_3379195 := by
    simpa [prefixWord, tailWord_3379195, baseEnd_3379195] using wordTrace_append hprefix tailTrace_3379195
  have hstable : (prefixWord ++ tailWord_3379195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379195).length < 2 ^ (prefixWord ++ tailWord_3379195).sum := by decide
  have hdescent : baseEnd_3379195 < baseStart_3379195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379205 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 3, 4]
def baseStart_3379205 : Nat := 118140960795 + 3379205 * 2 ^ 59
def prefixEnd_3379205 : Nat := 4983230072969 + 3 ^ 40 * 3379205 * 2
def baseEnd_3379205 : Nat := 578385465025518859532275

theorem tailTrace_3379205 : CollatzResearch.WordTrace tailWord_3379205 prefixEnd_3379205 578385465025518859532275 := by
  unfold tailWord_3379205
  simp only [CollatzResearch.WordTrace]
  refine ⟨123249731722724882112059069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82166487815149921408039379 123249731722724882112059069)
  ·
    refine ⟨46218649396021830792022151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123249731722724882112059069 46218649396021830792022151)
    ·
      refine ⟨69327974094032746188033227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46218649396021830792022151 69327974094032746188033227)
      ·
        refine ⟨103991961141049119282049841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69327974094032746188033227 103991961141049119282049841)
        ·
          refine ⟨77993970855786839461537381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103991961141049119282049841 77993970855786839461537381)
          ·
            refine ⟨14623869535460032399038259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77993970855786839461537381 14623869535460032399038259)
            ·
              refine ⟨21935804303190048598557389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14623869535460032399038259 21935804303190048598557389)
              ·
                refine ⟨8225926613696268224459021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21935804303190048598557389 8225926613696268224459021)
                ·
                  refine ⟨3084722480136100584172133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8225926613696268224459021 3084722480136100584172133)
                  ·
                    refine ⟨578385465025518859532275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084722480136100584172133 578385465025518859532275)
                    ·
                      rfl

theorem cell23_3379205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_3379205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379205 prefixEnd_3379205 := by exact prefixLift 3379205
  have htrace : WordTrace (prefixWord ++ tailWord_3379205) baseStart_3379205 baseEnd_3379205 := by
    simpa [prefixWord, tailWord_3379205, baseEnd_3379205] using wordTrace_append hprefix tailTrace_3379205
  have hstable : (prefixWord ++ tailWord_3379205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379205).length < 2 ^ (prefixWord ++ tailWord_3379205).sum := by decide
  have hdescent : baseEnd_3379205 < baseStart_3379205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379208 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3379208 : Nat := 118140960795 + 3379208 * 2 ^ 59
def prefixEnd_3379208 : Nat := 4983230072969 + 3 ^ 40 * 3379208 * 2
def baseEnd_3379208 : Nat := 1735157935518520066859311

theorem tailTrace_3379208 : CollatzResearch.WordTrace tailWord_3379208 prefixEnd_3379208 1735157935518520066859311 := by
  unfold tailWord_3379208
  simp only [CollatzResearch.WordTrace]
  refine ⟨61624920570857006812209139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82166560761142675749612185 61624920570857006812209139)
  ·
    refine ⟨92437380856285510218313709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61624920570857006812209139 92437380856285510218313709)
    ·
      refine ⟨34664017821107066331867641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92437380856285510218313709 34664017821107066331867641)
      ·
        refine ⟨25998013365830299748900731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34664017821107066331867641 25998013365830299748900731)
        ·
          refine ⟨38997020048745449623351097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25998013365830299748900731 38997020048745449623351097)
          ·
            refine ⟨29247765036559087217513323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38997020048745449623351097 29247765036559087217513323)
            ·
              refine ⟨43871647554838630826269985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29247765036559087217513323 43871647554838630826269985)
              ·
                refine ⟨32903735666128973119702489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43871647554838630826269985 32903735666128973119702489)
                ·
                  refine ⟨24677801749596729839776867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32903735666128973119702489 24677801749596729839776867)
                  ·
                    refine ⟨37016702624395094759665301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24677801749596729839776867 37016702624395094759665301)
                    ·
                      refine ⟨1735157935518520066859311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37016702624395094759665301 1735157935518520066859311)
                      ·
                        rfl

theorem cell23_3379208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3379208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379208 prefixEnd_3379208 := by exact prefixLift 3379208
  have htrace : WordTrace (prefixWord ++ tailWord_3379208) baseStart_3379208 baseEnd_3379208 := by
    simpa [prefixWord, tailWord_3379208, baseEnd_3379208] using wordTrace_append hprefix tailTrace_3379208
  have hstable : (prefixWord ++ tailWord_3379208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379208).length < 2 ^ (prefixWord ++ tailWord_3379208).sum := by decide
  have hdescent : baseEnd_3379208 < baseStart_3379208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379256 : List Nat := [2, 1, 2, 1, 6, 1, 3, 2, 1, 4]
def baseStart_3379256 : Nat := 118140960795 + 3379256 * 2 ^ 59
def prefixEnd_3379256 : Nat := 4983230072969 + 3 ^ 40 * 3379256 * 2
def baseEnd_3379256 : Nat := 578394194196645293019697

theorem tailTrace_3379256 : CollatzResearch.WordTrace tailWord_3379256 prefixEnd_3379256 578394194196645293019697 := by
  unfold tailWord_3379256
  simp only [CollatzResearch.WordTrace]
  refine ⟨61625795922770058911082811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82167727897026745214777081 61625795922770058911082811)
  ·
    refine ⟨92438693884155088366624217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61625795922770058911082811 92438693884155088366624217)
    ·
      refine ⟨69329020413116316274968163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92438693884155088366624217 69329020413116316274968163)
      ·
        refine ⟨103993530619674474412452245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69329020413116316274968163 103993530619674474412452245)
        ·
          refine ⟨4874696747797240988083699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103993530619674474412452245 4874696747797240988083699)
          ·
            refine ⟨7312045121695861482125549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874696747797240988083699 7312045121695861482125549)
            ·
              refine ⟨2742016920635948055797081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7312045121695861482125549 2742016920635948055797081)
              ·
                refine ⟨2056512690476961041847811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742016920635948055797081 2056512690476961041847811)
                ·
                  refine ⟨3084769035715441562771717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056512690476961041847811 3084769035715441562771717)
                  ·
                    refine ⟨578394194196645293019697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084769035715441562771717 578394194196645293019697)
                    ·
                      rfl

theorem cell23_3379256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_3379256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379256 prefixEnd_3379256 := by exact prefixLift 3379256
  have htrace : WordTrace (prefixWord ++ tailWord_3379256) baseStart_3379256 baseEnd_3379256 := by
    simpa [prefixWord, tailWord_3379256, baseEnd_3379256] using wordTrace_append hprefix tailTrace_3379256
  have hstable : (prefixWord ++ tailWord_3379256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379256).length < 2 ^ (prefixWord ++ tailWord_3379256).sum := by decide
  have hdescent : baseEnd_3379256 < baseStart_3379256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379258 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_3379258 : Nat := 118140960795 + 3379258 * 2 ^ 59
def prefixEnd_3379258 : Nat := 4983230072969 + 3 ^ 40 * 3379258 * 2
def baseEnd_3379258 : Nat := 1735183609551244871234081

theorem tailTrace_3379258 : CollatzResearch.WordTrace tailWord_3379258 prefixEnd_3379258 1735183609551244871234081 := by
  unfold tailWord_3379258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30812916197883218040934607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82167776527688581442492285 30812916197883218040934607)
  ·
    refine ⟨46219374296824827061401911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30812916197883218040934607 46219374296824827061401911)
    ·
      refine ⟨69329061445237240592102867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46219374296824827061401911 69329061445237240592102867)
      ·
        refine ⟨103993592167855860888154301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69329061445237240592102867 103993592167855860888154301)
        ·
          refine ⟨38997597062945947833057863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103993592167855860888154301 38997597062945947833057863)
          ·
            refine ⟨58496395594418921749586795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38997597062945947833057863 58496395594418921749586795)
            ·
              refine ⟨87744593391628382624380193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58496395594418921749586795 87744593391628382624380193)
              ·
                refine ⟨65808445043721286968285145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87744593391628382624380193 65808445043721286968285145)
                ·
                  refine ⟨49356333782790965226213859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65808445043721286968285145 49356333782790965226213859)
                  ·
                    refine ⟨74034500674186447839320789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49356333782790965226213859 74034500674186447839320789)
                    ·
                      refine ⟨1735183609551244871234081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74034500674186447839320789 1735183609551244871234081)
                      ·
                        rfl

theorem cell23_3379258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_3379258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379258 prefixEnd_3379258 := by exact prefixLift 3379258
  have htrace : WordTrace (prefixWord ++ tailWord_3379258) baseStart_3379258 baseEnd_3379258 := by
    simpa [prefixWord, tailWord_3379258, baseEnd_3379258] using wordTrace_append hprefix tailTrace_3379258
  have hstable : (prefixWord ++ tailWord_3379258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379258).length < 2 ^ (prefixWord ++ tailWord_3379258).sum := by decide
  have hdescent : baseEnd_3379258 < baseStart_3379258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379282 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 3, 5]
def baseStart_3379282 : Nat := 118140960795 + 3379282 * 2 ^ 59
def prefixEnd_3379282 : Nat := 4983230072969 + 3 ^ 40 * 3379282 * 2
def baseEnd_3379282 : Nat := 578398644362317592444657

theorem tailTrace_3379282 : CollatzResearch.WordTrace tailWord_3379282 prefixEnd_3379282 578398644362317592444657 := by
  unfold tailWord_3379282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30813135035861481065653025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82168360095630616175074733 30813135035861481065653025)
  ·
    refine ⟨23109851276896110799239769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30813135035861481065653025 23109851276896110799239769)
    ·
      refine ⟨17332388457672083099429827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23109851276896110799239769 17332388457672083099429827)
      ·
        refine ⟨25998582686508124649144741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17332388457672083099429827 25998582686508124649144741)
        ·
          refine ⟨4874734253720273371714639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25998582686508124649144741 4874734253720273371714639)
          ·
            refine ⟨7312101380580410057571959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874734253720273371714639 7312101380580410057571959)
            ·
              refine ⟨10968152070870615086357939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312101380580410057571959 10968152070870615086357939)
              ·
                refine ⟨16452228106305922629536909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10968152070870615086357939 16452228106305922629536909)
                ·
                  refine ⟨6169585539864720986076341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16452228106305922629536909 6169585539864720986076341)
                  ·
                    refine ⟨578398644362317592444657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6169585539864720986076341 578398644362317592444657)
                    ·
                      rfl

theorem cell23_3379282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_3379282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379282 prefixEnd_3379282 := by exact prefixLift 3379282
  have htrace : WordTrace (prefixWord ++ tailWord_3379282) baseStart_3379282 baseEnd_3379282 := by
    simpa [prefixWord, tailWord_3379282, baseEnd_3379282] using wordTrace_append hprefix tailTrace_3379282
  have hstable : (prefixWord ++ tailWord_3379282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379282).length < 2 ^ (prefixWord ++ tailWord_3379282).sum := by decide
  have hdescent : baseEnd_3379282 < baseStart_3379282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379295 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 4, 4]
def baseStart_3379295 : Nat := 118140960795 + 3379295 * 2 ^ 59
def prefixEnd_3379295 : Nat := 4983230072969 + 3 ^ 40 * 3379295 * 2
def baseEnd_3379295 : Nat := 578400869445153742157137

theorem tailTrace_3379295 : CollatzResearch.WordTrace tailWord_3379295 prefixEnd_3379295 578400869445153742157137 := by
  unfold tailWord_3379295
  simp only [CollatzResearch.WordTrace]
  refine ⟨123253014292398827482835339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82168676194932551655223559 123253014292398827482835339)
  ·
    refine ⟨184879521438598241224253009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123253014292398827482835339 184879521438598241224253009)
    ·
      refine ⟨138659641078948680918189757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184879521438598241224253009 138659641078948680918189757)
      ·
        refine ⟨51997365404605755344321159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138659641078948680918189757 51997365404605755344321159)
        ·
          refine ⟨77996048106908633016481739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51997365404605755344321159 77996048106908633016481739)
          ·
            refine ⟨116994072160362949524722609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77996048106908633016481739 116994072160362949524722609)
            ·
              refine ⟨87745554120272212143541957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116994072160362949524722609 87745554120272212143541957)
              ·
                refine ⟨16452291397551039776914117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87745554120272212143541957 16452291397551039776914117)
                ·
                  refine ⟨3084804637040819958171397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16452291397551039776914117 3084804637040819958171397)
                  ·
                    refine ⟨578400869445153742157137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084804637040819958171397 578400869445153742157137)
                    ·
                      rfl

theorem cell23_3379295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_3379295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379295 prefixEnd_3379295 := by exact prefixLift 3379295
  have htrace : WordTrace (prefixWord ++ tailWord_3379295) baseStart_3379295 baseEnd_3379295 := by
    simpa [prefixWord, tailWord_3379295, baseEnd_3379295] using wordTrace_append hprefix tailTrace_3379295
  have hstable : (prefixWord ++ tailWord_3379295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379295).length < 2 ^ (prefixWord ++ tailWord_3379295).sum := by decide
  have hdescent : baseEnd_3379295 < baseStart_3379295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379308 : List Nat := [2, 2, 1, 1, 3, 14]
def baseStart_3379308 : Nat := 118140960795 + 3379308 * 2 ^ 59
def prefixEnd_3379308 : Nat := 4983230072969 + 3 ^ 40 * 3379308 * 2
def baseEnd_3379308 : Nat := 7140778944789998665057

theorem tailTrace_3379308 : CollatzResearch.WordTrace tailWord_3379308 prefixEnd_3379308 7140778944789998665057 := by
  unfold tailWord_3379308
  simp only [CollatzResearch.WordTrace]
  refine ⟨61626744220675865351529289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82168992294234487135372385 61626744220675865351529289)
  ·
    refine ⟨46220058165506899013646967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61626744220675865351529289 46220058165506899013646967)
    ·
      refine ⟨69330087248260348520470451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46220058165506899013646967 69330087248260348520470451)
      ·
        refine ⟨103995130872390522780705677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69330087248260348520470451 103995130872390522780705677)
        ·
          refine ⟨38998174077146446042764629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103995130872390522780705677 38998174077146446042764629)
          ·
            refine ⟨7140778944789998665057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 38998174077146446042764629 7140778944789998665057)
            ·
              rfl

theorem cell23_3379308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 14].length) (baseStart_3379308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379308 prefixEnd_3379308 := by exact prefixLift 3379308
  have htrace : WordTrace (prefixWord ++ tailWord_3379308) baseStart_3379308 baseEnd_3379308 := by
    simpa [prefixWord, tailWord_3379308, baseEnd_3379308] using wordTrace_append hprefix tailTrace_3379308
  have hstable : (prefixWord ++ tailWord_3379308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379308).length < 2 ^ (prefixWord ++ tailWord_3379308).sum := by decide
  have hdescent : baseEnd_3379308 < baseStart_3379308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379312 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 2, 4]
def baseStart_3379312 : Nat := 118140960795 + 3379312 * 2 ^ 59
def prefixEnd_3379312 : Nat := 4983230072969 + 3 ^ 40 * 3379312 * 2
def baseEnd_3379312 : Nat := 578403779168862553319611

theorem tailTrace_3379312 : CollatzResearch.WordTrace tailWord_3379312 prefixEnd_3379312 578403779168862553319611 := by
  unfold tailWord_3379312
  simp only [CollatzResearch.WordTrace]
  refine ⟨61626817166668619693102095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82169089555558159590802793 61626817166668619693102095)
  ·
    refine ⟨92440225750002929539653143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61626817166668619693102095 92440225750002929539653143)
    ·
      refine ⟨138660338625004394309479715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92440225750002929539653143 138660338625004394309479715)
      ·
        refine ⟨207990507937506591464219573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138660338625004394309479715 207990507937506591464219573)
        ·
          refine ⟨19499110119141242949770585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207990507937506591464219573 19499110119141242949770585)
          ·
            refine ⟨14624332589355932212327939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19499110119141242949770585 14624332589355932212327939)
            ·
              refine ⟨21936498884033898318491909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14624332589355932212327939 21936498884033898318491909)
              ·
                refine ⟨4113093540756355934717233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21936498884033898318491909 4113093540756355934717233)
                ·
                  refine ⟨3084820155567266951037925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113093540756355934717233 3084820155567266951037925)
                  ·
                    refine ⟨578403779168862553319611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084820155567266951037925 578403779168862553319611)
                    ·
                      rfl

theorem cell23_3379312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 2, 4].length) (baseStart_3379312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379312 prefixEnd_3379312 := by exact prefixLift 3379312
  have htrace : WordTrace (prefixWord ++ tailWord_3379312) baseStart_3379312 baseEnd_3379312 := by
    simpa [prefixWord, tailWord_3379312, baseEnd_3379312] using wordTrace_append hprefix tailTrace_3379312
  have hstable : (prefixWord ++ tailWord_3379312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379312).length < 2 ^ (prefixWord ++ tailWord_3379312).sum := by decide
  have hdescent : baseEnd_3379312 < baseStart_3379312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379325 : List Nat := [1, 4, 1, 1, 3, 2, 3, 8]
def baseStart_3379325 : Nat := 118140960795 + 3379325 * 2 ^ 59
def prefixEnd_3379325 : Nat := 4983230072969 + 3 ^ 40 * 3379325 * 2
def baseEnd_3379325 : Nat := 64267333805744300336899

theorem tailTrace_3379325 : CollatzResearch.WordTrace tailWord_3379325 prefixEnd_3379325 64267333805744300336899 := by
  unfold tailWord_3379325
  simp only [CollatzResearch.WordTrace]
  refine ⟨123254108482290142606427429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82169405654860095070951619 123254108482290142606427429)
  ·
    refine ⟨23110145340429401738705143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123254108482290142606427429 23110145340429401738705143)
    ·
      refine ⟨34665218010644102608057715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23110145340429401738705143 34665218010644102608057715)
      ·
        refine ⟨51997827015966153912086573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34665218010644102608057715 51997827015966153912086573)
        ·
          refine ⟨19499185130987307717032465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51997827015966153912086573 19499185130987307717032465)
          ·
            refine ⟨14624388848240480787774349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19499185130987307717032465 14624388848240480787774349)
            ·
              refine ⟨5484145818090180295415381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14624388848240480787774349 5484145818090180295415381)
              ·
                refine ⟨64267333805744300336899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5484145818090180295415381 64267333805744300336899)
                ·
                  rfl

theorem cell23_3379325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 8].length) (baseStart_3379325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379325 prefixEnd_3379325 := by exact prefixLift 3379325
  have htrace : WordTrace (prefixWord ++ tailWord_3379325) baseStart_3379325 baseEnd_3379325 := by
    simpa [prefixWord, tailWord_3379325, baseEnd_3379325] using wordTrace_append hprefix tailTrace_3379325
  have hstable : (prefixWord ++ tailWord_3379325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379325).length < 2 ^ (prefixWord ++ tailWord_3379325).sum := by decide
  have hdescent : baseEnd_3379325 < baseStart_3379325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379332 : List Nat := [2, 3, 2, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_3379332 : Nat := 118140960795 + 3379332 * 2 ^ 59
def prefixEnd_3379332 : Nat := 4983230072969 + 3 ^ 40 * 3379332 * 2
def baseEnd_3379332 : Nat := 1735221607119677581708741

theorem tailTrace_3379332 : CollatzResearch.WordTrace tailWord_3379332 prefixEnd_3379332 1735221607119677581708741 := by
  unfold tailWord_3379332
  simp only [CollatzResearch.WordTrace]
  refine ⟨61627181896632391400966125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82169575862176521867954833 61627181896632391400966125)
  ·
    refine ⟨23110193211237146775362297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61627181896632391400966125 23110193211237146775362297)
    ·
      refine ⟨17332644908427860081521723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23110193211237146775362297 17332644908427860081521723)
      ·
        refine ⟨25998967362641790122282585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17332644908427860081521723 25998967362641790122282585)
        ·
          refine ⟨19499225521981342591711939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25998967362641790122282585 19499225521981342591711939)
          ·
            refine ⟨29248838282972013887567909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499225521981342591711939 29248838282972013887567909)
            ·
              refine ⟨5484157178057252603918983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29248838282972013887567909 5484157178057252603918983)
              ·
                refine ⟨8226235767085878905878475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484157178057252603918983 8226235767085878905878475)
                ·
                  refine ⟨12339353650628818358817713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8226235767085878905878475 12339353650628818358817713)
                  ·
                    refine ⟨9254515237971613769113285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12339353650628818358817713 9254515237971613769113285)
                    ·
                      refine ⟨1735221607119677581708741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9254515237971613769113285 1735221607119677581708741)
                      ·
                        rfl

theorem cell23_3379332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_3379332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379332 prefixEnd_3379332 := by exact prefixLift 3379332
  have htrace : WordTrace (prefixWord ++ tailWord_3379332) baseStart_3379332 baseEnd_3379332 := by
    simpa [prefixWord, tailWord_3379332, baseEnd_3379332] using wordTrace_append hprefix tailTrace_3379332
  have hstable : (prefixWord ++ tailWord_3379332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379332).length < 2 ^ (prefixWord ++ tailWord_3379332).sum := by decide
  have hdescent : baseEnd_3379332 < baseStart_3379332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379336 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 3, 2, 2]
def baseStart_3379336 : Nat := 118140960795 + 3379336 * 2 ^ 59
def prefixEnd_3379336 : Nat := 4983230072969 + 3 ^ 40 * 3379336 * 2
def baseEnd_3379336 : Nat := 1735223661042295566058723

theorem tailTrace_3379336 : CollatzResearch.WordTrace tailWord_3379336 prefixEnd_3379336 1735223661042295566058723 := by
  unfold tailWord_3379336
  simp only [CollatzResearch.WordTrace]
  refine ⟨61627254842625145742538931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82169673123500194323385241 61627254842625145742538931)
  ·
    refine ⟨92440882263937718613808397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61627254842625145742538931 92440882263937718613808397)
    ·
      refine ⟨34665330848976644480178149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92440882263937718613808397 34665330848976644480178149)
      ·
        refine ⟨6499749534183120840033403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34665330848976644480178149 6499749534183120840033403)
        ·
          refine ⟨9749624301274681260050105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6499749534183120840033403 9749624301274681260050105)
          ·
            refine ⟨7312218225956010945037579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9749624301274681260050105 7312218225956010945037579)
            ·
              refine ⟨10968327338934016417556369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312218225956010945037579 10968327338934016417556369)
              ·
                refine ⟨8226245504200512313167277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10968327338934016417556369 8226245504200512313167277)
                ·
                  refine ⟨3084842064075192117437729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8226245504200512313167277 3084842064075192117437729)
                  ·
                    refine ⟨2313631548056394088078297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084842064075192117437729 2313631548056394088078297)
                    ·
                      refine ⟨1735223661042295566058723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313631548056394088078297 1735223661042295566058723)
                      ·
                        rfl

theorem cell23_3379336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_3379336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379336 prefixEnd_3379336 := by exact prefixLift 3379336
  have htrace : WordTrace (prefixWord ++ tailWord_3379336) baseStart_3379336 baseEnd_3379336 := by
    simpa [prefixWord, tailWord_3379336, baseEnd_3379336] using wordTrace_append hprefix tailTrace_3379336
  have hstable : (prefixWord ++ tailWord_3379336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379336).length < 2 ^ (prefixWord ++ tailWord_3379336).sum := by decide
  have hdescent : baseEnd_3379336 < baseStart_3379336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379350 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3379350 : Nat := 118140960795 + 3379350 * 2 ^ 59
def prefixEnd_3379350 : Nat := 4983230072969 + 3 ^ 40 * 3379350 * 2
def baseEnd_3379350 : Nat := 578410283257152837094553

theorem tailTrace_3379350 : CollatzResearch.WordTrace tailWord_3379350 prefixEnd_3379350 578410283257152837094553 := by
  unfold tailWord_3379350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703438769199973242255469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82170013538133047917391669 7703438769199973242255469)
  ·
    refine ⟨2888789538449989965845801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7703438769199973242255469 2888789538449989965845801)
    ·
      refine ⟨2166592153837492474384351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2888789538449989965845801 2166592153837492474384351)
      ·
        refine ⟨3249888230756238711576527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166592153837492474384351 3249888230756238711576527)
        ·
          refine ⟨4874832346134358067364791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249888230756238711576527 4874832346134358067364791)
          ·
            refine ⟨7312248519201537101047187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874832346134358067364791 7312248519201537101047187)
            ·
              refine ⟨10968372778802305651570781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312248519201537101047187 10968372778802305651570781)
              ·
                refine ⟨4113139792050864619339043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10968372778802305651570781 4113139792050864619339043)
                ·
                  refine ⟨6169709688076296929008565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113139792050864619339043 6169709688076296929008565)
                  ·
                    refine ⟨578410283257152837094553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6169709688076296929008565 578410283257152837094553)
                    ·
                      rfl

theorem cell23_3379350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3379350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379350 prefixEnd_3379350 := by exact prefixLift 3379350
  have htrace : WordTrace (prefixWord ++ tailWord_3379350) baseStart_3379350 baseEnd_3379350 := by
    simpa [prefixWord, tailWord_3379350, baseEnd_3379350] using wordTrace_append hprefix tailTrace_3379350
  have hstable : (prefixWord ++ tailWord_3379350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379350).length < 2 ^ (prefixWord ++ tailWord_3379350).sum := by decide
  have hdescent : baseEnd_3379350 < baseStart_3379350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379380 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3379380 : Nat := 118140960795 + 3379380 * 2 ^ 59
def prefixEnd_3379380 : Nat := 4983230072969 + 3 ^ 40 * 3379380 * 2
def baseEnd_3379380 : Nat := 578415418063697797969507

theorem tailTrace_3379380 : CollatzResearch.WordTrace tailWord_3379380 prefixEnd_3379380 578415418063697797969507 := by
  unfold tailWord_3379380
  simp only [CollatzResearch.WordTrace]
  refine ⟨61628057248545443499839797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82170742998060591333119729 61628057248545443499839797)
  ·
    refine ⟨5777630367051135328109981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61628057248545443499839797 5777630367051135328109981)
    ·
      refine ⟨2166611387644175748041243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5777630367051135328109981 2166611387644175748041243)
      ·
        refine ⟨3249917081466263622061865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2166611387644175748041243 3249917081466263622061865)
        ·
          refine ⟨2437437811099697716546399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3249917081466263622061865 2437437811099697716546399)
          ·
            refine ⟨3656156716649546574819599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437437811099697716546399 3656156716649546574819599)
            ·
              refine ⟨5484235074974319862229399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656156716649546574819599 5484235074974319862229399)
              ·
                refine ⟨8226352612461479793344099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484235074974319862229399 8226352612461479793344099)
                ·
                  refine ⟨12339528918692219690016149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8226352612461479793344099 12339528918692219690016149)
                  ·
                    refine ⟨578415418063697797969507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12339528918692219690016149 578415418063697797969507)
                    ·
                      rfl

theorem cell23_3379380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3379380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379380 prefixEnd_3379380 := by exact prefixLift 3379380
  have htrace : WordTrace (prefixWord ++ tailWord_3379380) baseStart_3379380 baseEnd_3379380 := by
    simpa [prefixWord, tailWord_3379380, baseEnd_3379380] using wordTrace_append hprefix tailTrace_3379380
  have hstable : (prefixWord ++ tailWord_3379380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379380).length < 2 ^ (prefixWord ++ tailWord_3379380).sum := by decide
  have hdescent : baseEnd_3379380 < baseStart_3379380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379385 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 2, 6]
def baseStart_3379385 : Nat := 118140960795 + 3379385 * 2 ^ 59
def prefixEnd_3379385 : Nat := 4983230072969 + 3 ^ 40 * 3379385 * 2
def baseEnd_3379385 : Nat := 578416273864788624781999

theorem tailTrace_3379385 : CollatzResearch.WordTrace tailWord_3379385 prefixEnd_3379385 578416273864788624781999 := by
  unfold tailWord_3379385
  simp only [CollatzResearch.WordTrace]
  refine ⟨123256296862072772853611609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82170864574715181902407739 123256296862072772853611609)
  ·
    refine ⟨92442222646554579640208707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123256296862072772853611609 92442222646554579640208707)
    ·
      refine ⟨138663333969831869460313061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92442222646554579640208707 138663333969831869460313061)
      ·
        refine ⟨25999375119343475523808699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138663333969831869460313061 25999375119343475523808699)
        ·
          refine ⟨38999062679015213285713049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25999375119343475523808699 38999062679015213285713049)
          ·
            refine ⟨29249297009261409964284787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38999062679015213285713049 29249297009261409964284787)
            ·
              refine ⟨43873945513892114946427181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29249297009261409964284787 43873945513892114946427181)
              ·
                refine ⟨16452729567709543104910193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43873945513892114946427181 16452729567709543104910193)
                ·
                  refine ⟨12339547175782157328682645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16452729567709543104910193 12339547175782157328682645)
                  ·
                    refine ⟨578416273864788624781999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12339547175782157328682645 578416273864788624781999)
                    ·
                      rfl

theorem cell23_3379385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 2, 6].length) (baseStart_3379385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379385 prefixEnd_3379385 := by exact prefixLift 3379385
  have htrace : WordTrace (prefixWord ++ tailWord_3379385) baseStart_3379385 baseEnd_3379385 := by
    simpa [prefixWord, tailWord_3379385, baseEnd_3379385] using wordTrace_append hprefix tailTrace_3379385
  have hstable : (prefixWord ++ tailWord_3379385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379385).length < 2 ^ (prefixWord ++ tailWord_3379385).sum := by decide
  have hdescent : baseEnd_3379385 < baseStart_3379385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379395 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 3]
def baseStart_3379395 : Nat := 118140960795 + 3379395 * 2 ^ 59
def prefixEnd_3379395 : Nat := 4983230072969 + 3 ^ 40 * 3379395 * 2
def baseEnd_3379395 : Nat := 1735253956400910835220951

theorem tailTrace_3379395 : CollatzResearch.WordTrace tailWord_3379395 prefixEnd_3379395 1735253956400910835220951 := by
  unfold tailWord_3379395
  simp only [CollatzResearch.WordTrace]
  refine ⟨123256661592036544561475639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82171107728024363040983759 123256661592036544561475639)
  ·
    refine ⟨184884992388054816842213459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123256661592036544561475639 184884992388054816842213459)
    ·
      refine ⟨277327488582082225263320189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184884992388054816842213459 277327488582082225263320189)
      ·
        refine ⟨103997808218280834473745071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277327488582082225263320189 103997808218280834473745071)
        ·
          refine ⟨155996712327421251710617607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103997808218280834473745071 155996712327421251710617607)
          ·
            refine ⟨233995068491131877565926411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155996712327421251710617607 233995068491131877565926411)
            ·
              refine ⟨350992602736697816348889617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233995068491131877565926411 350992602736697816348889617)
              ·
                refine ⟨263244452052523362261667213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350992602736697816348889617 263244452052523362261667213)
                ·
                  refine ⟨98716669519696260848125205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263244452052523362261667213 98716669519696260848125205)
                  ·
                    refine ⟨4627343883735762227255869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98716669519696260848125205 4627343883735762227255869)
                    ·
                      refine ⟨1735253956400910835220951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4627343883735762227255869 1735253956400910835220951)
                      ·
                        rfl

theorem cell23_3379395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_3379395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379395 prefixEnd_3379395 := by exact prefixLift 3379395
  have htrace : WordTrace (prefixWord ++ tailWord_3379395) baseStart_3379395 baseEnd_3379395 := by
    simpa [prefixWord, tailWord_3379395, baseEnd_3379395] using wordTrace_append hprefix tailTrace_3379395
  have hstable : (prefixWord ++ tailWord_3379395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379395).length < 2 ^ (prefixWord ++ tailWord_3379395).sum := by decide
  have hdescent : baseEnd_3379395 < baseStart_3379395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379396 : List Nat := [2, 3, 3, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_3379396 : Nat := 118140960795 + 3379396 * 2 ^ 59
def prefixEnd_3379396 : Nat := 4983230072969 + 3 ^ 40 * 3379396 * 2
def baseEnd_3379396 : Nat := 1735254469881565331308447

theorem tailTrace_3379396 : CollatzResearch.WordTrace tailWord_3379396 prefixEnd_3379396 1735254469881565331308447 := by
  unfold tailWord_3379396
  simp only [CollatzResearch.WordTrace]
  refine ⟨61628349032516460866131021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82171132043355281154841361 61628349032516460866131021)
  ·
    refine ⟨23110630887193672824799133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61628349032516460866131021 23110630887193672824799133)
    ·
      refine ⟨8666486582697627309299675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23110630887193672824799133 8666486582697627309299675)
      ·
        refine ⟨12999729874046440963949513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666486582697627309299675 12999729874046440963949513)
        ·
          refine ⟨9749797405534830722962135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12999729874046440963949513 9749797405534830722962135)
          ·
            refine ⟨14624696108302246084443203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9749797405534830722962135 14624696108302246084443203)
            ·
              refine ⟨21937044162453369126664805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14624696108302246084443203 21937044162453369126664805)
              ·
                refine ⟨4113195780460006711249651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21937044162453369126664805 4113195780460006711249651)
                ·
                  refine ⟨6169793670690010066874477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113195780460006711249651 6169793670690010066874477)
                  ·
                    refine ⟨2313672626508753775077929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6169793670690010066874477 2313672626508753775077929)
                    ·
                      refine ⟨1735254469881565331308447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313672626508753775077929 1735254469881565331308447)
                      ·
                        rfl

theorem cell23_3379396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_3379396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379396 prefixEnd_3379396 := by exact prefixLift 3379396
  have htrace : WordTrace (prefixWord ++ tailWord_3379396) baseStart_3379396 baseEnd_3379396 := by
    simpa [prefixWord, tailWord_3379396, baseEnd_3379396] using wordTrace_append hprefix tailTrace_3379396
  have hstable : (prefixWord ++ tailWord_3379396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379396).length < 2 ^ (prefixWord ++ tailWord_3379396).sum := by decide
  have hdescent : baseEnd_3379396 < baseStart_3379396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379409 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 4, 2, 2]
def baseStart_3379409 : Nat := 118140960795 + 3379409 * 2 ^ 59
def prefixEnd_3379409 : Nat := 4983230072969 + 3 ^ 40 * 3379409 * 2
def baseEnd_3379409 : Nat := 1735261145130073780445887

theorem tailTrace_3379409 : CollatzResearch.WordTrace tailWord_3379409 prefixEnd_3379409 1735261145130073780445887 := by
  unfold tailWord_3379409
  simp only [CollatzResearch.WordTrace]
  refine ⟨123257172213985824952485281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82171448142657216634990187 123257172213985824952485281)
  ·
    refine ⟨92442879160489368714363961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123257172213985824952485281 92442879160489368714363961)
    ·
      refine ⟨69332159370367026535772971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92442879160489368714363961 69332159370367026535772971)
      ·
        refine ⟨103998239055550539803659457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69332159370367026535772971 103998239055550539803659457)
        ·
          refine ⟨77998679291662904852744593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103998239055550539803659457 77998679291662904852744593)
          ·
            refine ⟨58499009468747178639558445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77998679291662904852744593 58499009468747178639558445)
            ·
              refine ⟨21937128550780191989834417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58499009468747178639558445 21937128550780191989834417)
              ·
                refine ⟨16452846413085143992375813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21937128550780191989834417 16452846413085143992375813)
                ·
                  refine ⟨3084908702453464498570465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16452846413085143992375813 3084908702453464498570465)
                  ·
                    refine ⟨2313681526840098373927849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3084908702453464498570465 2313681526840098373927849)
                    ·
                      refine ⟨1735261145130073780445887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313681526840098373927849 1735261145130073780445887)
                      ·
                        rfl

theorem cell23_3379409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_3379409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379409 prefixEnd_3379409 := by exact prefixLift 3379409
  have htrace : WordTrace (prefixWord ++ tailWord_3379409) baseStart_3379409 baseEnd_3379409 := by
    simpa [prefixWord, tailWord_3379409, baseEnd_3379409] using wordTrace_append hprefix tailTrace_3379409
  have hstable : (prefixWord ++ tailWord_3379409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379409).length < 2 ^ (prefixWord ++ tailWord_3379409).sum := by decide
  have hdescent : baseEnd_3379409 < baseStart_3379409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379425 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_3379425 : Nat := 118140960795 + 3379425 * 2 ^ 59
def prefixEnd_3379425 : Nat := 4983230072969 + 3 ^ 40 * 3379425 * 2
def baseEnd_3379425 : Nat := 1735269360820545717845813

theorem tailTrace_3379425 : CollatzResearch.WordTrace tailWord_3379425 prefixEnd_3379425 1735269360820545717845813 := by
  unfold tailWord_3379425
  simp only [CollatzResearch.WordTrace]
  refine ⟨123257755781927859685067729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82171837187951906456711819 123257755781927859685067729)
  ·
    refine ⟨92443316836445894763800797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123257755781927859685067729 92443316836445894763800797)
    ·
      refine ⟨34666243813667210536425299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92443316836445894763800797 34666243813667210536425299)
      ·
        refine ⟨51999365720500815804637949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34666243813667210536425299 51999365720500815804637949)
        ·
          refine ⟨19499762145187805926739231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51999365720500815804637949 19499762145187805926739231)
          ·
            refine ⟨29249643217781708890108847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499762145187805926739231 29249643217781708890108847)
            ·
              refine ⟨43874464826672563335163271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29249643217781708890108847 43874464826672563335163271)
              ·
                refine ⟨65811697240008845002744907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43874464826672563335163271 65811697240008845002744907)
                ·
                  refine ⟨98717545860013267504117361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65811697240008845002744907 98717545860013267504117361)
                  ·
                    refine ⟨74038159395009950628088021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98717545860013267504117361 74038159395009950628088021)
                    ·
                      refine ⟨1735269360820545717845813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74038159395009950628088021 1735269360820545717845813)
                      ·
                        rfl

theorem cell23_3379425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_3379425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379425 prefixEnd_3379425 := by exact prefixLift 3379425
  have htrace : WordTrace (prefixWord ++ tailWord_3379425) baseStart_3379425 baseEnd_3379425 := by
    simpa [prefixWord, tailWord_3379425, baseEnd_3379425] using wordTrace_append hprefix tailTrace_3379425
  have hstable : (prefixWord ++ tailWord_3379425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379425).length < 2 ^ (prefixWord ++ tailWord_3379425).sum := by decide
  have hdescent : baseEnd_3379425 < baseStart_3379425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379432 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 7]
def baseStart_3379432 : Nat := 118140960795 + 3379432 * 2 ^ 59
def prefixEnd_3379432 : Nat := 4983230072969 + 3 ^ 40 * 3379432 * 2
def baseEnd_3379432 : Nat := 192808106131680798939809

theorem tailTrace_3379432 : CollatzResearch.WordTrace tailWord_3379432 prefixEnd_3379432 192808106131680798939809 := by
  unfold tailWord_3379432
  simp only [CollatzResearch.WordTrace]
  refine ⟨61629005546451249940286275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82172007395268333253715033 61629005546451249940286275)
  ·
    refine ⟨92443508319676874910429413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61629005546451249940286275 92443508319676874910429413)
    ·
      refine ⟨17333157809939414045705515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92443508319676874910429413 17333157809939414045705515)
      ·
        refine ⟨25999736714909121068558273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17333157809939414045705515 25999736714909121068558273)
        ·
          refine ⟨19499802536181840801418705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25999736714909121068558273 19499802536181840801418705)
          ·
            refine ⟨14624851902136380601064029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19499802536181840801418705 14624851902136380601064029)
            ·
              refine ⟨5484319463301142725399011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14624851902136380601064029 5484319463301142725399011)
              ·
                refine ⟨8226479194951714088098517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5484319463301142725399011 8226479194951714088098517)
                ·
                  refine ⟨192808106131680798939809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8226479194951714088098517 192808106131680798939809)
                  ·
                    rfl

theorem cell23_3379432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 7].length) (baseStart_3379432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379432 prefixEnd_3379432 := by exact prefixLift 3379432
  have htrace : WordTrace (prefixWord ++ tailWord_3379432) baseStart_3379432 baseEnd_3379432 := by
    simpa [prefixWord, tailWord_3379432, baseEnd_3379432] using wordTrace_append hprefix tailTrace_3379432
  have hstable : (prefixWord ++ tailWord_3379432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379432).length < 2 ^ (prefixWord ++ tailWord_3379432).sum := by decide
  have hdescent : baseEnd_3379432 < baseStart_3379432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379455 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_3379455 : Nat := 118140960795 + 3379455 * 2 ^ 59
def prefixEnd_3379455 : Nat := 4983230072969 + 3 ^ 40 * 3379455 * 2
def baseEnd_3379455 : Nat := 1735284765240180600470675

theorem tailTrace_3379455 : CollatzResearch.WordTrace tailWord_3379455 prefixEnd_3379455 1735284765240180600470675 := by
  unfold tailWord_3379455
  simp only [CollatzResearch.WordTrace]
  refine ⟨123258849971819174808659819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82172566647879449872439879 123258849971819174808659819)
  ·
    refine ⟨184888274957728762212989729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123258849971819174808659819 184888274957728762212989729)
    ·
      refine ⟨138666206218296571659742297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184888274957728762212989729 138666206218296571659742297)
      ·
        refine ⟨103999654663722428744806723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138666206218296571659742297 103999654663722428744806723)
        ·
          refine ⟨155999481995583643117210085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103999654663722428744806723 155999481995583643117210085)
          ·
            refine ⟨29249902874171933084476891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155999481995583643117210085 29249902874171933084476891)
            ·
              refine ⟨43874854311257899626715337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29249902874171933084476891 43874854311257899626715337)
              ·
                refine ⟨32906140733443424720036503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43874854311257899626715337 32906140733443424720036503)
                ·
                  refine ⟨49359211100165137080054755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32906140733443424720036503 49359211100165137080054755)
                  ·
                    refine ⟨74038816650247705620082133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49359211100165137080054755 74038816650247705620082133)
                    ·
                      refine ⟨1735284765240180600470675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74038816650247705620082133 1735284765240180600470675)
                      ·
                        rfl

theorem cell23_3379455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_3379455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379455 prefixEnd_3379455 := by exact prefixLift 3379455
  have htrace : WordTrace (prefixWord ++ tailWord_3379455) baseStart_3379455 baseEnd_3379455 := by
    simpa [prefixWord, tailWord_3379455, baseEnd_3379455] using wordTrace_append hprefix tailTrace_3379455
  have hstable : (prefixWord ++ tailWord_3379455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379455).length < 2 ^ (prefixWord ++ tailWord_3379455).sum := by decide
  have hdescent : baseEnd_3379455 < baseStart_3379455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379509 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3379509 : Nat := 118140960795 + 3379509 * 2 ^ 59
def prefixEnd_3379509 : Nat := 4983230072969 + 3 ^ 40 * 3379509 * 2
def baseEnd_3379509 : Nat := 578437497731841129731809

theorem tailTrace_3379509 : CollatzResearch.WordTrace tailWord_3379509 prefixEnd_3379509 578437497731841129731809 := by
  unfold tailWord_3379509
  simp only [CollatzResearch.WordTrace]
  refine ⟨123260819513623542031125581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82173879675749028020750387 123260819513623542031125581)
  ·
    refine ⟨46222807317608828261672093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123260819513623542031125581 46222807317608828261672093)
    ·
      refine ⟨17333552744103310598127035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46222807317608828261672093 17333552744103310598127035)
      ·
        refine ⟨26000329116154965897190553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17333552744103310598127035 26000329116154965897190553)
        ·
          refine ⟨19500246837116224422892915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26000329116154965897190553 19500246837116224422892915)
          ·
            refine ⟨29250370255674336634339373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19500246837116224422892915 29250370255674336634339373)
            ·
              refine ⟨10968888845877876237877265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29250370255674336634339373 10968888845877876237877265)
              ·
                refine ⟨8226666634408407178407949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10968888845877876237877265 8226666634408407178407949)
                ·
                  refine ⟨3084999987903152691902981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8226666634408407178407949 3084999987903152691902981)
                  ·
                    refine ⟨578437497731841129731809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3084999987903152691902981 578437497731841129731809)
                    ·
                      rfl

theorem cell23_3379509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3379509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379509 prefixEnd_3379509 := by exact prefixLift 3379509
  have htrace : WordTrace (prefixWord ++ tailWord_3379509) baseStart_3379509 baseEnd_3379509 := by
    simpa [prefixWord, tailWord_3379509, baseEnd_3379509] using wordTrace_append hprefix tailTrace_3379509
  have hstable : (prefixWord ++ tailWord_3379509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379509).length < 2 ^ (prefixWord ++ tailWord_3379509).sum := by decide
  have hdescent : baseEnd_3379509 < baseStart_3379509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379609 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 3]
def baseStart_3379609 : Nat := 118140960795 + 3379609 * 2 ^ 59
def prefixEnd_3379609 : Nat := 4983230072969 + 3 ^ 40 * 3379609 * 2
def baseEnd_3379609 : Nat := 1735363841260972997944967

theorem tailTrace_3379609 : CollatzResearch.WordTrace tailWord_3379609 prefixEnd_3379609 1735363841260972997944967 := by
  unfold tailWord_3379609
  simp only [CollatzResearch.WordTrace]
  refine ⟨123264466813261259109765881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82176311208840839406510587 123264466813261259109765881)
  ·
    refine ⟨92448350109945944332324411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123264466813261259109765881 92448350109945944332324411)
    ·
      refine ⟨138672525164918916498486617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92448350109945944332324411 138672525164918916498486617)
      ·
        refine ⟨104004393873689187373864963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138672525164918916498486617 104004393873689187373864963)
        ·
          refine ⟨156006590810533781060797445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104004393873689187373864963 156006590810533781060797445)
          ·
            refine ⟨29251235776975083948899521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156006590810533781060797445 29251235776975083948899521)
            ·
              refine ⟨21938426832731312961674641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29251235776975083948899521 21938426832731312961674641)
              ·
                refine ⟨16453820124548484721255981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21938426832731312961674641 16453820124548484721255981)
                ·
                  refine ⟨6170182546705681770470993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16453820124548484721255981 6170182546705681770470993)
                  ·
                    refine ⟨4627636910029261327853245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6170182546705681770470993 4627636910029261327853245)
                    ·
                      refine ⟨1735363841260972997944967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4627636910029261327853245 1735363841260972997944967)
                      ·
                        rfl

theorem cell23_3379609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_3379609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379609 prefixEnd_3379609 := by exact prefixLift 3379609
  have htrace : WordTrace (prefixWord ++ tailWord_3379609) baseStart_3379609 baseEnd_3379609 := by
    simpa [prefixWord, tailWord_3379609, baseEnd_3379609] using wordTrace_append hprefix tailTrace_3379609
  have hstable : (prefixWord ++ tailWord_3379609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379609).length < 2 ^ (prefixWord ++ tailWord_3379609).sum := by decide
  have hdescent : baseEnd_3379609 < baseStart_3379609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379616 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 2, 4]
def baseStart_3379616 : Nat := 118140960795 + 3379616 * 2 ^ 59
def prefixEnd_3379616 : Nat := 4983230072969 + 3 ^ 40 * 3379616 * 2
def baseEnd_3379616 : Nat := 578455811875184823519145

theorem tailTrace_3379616 : CollatzResearch.WordTrace tailWord_3379616 prefixEnd_3379616 578455811875184823519145 := by
  unfold tailWord_3379616
  simp only [CollatzResearch.WordTrace]
  refine ⟨61632361062117949652635351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82176481416157266203513801 61632361062117949652635351)
  ·
    refine ⟨92448541593176924478953027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61632361062117949652635351 92448541593176924478953027)
    ·
      refine ⟨138672812389765386718429541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92448541593176924478953027 138672812389765386718429541)
      ·
        refine ⟨26001152323081010009705539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138672812389765386718429541 26001152323081010009705539)
        ·
          refine ⟨39001728484621515014558309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26001152323081010009705539 39001728484621515014558309)
          ·
            refine ⟨7312824090866534065229683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39001728484621515014558309 7312824090866534065229683)
            ·
              refine ⟨10969236136299801097844525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7312824090866534065229683 10969236136299801097844525)
              ·
                refine ⟨4113463551112425411691697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10969236136299801097844525 4113463551112425411691697)
                ·
                  refine ⟨3085097663334319058768773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113463551112425411691697 3085097663334319058768773)
                  ·
                    refine ⟨578455811875184823519145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085097663334319058768773 578455811875184823519145)
                    ·
                      rfl

theorem cell23_3379616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 2, 4].length) (baseStart_3379616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379616 prefixEnd_3379616 := by exact prefixLift 3379616
  have htrace : WordTrace (prefixWord ++ tailWord_3379616) baseStart_3379616 baseEnd_3379616 := by
    simpa [prefixWord, tailWord_3379616, baseEnd_3379616] using wordTrace_append hprefix tailTrace_3379616
  have hstable : (prefixWord ++ tailWord_3379616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379616).length < 2 ^ (prefixWord ++ tailWord_3379616).sum := by decide
  have hdescent : baseEnd_3379616 < baseStart_3379616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379623 : List Nat := [1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_3379623 : Nat := 118140960795 + 3379623 * 2 ^ 59
def prefixEnd_3379623 : Nat := 4983230072969 + 3 ^ 40 * 3379623 * 2
def baseEnd_3379623 : Nat := 1735371029990135943169903

theorem tailTrace_3379623 : CollatzResearch.WordTrace tailWord_3379623 prefixEnd_3379623 1735371029990135943169903 := by
  unfold tailWord_3379623
  simp only [CollatzResearch.WordTrace]
  refine ⟨123264977435210539500775523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82176651623473693000517015 123264977435210539500775523)
  ·
    refine ⟨184897466152815809251163285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123264977435210539500775523 184897466152815809251163285)
    ·
      refine ⟨8667068725913241058648279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184897466152815809251163285 8667068725913241058648279)
      ·
        refine ⟨13000603088869861587972419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667068725913241058648279 13000603088869861587972419)
        ·
          refine ⟨19500904633304792381958629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13000603088869861587972419 19500904633304792381958629)
          ·
            refine ⟨3656419618744648571617243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19500904633304792381958629 3656419618744648571617243)
            ·
              refine ⟨5484629428116972857425865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656419618744648571617243 5484629428116972857425865)
              ·
                refine ⟨4113472071087729643069399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5484629428116972857425865 4113472071087729643069399)
                ·
                  refine ⟨6170208106631594464604099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113472071087729643069399 6170208106631594464604099)
                  ·
                    refine ⟨9255312159947391696906149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6170208106631594464604099 9255312159947391696906149)
                    ·
                      refine ⟨1735371029990135943169903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9255312159947391696906149 1735371029990135943169903)
                      ·
                        rfl

theorem cell23_3379623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_3379623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379623 prefixEnd_3379623 := by exact prefixLift 3379623
  have htrace : WordTrace (prefixWord ++ tailWord_3379623) baseStart_3379623 baseEnd_3379623 := by
    simpa [prefixWord, tailWord_3379623, baseEnd_3379623] using wordTrace_append hprefix tailTrace_3379623
  have hstable : (prefixWord ++ tailWord_3379623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379623).length < 2 ^ (prefixWord ++ tailWord_3379623).sum := by decide
  have hdescent : baseEnd_3379623 < baseStart_3379623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379639 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3]
def baseStart_3379639 : Nat := 118140960795 + 3379639 * 2 ^ 59
def prefixEnd_3379639 : Nat := 4983230072969 + 3 ^ 40 * 3379639 * 2
def baseEnd_3379639 : Nat := 1735379245680607880569829

theorem tailTrace_3379639 : CollatzResearch.WordTrace tailWord_3379639 prefixEnd_3379639 1735379245680607880569829 := by
  unfold tailWord_3379639
  simp only [CollatzResearch.WordTrace]
  refine ⟨123265561003152574233357971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82177040668768382822238647 123265561003152574233357971)
  ·
    refine ⟨184898341504728861350036957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123265561003152574233357971 184898341504728861350036957)
    ·
      refine ⟨69336878064273323006263859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184898341504728861350036957 69336878064273323006263859)
      ·
        refine ⟨104005317096409984509395789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69336878064273323006263859 104005317096409984509395789)
        ·
          refine ⟨39001993911153744191023421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104005317096409984509395789 39001993911153744191023421)
          ·
            refine ⟨14625747716682654071633783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39001993911153744191023421 14625747716682654071633783)
            ·
              refine ⟨21938621575023981107450675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14625747716682654071633783 21938621575023981107450675)
              ·
                refine ⟨32907932362535971661176013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21938621575023981107450675 32907932362535971661176013)
                ·
                  refine ⟨12340474635950989372941005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32907932362535971661176013 12340474635950989372941005)
                  ·
                    refine ⟨4627677988481621014852877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12340474635950989372941005 4627677988481621014852877)
                    ·
                      refine ⟨1735379245680607880569829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4627677988481621014852877 1735379245680607880569829)
                      ·
                        rfl

theorem cell23_3379639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_3379639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379639 prefixEnd_3379639 := by exact prefixLift 3379639
  have htrace : WordTrace (prefixWord ++ tailWord_3379639) baseStart_3379639 baseEnd_3379639 := by
    simpa [prefixWord, tailWord_3379639, baseEnd_3379639] using wordTrace_append hprefix tailTrace_3379639
  have hstable : (prefixWord ++ tailWord_3379639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379639).length < 2 ^ (prefixWord ++ tailWord_3379639).sum := by decide
  have hdescent : baseEnd_3379639 < baseStart_3379639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379642 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_3379642 : Nat := 118140960795 + 3379642 * 2 ^ 59
def prefixEnd_3379642 : Nat := 4983230072969 + 3 ^ 40 * 3379642 * 2
def baseEnd_3379642 : Nat := 578460262040857122944105

theorem tailTrace_3379642 : CollatzResearch.WordTrace tailWord_3379642 prefixEnd_3379642 578460262040857122944105 := by
  unfold tailWord_3379642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30816417605535426436429295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82177113614761137163811453 30816417605535426436429295)
  ·
    refine ⟨46224626408303139654643943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30816417605535426436429295 46224626408303139654643943)
    ·
      refine ⟨69336939612454709481965915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46224626408303139654643943 69336939612454709481965915)
      ·
        refine ⟨104005409418682064222948873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69336939612454709481965915 104005409418682064222948873)
        ·
          refine ⟨78004057064011548167211655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104005409418682064222948873 78004057064011548167211655)
          ·
            refine ⟨117006085596017322250817483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78004057064011548167211655 117006085596017322250817483)
            ·
              refine ⟨175509128394025983376226225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117006085596017322250817483 175509128394025983376226225)
              ·
                refine ⟨131631846295519487532169669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175509128394025983376226225 131631846295519487532169669)
                ·
                  refine ⟨24680971180409903912281813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131631846295519487532169669 24680971180409903912281813)
                  ·
                    refine ⟨578460262040857122944105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24680971180409903912281813 578460262040857122944105)
                    ·
                      rfl

theorem cell23_3379642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_3379642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379642 prefixEnd_3379642 := by exact prefixLift 3379642
  have htrace : WordTrace (prefixWord ++ tailWord_3379642) baseStart_3379642 baseEnd_3379642 := by
    simpa [prefixWord, tailWord_3379642, baseEnd_3379642] using wordTrace_append hprefix tailTrace_3379642
  have hstable : (prefixWord ++ tailWord_3379642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379642).length < 2 ^ (prefixWord ++ tailWord_3379642).sum := by decide
  have hdescent : baseEnd_3379642 < baseStart_3379642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379696 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 1, 4, 2]
def baseStart_3379696 : Nat := 118140960795 + 3379696 * 2 ^ 59
def prefixEnd_3379696 : Nat := 4983230072969 + 3 ^ 40 * 3379696 * 2
def baseEnd_3379696 : Nat := 1735408514077914157557067

theorem tailTrace_3379696 : CollatzResearch.WordTrace tailWord_3379696 prefixEnd_3379696 1735408514077914157557067 := by
  unfold tailWord_3379696
  simp only [CollatzResearch.WordTrace]
  refine ⟨61633819981973036484091471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82178426642630715312121961 61633819981973036484091471)
  ·
    refine ⟨92450729972959554726137207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61633819981973036484091471 92450729972959554726137207)
    ·
      refine ⟨138676094959439332089205811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92450729972959554726137207 138676094959439332089205811)
      ·
        refine ⟨208014142439158998133808717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138676094959439332089205811 208014142439158998133808717)
        ·
          refine ⟨78005303414684624300178269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208014142439158998133808717 78005303414684624300178269)
          ·
            refine ⟨29251988780506734112566851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78005303414684624300178269 29251988780506734112566851)
            ·
              refine ⟨43877983170760101168850277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29251988780506734112566851 43877983170760101168850277)
              ·
                refine ⟨8227121844517518969159427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43877983170760101168850277 8227121844517518969159427)
                ·
                  refine ⟨12340682766776278453739141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8227121844517518969159427 12340682766776278453739141)
                  ·
                    refine ⟨2313878018770552210076089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12340682766776278453739141 2313878018770552210076089)
                    ·
                      refine ⟨1735408514077914157557067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313878018770552210076089 1735408514077914157557067)
                      ·
                        rfl

theorem cell23_3379696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 4, 2].length) (baseStart_3379696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379696 prefixEnd_3379696 := by exact prefixLift 3379696
  have htrace : WordTrace (prefixWord ++ tailWord_3379696) baseStart_3379696 baseEnd_3379696 := by
    simpa [prefixWord, tailWord_3379696, baseEnd_3379696] using wordTrace_append hprefix tailTrace_3379696
  have hstable : (prefixWord ++ tailWord_3379696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379696).length < 2 ^ (prefixWord ++ tailWord_3379696).sum := by decide
  have hdescent : baseEnd_3379696 < baseStart_3379696 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379709 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_3379709 : Nat := 118140960795 + 3379709 * 2 ^ 59
def prefixEnd_3379709 : Nat := 4983230072969 + 3 ^ 40 * 3379709 * 2
def baseEnd_3379709 : Nat := 1735415189326422606694507

theorem tailTrace_3379709 : CollatzResearch.WordTrace tailWord_3379709 prefixEnd_3379709 1735415189326422606694507 := by
  unfold tailWord_3379709
  simp only [CollatzResearch.WordTrace]
  refine ⟨123268114112898976188406181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82178742741932650792270787 123268114112898976188406181)
  ·
    refine ⟨23112771396168558035326159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123268114112898976188406181 23112771396168558035326159)
    ·
      refine ⟨34669157094252837052989239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112771396168558035326159 34669157094252837052989239)
      ·
        refine ⟨52003735641379255579483859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34669157094252837052989239 52003735641379255579483859)
        ·
          refine ⟨78005603462068883369225789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52003735641379255579483859 78005603462068883369225789)
          ·
            refine ⟨29252101298275831263459671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78005603462068883369225789 29252101298275831263459671)
            ·
              refine ⟨43878151947413746895189507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29252101298275831263459671 43878151947413746895189507)
              ·
                refine ⟨65817227921120620342784261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43878151947413746895189507 65817227921120620342784261)
                ·
                  refine ⟨12340730235210116314272049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65817227921120620342784261 12340730235210116314272049)
                  ·
                    refine ⟨9255547676407587235704037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12340730235210116314272049 9255547676407587235704037)
                    ·
                      refine ⟨1735415189326422606694507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9255547676407587235704037 1735415189326422606694507)
                      ·
                        rfl

theorem cell23_3379709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_3379709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379709 prefixEnd_3379709 := by exact prefixLift 3379709
  have htrace : WordTrace (prefixWord ++ tailWord_3379709) baseStart_3379709 baseEnd_3379709 := by
    simpa [prefixWord, tailWord_3379709, baseEnd_3379709] using wordTrace_append hprefix tailTrace_3379709
  have hstable : (prefixWord ++ tailWord_3379709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379709).length < 2 ^ (prefixWord ++ tailWord_3379709).sum := by decide
  have hdescent : baseEnd_3379709 < baseStart_3379709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379726 : List Nat := [4, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_3379726 : Nat := 118140960795 + 3379726 * 2 ^ 59
def prefixEnd_3379726 : Nat := 4983230072969 + 3 ^ 40 * 3379726 * 2
def baseEnd_3379726 : Nat := 1735423918497549040181929

theorem tailTrace_3379726 : CollatzResearch.WordTrace tailWord_3379726 prefixEnd_3379726 1735423918497549040181929 := by
  unfold tailWord_3379726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15408591769229673511471879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82179156102558258727850021 15408591769229673511471879)
  ·
    refine ⟨23112887653844510267207819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15408591769229673511471879 23112887653844510267207819)
    ·
      refine ⟨34669331480766765400811729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23112887653844510267207819 34669331480766765400811729)
      ·
        refine ⟨26001998610575074050608797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34669331480766765400811729 26001998610575074050608797)
        ·
          refine ⟨9750749478965652768978299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26001998610575074050608797 9750749478965652768978299)
          ·
            refine ⟨14626124218448479153467449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9750749478965652768978299 14626124218448479153467449)
            ·
              refine ⟨10969593163836359365100587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14626124218448479153467449 10969593163836359365100587)
              ·
                refine ⟨16454389745754539047650881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10969593163836359365100587 16454389745754539047650881)
                ·
                  refine ⟨12340792309315904285738161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16454389745754539047650881 12340792309315904285738161)
                  ·
                    refine ⟨9255594231986928214303621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12340792309315904285738161 9255594231986928214303621)
                    ·
                      refine ⟨1735423918497549040181929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9255594231986928214303621 1735423918497549040181929)
                      ·
                        rfl

theorem cell23_3379726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_3379726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379726 prefixEnd_3379726 := by exact prefixLift 3379726
  have htrace : WordTrace (prefixWord ++ tailWord_3379726) baseStart_3379726 baseEnd_3379726 := by
    simpa [prefixWord, tailWord_3379726, baseEnd_3379726] using wordTrace_append hprefix tailTrace_3379726
  have hstable : (prefixWord ++ tailWord_3379726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379726).length < 2 ^ (prefixWord ++ tailWord_3379726).sum := by decide
  have hdescent : baseEnd_3379726 < baseStart_3379726 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379729 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 3]
def baseStart_3379729 : Nat := 118140960795 + 3379729 * 2 ^ 59
def prefixEnd_3379729 : Nat := 4983230072969 + 3 ^ 40 * 3379729 * 2
def baseEnd_3379729 : Nat := 1735425458939512528444415

theorem tailTrace_3379729 : CollatzResearch.WordTrace tailWord_3379729 prefixEnd_3379729 1735425458939512528444415 := by
  unfold tailWord_3379729
  simp only [CollatzResearch.WordTrace]
  refine ⟨123268843572826519604134241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82179229048551013069422827 123268843572826519604134241)
  ·
    refine ⟨92451632679619889703100681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123268843572826519604134241 92451632679619889703100681)
    ·
      refine ⟨69338724509714917277325511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92451632679619889703100681 69338724509714917277325511)
      ·
        refine ⟨104008086764572375915988267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69338724509714917277325511 104008086764572375915988267)
        ·
          refine ⟨156012130146858563873982401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104008086764572375915988267 156012130146858563873982401)
          ·
            refine ⟨117009097610143922905486801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156012130146858563873982401 117009097610143922905486801)
            ·
              refine ⟨87756823207607942179115101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117009097610143922905486801 87756823207607942179115101)
              ·
                refine ⟨32908808702852978317168163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87756823207607942179115101 32908808702852978317168163)
                ·
                  refine ⟨49363213054279467475752245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32908808702852978317168163 49363213054279467475752245)
                  ·
                    refine ⟨4627801223838700075851773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49363213054279467475752245 4627801223838700075851773)
                    ·
                      refine ⟨1735425458939512528444415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4627801223838700075851773 1735425458939512528444415)
                      ·
                        rfl

theorem cell23_3379729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_3379729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379729 prefixEnd_3379729 := by exact prefixLift 3379729
  have htrace : WordTrace (prefixWord ++ tailWord_3379729) baseStart_3379729 baseEnd_3379729 := by
    simpa [prefixWord, tailWord_3379729, baseEnd_3379729] using wordTrace_append hprefix tailTrace_3379729
  have hstable : (prefixWord ++ tailWord_3379729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379729).length < 2 ^ (prefixWord ++ tailWord_3379729).sum := by decide
  have hdescent : baseEnd_3379729 < baseStart_3379729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379749 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 1, 7]
def baseStart_3379749 : Nat := 118140960795 + 3379749 * 2 ^ 59
def prefixEnd_3379749 : Nat := 4983230072969 + 3 ^ 40 * 3379749 * 2
def baseEnd_3379749 : Nat := 578478576184200816731441

theorem tailTrace_3379749 : CollatzResearch.WordTrace tailWord_3379749 prefixEnd_3379749 578478576184200816731441 := by
  unfold tailWord_3379749
  simp only [CollatzResearch.WordTrace]
  refine ⟨123269573032754063019862301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82179715355169375346574867 123269573032754063019862301)
  ·
    refine ⟨46226089887282773632448363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123269573032754063019862301 46226089887282773632448363)
    ·
      refine ⟨69339134830924160448672545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46226089887282773632448363 69339134830924160448672545)
      ·
        refine ⟨52004351123193120336504409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69339134830924160448672545 52004351123193120336504409)
        ·
          refine ⟨39003263342394840252378307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52004351123193120336504409 39003263342394840252378307)
          ·
            refine ⟨58504895013592260378567461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39003263342394840252378307 58504895013592260378567461)
            ·
              refine ⟨10969667815048548820981399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58504895013592260378567461 10969667815048548820981399)
              ·
                refine ⟨16454501722572823231472099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10969667815048548820981399 16454501722572823231472099)
                ·
                  refine ⟨24681752583859234847208149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16454501722572823231472099 24681752583859234847208149)
                  ·
                    refine ⟨578478576184200816731441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24681752583859234847208149 578478576184200816731441)
                    ·
                      rfl

theorem cell23_3379749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_3379749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379749 prefixEnd_3379749 := by exact prefixLift 3379749
  have htrace : WordTrace (prefixWord ++ tailWord_3379749) baseStart_3379749 baseEnd_3379749 := by
    simpa [prefixWord, tailWord_3379749, baseEnd_3379749] using wordTrace_append hprefix tailTrace_3379749
  have hstable : (prefixWord ++ tailWord_3379749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379749).length < 2 ^ (prefixWord ++ tailWord_3379749).sum := by decide
  have hdescent : baseEnd_3379749 < baseStart_3379749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379849 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 7]
def baseStart_3379849 : Nat := 118140960795 + 3379849 * 2 ^ 59
def prefixEnd_3379849 : Nat := 4983230072969 + 3 ^ 40 * 3379849 * 2
def baseEnd_3379849 : Nat := 1735487076618052058943863

theorem tailTrace_3379849 : CollatzResearch.WordTrace tailWord_3379849 prefixEnd_3379849 1735487076618052058943863 := by
  unfold tailWord_3379849
  simp only [CollatzResearch.WordTrace]
  refine ⟨123273220332391780098502601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82182146888261186732335067 123273220332391780098502601)
  ·
    refine ⟨92454915249293835073876951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123273220332391780098502601 92454915249293835073876951)
    ·
      refine ⟨138682372873940752610815427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92454915249293835073876951 138682372873940752610815427)
      ·
        refine ⟨208023559310911128916223141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138682372873940752610815427 208023559310911128916223141)
        ·
          refine ⟨39004417370795836671791839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208023559310911128916223141 39004417370795836671791839)
          ·
            refine ⟨58506626056193755007687759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39004417370795836671791839 58506626056193755007687759)
            ·
              refine ⟨87759939084290632511531639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58506626056193755007687759 87759939084290632511531639)
              ·
                refine ⟨131639908626435948767297459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87759939084290632511531639 131639908626435948767297459)
                ·
                  refine ⟨197459862939653923150946189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131639908626435948767297459 197459862939653923150946189)
                  ·
                    refine ⟨74047448602370221181604821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 197459862939653923150946189 74047448602370221181604821)
                    ·
                      refine ⟨1735487076618052058943863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74047448602370221181604821 1735487076618052058943863)
                      ·
                        rfl

theorem cell23_3379849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_3379849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379849 prefixEnd_3379849 := by exact prefixLift 3379849
  have htrace : WordTrace (prefixWord ++ tailWord_3379849) baseStart_3379849 baseEnd_3379849 := by
    simpa [prefixWord, tailWord_3379849, baseEnd_3379849] using wordTrace_append hprefix tailTrace_3379849
  have hstable : (prefixWord ++ tailWord_3379849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379849).length < 2 ^ (prefixWord ++ tailWord_3379849).sum := by decide
  have hdescent : baseEnd_3379849 < baseStart_3379849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379863 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 1, 5, 2]
def baseStart_3379863 : Nat := 118140960795 + 3379863 * 2 ^ 59
def prefixEnd_3379863 : Nat := 4983230072969 + 3 ^ 40 * 3379863 * 2
def baseEnd_3379863 : Nat := 1735494265347215004168799

theorem tailTrace_3379863 : CollatzResearch.WordTrace tailWord_3379863 prefixEnd_3379863 1735494265347215004168799 := by
  unfold tailWord_3379863
  simp only [CollatzResearch.WordTrace]
  refine ⟨123273730954341060489512243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82182487302894040326341495 123273730954341060489512243)
  ·
    refine ⟨184910596431511590734268365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123273730954341060489512243 184910596431511590734268365)
    ·
      refine ⟨69341473661816846525350637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184910596431511590734268365 69341473661816846525350637)
      ·
        refine ⟨26003052623181317447006489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69341473661816846525350637 26003052623181317447006489)
        ·
          refine ⟨19502289467385988085254867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26003052623181317447006489 19502289467385988085254867)
          ·
            refine ⟨29253434201078982127882301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19502289467385988085254867 29253434201078982127882301)
            ·
              refine ⟨10970037825404618297955863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29253434201078982127882301 10970037825404618297955863)
              ·
                refine ⟨16455056738106927446933795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10970037825404618297955863 16455056738106927446933795)
                ·
                  refine ⟨24682585107160391170400693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16455056738106927446933795 24682585107160391170400693)
                  ·
                    refine ⟨2313992353796286672225065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24682585107160391170400693 2313992353796286672225065)
                    ·
                      refine ⟨1735494265347215004168799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2313992353796286672225065 1735494265347215004168799)
                      ·
                        rfl

theorem cell23_3379863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_3379863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379863 prefixEnd_3379863 := by exact prefixLift 3379863
  have htrace : WordTrace (prefixWord ++ tailWord_3379863) baseStart_3379863 baseEnd_3379863 := by
    simpa [prefixWord, tailWord_3379863, baseEnd_3379863] using wordTrace_append hprefix tailTrace_3379863
  have hstable : (prefixWord ++ tailWord_3379863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379863).length < 2 ^ (prefixWord ++ tailWord_3379863).sum := by decide
  have hdescent : baseEnd_3379863 < baseStart_3379863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379870 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_3379870 : Nat := 118140960795 + 3379870 * 2 ^ 59
def prefixEnd_3379870 : Nat := 4983230072969 + 3 ^ 40 * 3379870 * 2
def baseEnd_3379870 : Nat := 1735497859711796476781267

theorem tailTrace_3379870 : CollatzResearch.WordTrace tailWord_3379870 prefixEnd_3379870 1735497859711796476781267 := by
  unfold tailWord_3379870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15409248283164462585627133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82182657510210467123344709 15409248283164462585627133)
  ·
    refine ⟨5778468106186673469610175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15409248283164462585627133 5778468106186673469610175)
    ·
      refine ⟨8667702159280010204415263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778468106186673469610175 8667702159280010204415263)
      ·
        refine ⟨13001553238920015306622895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8667702159280010204415263 13001553238920015306622895)
        ·
          refine ⟨19502329858380022959934343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001553238920015306622895 19502329858380022959934343)
          ·
            refine ⟨29253494787570034439901515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19502329858380022959934343 29253494787570034439901515)
            ·
              refine ⟨43880242181355051659852273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29253494787570034439901515 43880242181355051659852273)
              ·
                refine ⟨32910181636016288744889205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43880242181355051659852273 32910181636016288744889205)
                ·
                  refine ⟨3085329528376527069833363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32910181636016288744889205 3085329528376527069833363)
                  ·
                    refine ⟨4627994292564790604750045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3085329528376527069833363 4627994292564790604750045)
                    ·
                      refine ⟨1735497859711796476781267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4627994292564790604750045 1735497859711796476781267)
                      ·
                        rfl

theorem cell23_3379870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_3379870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379870 prefixEnd_3379870 := by exact prefixLift 3379870
  have htrace : WordTrace (prefixWord ++ tailWord_3379870) baseStart_3379870 baseEnd_3379870 := by
    simpa [prefixWord, tailWord_3379870, baseEnd_3379870] using wordTrace_append hprefix tailTrace_3379870
  have hstable : (prefixWord ++ tailWord_3379870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379870).length < 2 ^ (prefixWord ++ tailWord_3379870).sum := by decide
  have hdescent : baseEnd_3379870 < baseStart_3379870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379903 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 1, 6]
def baseStart_3379903 : Nat := 118140960795 + 3379903 * 2 ^ 59
def prefixEnd_3379903 : Nat := 4983230072969 + 3 ^ 40 * 3379903 * 2
def baseEnd_3379903 : Nat := 578504934857798282556205

theorem tailTrace_3379903 : CollatzResearch.WordTrace tailWord_3379903 prefixEnd_3379903 578504934857798282556205 := by
  unfold tailWord_3379903
  simp only [CollatzResearch.WordTrace]
  refine ⟨123275189874196147320968363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82183459916130764880645575 123275189874196147320968363)
  ·
    refine ⟨184912784811294220981452545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123275189874196147320968363 184912784811294220981452545)
    ·
      refine ⟨138684588608470665736089409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184912784811294220981452545 138684588608470665736089409)
      ·
        refine ⟨104013441456352999302067057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138684588608470665736089409 104013441456352999302067057)
        ·
          refine ⟨78010081092264749476550293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104013441456352999302067057 78010081092264749476550293)
          ·
            refine ⟨3656722551199910131713295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78010081092264749476550293 3656722551199910131713295)
            ·
              refine ⟨5485083826799865197569943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656722551199910131713295 5485083826799865197569943)
              ·
                refine ⟨8227625740199797796354915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485083826799865197569943 8227625740199797796354915)
                ·
                  refine ⟨12341438610299696694532373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8227625740199797796354915 12341438610299696694532373)
                  ·
                    refine ⟨578504934857798282556205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12341438610299696694532373 578504934857798282556205)
                    ·
                      rfl

theorem cell23_3379903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_3379903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379903 prefixEnd_3379903 := by exact prefixLift 3379903
  have htrace : WordTrace (prefixWord ++ tailWord_3379903) baseStart_3379903 baseEnd_3379903 := by
    simpa [prefixWord, tailWord_3379903, baseEnd_3379903] using wordTrace_append hprefix tailTrace_3379903
  have hstable : (prefixWord ++ tailWord_3379903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379903).length < 2 ^ (prefixWord ++ tailWord_3379903).sum := by decide
  have hdescent : baseEnd_3379903 < baseStart_3379903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379944 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_3379944 : Nat := 118140960795 + 3379944 * 2 ^ 59
def prefixEnd_3379944 : Nat := 4983230072969 + 3 ^ 40 * 3379944 * 2
def baseEnd_3379944 : Nat := 1735535857280229187255927

theorem tailTrace_3379944 : CollatzResearch.WordTrace tailWord_3379944 prefixEnd_3379944 1735535857280229187255927 := by
  unfold tailWord_3379944
  simp only [CollatzResearch.WordTrace]
  refine ⟨61638342633523805661605443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82184456844698407548807257 61638342633523805661605443)
  ·
    refine ⟨92457513950285708492408165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61638342633523805661605443 92457513950285708492408165)
    ·
      refine ⟨17335783865678570342326531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92457513950285708492408165 17335783865678570342326531)
      ·
        refine ⟨26003675798517855513489797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17335783865678570342326531 26003675798517855513489797)
        ·
          refine ⟨4875689212222097908779337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26003675798517855513489797 4875689212222097908779337)
          ·
            refine ⟨3656766909166573431584503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4875689212222097908779337 3656766909166573431584503)
            ·
              refine ⟨5485150363749860147376755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656766909166573431584503 5485150363749860147376755)
              ·
                refine ⟨8227725545624790221065133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485150363749860147376755 8227725545624790221065133)
                ·
                  refine ⟨3085397079609296332899425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8227725545624790221065133 3085397079609296332899425)
                  ·
                    refine ⟨2314047809706972249674569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3085397079609296332899425 2314047809706972249674569)
                    ·
                      refine ⟨1735535857280229187255927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314047809706972249674569 1735535857280229187255927)
                      ·
                        rfl

theorem cell23_3379944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_3379944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379944 prefixEnd_3379944 := by exact prefixLift 3379944
  have htrace : WordTrace (prefixWord ++ tailWord_3379944) baseStart_3379944 baseEnd_3379944 := by
    simpa [prefixWord, tailWord_3379944, baseEnd_3379944] using wordTrace_append hprefix tailTrace_3379944
  have hstable : (prefixWord ++ tailWord_3379944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379944).length < 2 ^ (prefixWord ++ tailWord_3379944).sum := by decide
  have hdescent : baseEnd_3379944 < baseStart_3379944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379946 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_3379946 : Nat := 118140960795 + 3379946 * 2 ^ 59
def prefixEnd_3379946 : Nat := 4983230072969 + 3 ^ 40 * 3379946 * 2
def baseEnd_3379946 : Nat := 578512294747179393143639

theorem tailTrace_3379946 : CollatzResearch.WordTrace tailWord_3379946 prefixEnd_3379946 578512294747179393143639 := by
  unfold tailWord_3379946
  simp only [CollatzResearch.WordTrace]
  refine ⟨30819189553260091416195923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82184505475360243776522461 30819189553260091416195923)
  ·
    refine ⟨46228784329890137124293885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30819189553260091416195923 46228784329890137124293885)
    ·
      refine ⟨17335794123708801421610207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46228784329890137124293885 17335794123708801421610207)
      ·
        refine ⟨26003691185563202132415311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17335794123708801421610207 26003691185563202132415311)
        ·
          refine ⟨39005536778344803198622967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26003691185563202132415311 39005536778344803198622967)
          ·
            refine ⟨58508305167517204797934451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39005536778344803198622967 58508305167517204797934451)
            ·
              refine ⟨87762457751275807196901677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58508305167517204797934451 87762457751275807196901677)
              ·
                refine ⟨32910921656728427698838129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87762457751275807196901677 32910921656728427698838129)
                ·
                  refine ⟨24683191242546320774128597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32910921656728427698838129 24683191242546320774128597)
                  ·
                    refine ⟨578512294747179393143639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24683191242546320774128597 578512294747179393143639)
                    ·
                      rfl

theorem cell23_3379946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_3379946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379946 prefixEnd_3379946 := by exact prefixLift 3379946
  have htrace : WordTrace (prefixWord ++ tailWord_3379946) baseStart_3379946 baseEnd_3379946 := by
    simpa [prefixWord, tailWord_3379946, baseEnd_3379946] using wordTrace_append hprefix tailTrace_3379946
  have hstable : (prefixWord ++ tailWord_3379946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379946).length < 2 ^ (prefixWord ++ tailWord_3379946).sum := by decide
  have hdescent : baseEnd_3379946 < baseStart_3379946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379960 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 2, 1, 3]
def baseStart_3379960 : Nat := 118140960795 + 3379960 * 2 ^ 59
def prefixEnd_3379960 : Nat := 4983230072969 + 3 ^ 40 * 3379960 * 2
def baseEnd_3379960 : Nat := 1735544072970701124655853

theorem tailTrace_3379960 : CollatzResearch.WordTrace tailWord_3379960 prefixEnd_3379960 1735544072970701124655853 := by
  unfold tailWord_3379960
  simp only [CollatzResearch.WordTrace]
  refine ⟨61638634417494823027896667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82184845889993097370528889 61638634417494823027896667)
  ·
    refine ⟨92457951626242234541845001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61638634417494823027896667 92457951626242234541845001)
    ·
      refine ⟨69343463719681675906383751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92457951626242234541845001 69343463719681675906383751)
      ·
        refine ⟨104015195579522513859575627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69343463719681675906383751 104015195579522513859575627)
        ·
          refine ⟨156022793369283770789363441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104015195579522513859575627 156022793369283770789363441)
          ·
            refine ⟨117017095026962828092022581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156022793369283770789363441 117017095026962828092022581)
            ·
              refine ⟨10970352658777765133627117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117017095026962828092022581 10970352658777765133627117)
              ·
                refine ⟨4113882247041661925110169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10970352658777765133627117 4113882247041661925110169)
                ·
                  refine ⟨3085411685281246443832627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113882247041661925110169 3085411685281246443832627)
                  ·
                    refine ⟨4628117527921869665748941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3085411685281246443832627 4628117527921869665748941)
                    ·
                      refine ⟨1735544072970701124655853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4628117527921869665748941 1735544072970701124655853)
                      ·
                        rfl

theorem cell23_3379960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 2, 1, 3].length) (baseStart_3379960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379960 prefixEnd_3379960 := by exact prefixLift 3379960
  have htrace : WordTrace (prefixWord ++ tailWord_3379960) baseStart_3379960 baseEnd_3379960 := by
    simpa [prefixWord, tailWord_3379960, baseEnd_3379960] using wordTrace_append hprefix tailTrace_3379960
  have hstable : (prefixWord ++ tailWord_3379960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379960).length < 2 ^ (prefixWord ++ tailWord_3379960).sum := by decide
  have hdescent : baseEnd_3379960 < baseStart_3379960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3379987 : List Nat := [1, 1, 1, 2, 1, 3, 7, 1, 1, 3, 2]
def baseStart_3379987 : Nat := 118140960795 + 3379987 * 2 ^ 59
def prefixEnd_3379987 : Nat := 4983230072969 + 3 ^ 40 * 3379987 * 2
def baseEnd_3379987 : Nat := 1735557936948372519018229

theorem tailTrace_3379987 : CollatzResearch.WordTrace tailWord_3379987 prefixEnd_3379987 1735557936948372519018229 := by
  unfold tailWord_3379987
  simp only [CollatzResearch.WordTrace]
  refine ⟨123278253605891829667026215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82185502403927886444684143 123278253605891829667026215)
  ·
    refine ⟨184917380408837744500539323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123278253605891829667026215 184917380408837744500539323)
    ·
      refine ⟨277376070613256616750808985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184917380408837744500539323 277376070613256616750808985)
      ·
        refine ⟨208032052959942462563106739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277376070613256616750808985 208032052959942462563106739)
        ·
          refine ⟨312048079439913693844660109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208032052959942462563106739 312048079439913693844660109)
          ·
            refine ⟨117018029789967635191747541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312048079439913693844660109 117018029789967635191747541)
            ·
              refine ⟨2742610073202366449806583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 117018029789967635191747541 2742610073202366449806583)
              ·
                refine ⟨4113915109803549674709875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742610073202366449806583 4113915109803549674709875)
                ·
                  refine ⟨6170872664705324512064813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4113915109803549674709875 6170872664705324512064813)
                  ·
                    refine ⟨2314077249264496692024305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6170872664705324512064813 2314077249264496692024305)
                    ·
                      refine ⟨1735557936948372519018229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314077249264496692024305 1735557936948372519018229)
                      ·
                        rfl

theorem cell23_3379987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 1, 1, 3, 2].length) (baseStart_3379987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3379987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3379987 prefixEnd_3379987 := by exact prefixLift 3379987
  have htrace : WordTrace (prefixWord ++ tailWord_3379987) baseStart_3379987 baseEnd_3379987 := by
    simpa [prefixWord, tailWord_3379987, baseEnd_3379987] using wordTrace_append hprefix tailTrace_3379987
  have hstable : (prefixWord ++ tailWord_3379987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3379987).length < 2 ^ (prefixWord ++ tailWord_3379987).sum := by decide
  have hdescent : baseEnd_3379987 < baseStart_3379987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3379987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380017 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 2, 2, 2]
def baseStart_3380017 : Nat := 118140960795 + 3380017 * 2 ^ 59
def prefixEnd_3380017 : Nat := 4983230072969 + 3 ^ 40 * 3380017 * 2
def baseEnd_3380017 : Nat := 1735573341368007401643091

theorem tailTrace_3380017 : CollatzResearch.WordTrace tailWord_3380017 prefixEnd_3380017 1735573341368007401643091 := by
  unfold tailWord_3380017
  simp only [CollatzResearch.WordTrace]
  refine ⟨123279347795783144790618305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82186231863855429860412203 123279347795783144790618305)
  ·
    refine ⟨92459510846837358592963729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123279347795783144790618305 92459510846837358592963729)
    ·
      refine ⟨69344633135128018944722797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92459510846837358592963729 69344633135128018944722797)
      ·
        refine ⟨26004237425673007104271049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69344633135128018944722797 26004237425673007104271049)
        ·
          refine ⟨19503178069254755328203287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26004237425673007104271049 19503178069254755328203287)
          ·
            refine ⟨29254767103882132992304931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19503178069254755328203287 29254767103882132992304931)
            ·
              refine ⟨43882150655823199488457397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29254767103882132992304931 43882150655823199488457397)
              ·
                refine ⟨4113951623983424952042881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43882150655823199488457397 4113951623983424952042881)
                ·
                  refine ⟨3085463717987568714032161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113951623983424952042881 3085463717987568714032161)
                  ·
                    refine ⟨2314097788490676535524121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3085463717987568714032161 2314097788490676535524121)
                    ·
                      refine ⟨1735573341368007401643091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314097788490676535524121 1735573341368007401643091)
                      ·
                        rfl

theorem cell23_3380017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_3380017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380017 prefixEnd_3380017 := by exact prefixLift 3380017
  have htrace : WordTrace (prefixWord ++ tailWord_3380017) baseStart_3380017 baseEnd_3380017 := by
    simpa [prefixWord, tailWord_3380017, baseEnd_3380017] using wordTrace_append hprefix tailTrace_3380017
  have hstable : (prefixWord ++ tailWord_3380017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380017).length < 2 ^ (prefixWord ++ tailWord_3380017).sum := by decide
  have hdescent : baseEnd_3380017 < baseStart_3380017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380040 : List Nat := [2, 1, 3, 1, 1, 3, 4, 3, 5]
def baseStart_3380040 : Nat := 118140960795 + 3380040 * 2 ^ 59
def prefixEnd_3380040 : Nat := 4983230072969 + 3 ^ 40 * 3380040 * 2
def baseEnd_3380040 : Nat := 192842794602562312406165

theorem tailTrace_3380040 : CollatzResearch.WordTrace tailWord_3380040 prefixEnd_3380040 192842794602562312406165 := by
  unfold tailWord_3380040
  simp only [CollatzResearch.WordTrace]
  refine ⟨61640093337349909859352787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82186791116466546479137049 61640093337349909859352787)
  ·
    refine ⟨92460140006024864789029181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61640093337349909859352787 92460140006024864789029181)
    ·
      refine ⟨34672552502259324295885943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92460140006024864789029181 34672552502259324295885943)
      ·
        refine ⟨52008828753388986443828915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34672552502259324295885943 52008828753388986443828915)
        ·
          refine ⟨78013243130083479665743373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52008828753388986443828915 78013243130083479665743373)
          ·
            refine ⟨29254966173781304874653765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78013243130083479665743373 29254966173781304874653765)
            ·
              refine ⟨5485306157583994663997581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29254966173781304874653765 5485306157583994663997581)
              ·
                refine ⟨2056989809093997998999093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5485306157583994663997581 2056989809093997998999093)
                ·
                  refine ⟨192842794602562312406165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2056989809093997998999093 192842794602562312406165)
                  ·
                    rfl

theorem cell23_3380040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 3, 5].length) (baseStart_3380040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380040 prefixEnd_3380040 := by exact prefixLift 3380040
  have htrace : WordTrace (prefixWord ++ tailWord_3380040) baseStart_3380040 baseEnd_3380040 := by
    simpa [prefixWord, tailWord_3380040, baseEnd_3380040] using wordTrace_append hprefix tailTrace_3380040
  have hstable : (prefixWord ++ tailWord_3380040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380040).length < 2 ^ (prefixWord ++ tailWord_3380040).sum := by decide
  have hdescent : baseEnd_3380040 < baseStart_3380040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380053 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3380053 : Nat := 118140960795 + 3380053 * 2 ^ 59
def prefixEnd_3380053 : Nat := 4983230072969 + 3 ^ 40 * 3380053 * 2
def baseEnd_3380053 : Nat := 578530608890523086930975

theorem tailTrace_3380053 : CollatzResearch.WordTrace tailWord_3380053 prefixEnd_3380053 578530608890523086930975 := by
  unfold tailWord_3380053
  simp only [CollatzResearch.WordTrace]
  refine ⟨123280660823652722938928813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82187107215768481959285875 123280660823652722938928813)
  ·
    refine ⟨46230247808869771102098305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123280660823652722938928813 46230247808869771102098305)
    ·
      refine ⟨34672685856652328326573729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46230247808869771102098305 34672685856652328326573729)
      ·
        refine ⟨26004514392489246244930297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34672685856652328326573729 26004514392489246244930297)
        ·
          refine ⟨19503385794366934683697723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26004514392489246244930297 19503385794366934683697723)
          ·
            refine ⟨29255078691550402025546585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19503385794366934683697723 29255078691550402025546585)
            ·
              refine ⟨21941309018662801519159939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29255078691550402025546585 21941309018662801519159939)
              ·
                refine ⟨32911963527994202278739909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21941309018662801519159939 32911963527994202278739909)
                ·
                  refine ⟨6170993161498912927263733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32911963527994202278739909 6170993161498912927263733)
                  ·
                    refine ⟨578530608890523086930975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6170993161498912927263733 578530608890523086930975)
                    ·
                      rfl

theorem cell23_3380053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3380053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380053 prefixEnd_3380053 := by exact prefixLift 3380053
  have htrace : WordTrace (prefixWord ++ tailWord_3380053) baseStart_3380053 baseEnd_3380053 := by
    simpa [prefixWord, tailWord_3380053, baseEnd_3380053] using wordTrace_append hprefix tailTrace_3380053
  have hstable : (prefixWord ++ tailWord_3380053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380053).length < 2 ^ (prefixWord ++ tailWord_3380053).sum := by decide
  have hdescent : baseEnd_3380053 < baseStart_3380053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380113 : List Nat := [1, 2, 2, 1, 1, 1, 3, 6, 6]
def baseStart_3380113 : Nat := 118140960795 + 3380113 * 2 ^ 59
def prefixEnd_3380113 : Nat := 4983230072969 + 3 ^ 40 * 3380113 * 2
def baseEnd_3380113 : Nat := 192846959501204336226961

theorem tailTrace_3380113 : CollatzResearch.WordTrace tailWord_3380113 prefixEnd_3380113 192846959501204336226961 := by
  unfold tailWord_3380113
  simp only [CollatzResearch.WordTrace]
  refine ⟨123282849203435353186112993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82188566135623568790741995 123282849203435353186112993)
  ·
    refine ⟨92462136902576514889584745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123282849203435353186112993 92462136902576514889584745)
    ·
      refine ⟨69346602676932386167188559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92462136902576514889584745 69346602676932386167188559)
      ·
        refine ⟨104019904015398579250782839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69346602676932386167188559 104019904015398579250782839)
        ·
          refine ⟨156029856023097868876174259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104019904015398579250782839 156029856023097868876174259)
          ·
            refine ⟨234044784034646803314261389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156029856023097868876174259 234044784034646803314261389)
            ·
              refine ⟨87766794012992551242848021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234044784034646803314261389 87766794012992551242848021)
              ·
                refine ⟨4114068469359025839508501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87766794012992551242848021 4114068469359025839508501)
                ·
                  refine ⟨192846959501204336226961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4114068469359025839508501 192846959501204336226961)
                  ·
                    rfl

theorem cell23_3380113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 6].length) (baseStart_3380113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380113 prefixEnd_3380113 := by exact prefixLift 3380113
  have htrace : WordTrace (prefixWord ++ tailWord_3380113) baseStart_3380113 baseEnd_3380113 := by
    simpa [prefixWord, tailWord_3380113, baseEnd_3380113] using wordTrace_append hprefix tailTrace_3380113
  have hstable : (prefixWord ++ tailWord_3380113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380113).length < 2 ^ (prefixWord ++ tailWord_3380113).sum := by decide
  have hdescent : baseEnd_3380113 < baseStart_3380113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380117 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 3, 4]
def baseStart_3380117 : Nat := 118140960795 + 3380117 * 2 ^ 59
def prefixEnd_3380117 : Nat := 4983230072969 + 3 ^ 40 * 3380117 * 2
def baseEnd_3380117 : Nat := 578541563144485670130877

theorem tailTrace_3380117 : CollatzResearch.WordTrace tailWord_3380117 prefixEnd_3380117 578541563144485670130877 := by
  unfold tailWord_3380117
  simp only [CollatzResearch.WordTrace]
  refine ⟨123282995095420861869258605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82188663396947241246172403 123282995095420861869258605)
  ·
    refine ⟨46231123160782823200971977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123282995095420861869258605 46231123160782823200971977)
    ·
      refine ⟨34673342370587117400728983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46231123160782823200971977 34673342370587117400728983)
      ·
        refine ⟨52010013555880676101093475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34673342370587117400728983 52010013555880676101093475)
        ·
          refine ⟨78015020333821014151640213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52010013555880676101093475 78015020333821014151640213)
          ·
            refine ⟨3656954078147860038358135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78015020333821014151640213 3656954078147860038358135)
            ·
              refine ⟨5485431117221790057537203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656954078147860038358135 5485431117221790057537203)
              ·
                refine ⟨8228146675832685086305805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485431117221790057537203 8228146675832685086305805)
                ·
                  refine ⟨3085555003437256907364677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8228146675832685086305805 3085555003437256907364677)
                  ·
                    refine ⟨578541563144485670130877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085555003437256907364677 578541563144485670130877)
                    ·
                      rfl

theorem cell23_3380117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_3380117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380117 prefixEnd_3380117 := by exact prefixLift 3380117
  have htrace : WordTrace (prefixWord ++ tailWord_3380117) baseStart_3380117 baseEnd_3380117 := by
    simpa [prefixWord, tailWord_3380117, baseEnd_3380117] using wordTrace_append hprefix tailTrace_3380117
  have hstable : (prefixWord ++ tailWord_3380117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380117).length < 2 ^ (prefixWord ++ tailWord_3380117).sum := by decide
  have hdescent : baseEnd_3380117 < baseStart_3380117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380164 : List Nat := [2, 3, 3, 3, 1, 1, 2, 2, 6]
def baseStart_3380164 : Nat := 118140960795 + 3380164 * 2 ^ 59
def prefixEnd_3380164 : Nat := 4983230072969 + 3 ^ 40 * 3380164 * 2
def baseEnd_3380164 : Nat := 192849869224913147389435

theorem tailTrace_3380164 : CollatzResearch.WordTrace tailWord_3380164 prefixEnd_3380164 192849869224913147389435 := by
  unfold tailWord_3380164
  simp only [CollatzResearch.WordTrace]
  refine ⟨61642354663125294448109773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82189806217500392597479697 61642354663125294448109773)
  ·
    refine ⟨23115882998671985418041165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61642354663125294448109773 23115882998671985418041165)
    ·
      refine ⟨8668456124501994531765437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23115882998671985418041165 8668456124501994531765437)
      ·
        refine ⟨3250671046688247949412039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8668456124501994531765437 3250671046688247949412039)
        ·
          refine ⟨4876006570032371924118059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250671046688247949412039 4876006570032371924118059)
          ·
            refine ⟨7314009855048557886177089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876006570032371924118059 7314009855048557886177089)
            ·
              refine ⟨5485507391286418414632817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7314009855048557886177089 5485507391286418414632817)
              ·
                refine ⟨4114130543464813810974613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485507391286418414632817 4114130543464813810974613)
                ·
                  refine ⟨192849869224913147389435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4114130543464813810974613 192849869224913147389435)
                  ·
                    rfl

theorem cell23_3380164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_3380164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380164 prefixEnd_3380164 := by exact prefixLift 3380164
  have htrace : WordTrace (prefixWord ++ tailWord_3380164) baseStart_3380164 baseEnd_3380164 := by
    simpa [prefixWord, tailWord_3380164, baseEnd_3380164] using wordTrace_append hprefix tailTrace_3380164
  have hstable : (prefixWord ++ tailWord_3380164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380164).length < 2 ^ (prefixWord ++ tailWord_3380164).sum := by decide
  have hdescent : baseEnd_3380164 < baseStart_3380164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380167 : List Nat := [1, 1, 4, 1, 1, 2, 4, 2, 2, 3, 2]
def baseStart_3380167 : Nat := 118140960795 + 3380167 * 2 ^ 59
def prefixEnd_3380167 : Nat := 4983230072969 + 3 ^ 40 * 3380167 * 2
def baseEnd_3380167 : Nat := 1735650363466181814767401

theorem tailTrace_3380167 : CollatzResearch.WordTrace tailWord_3380167 prefixEnd_3380167 1735650363466181814767401 := by
  unfold tailWord_3380167
  simp only [CollatzResearch.WordTrace]
  refine ⟨123284818745239720408578755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82189879163493146939052503 123284818745239720408578755)
  ·
    refine ⟨184927228117859580612868133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123284818745239720408578755 184927228117859580612868133)
    ·
      refine ⟨34673855272098671364912775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184927228117859580612868133 34673855272098671364912775)
      ·
        refine ⟨52010782908148007047369163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34673855272098671364912775 52010782908148007047369163)
        ·
          refine ⟨78016174362222010571053745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52010782908148007047369163 78016174362222010571053745)
          ·
            refine ⟨58512130771666507928290309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78016174362222010571053745 58512130771666507928290309)
            ·
              refine ⟨10971024519687470236554433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58512130771666507928290309 10971024519687470236554433)
              ·
                refine ⟨8228268389765602677415825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10971024519687470236554433 8228268389765602677415825)
                ·
                  refine ⟨6171201292324202008061869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8228268389765602677415825 6171201292324202008061869)
                  ·
                    refine ⟨2314200484621575753023201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6171201292324202008061869 2314200484621575753023201)
                    ·
                      refine ⟨1735650363466181814767401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314200484621575753023201 1735650363466181814767401)
                      ·
                        rfl

theorem cell23_3380167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_3380167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380167 prefixEnd_3380167 := by exact prefixLift 3380167
  have htrace : WordTrace (prefixWord ++ tailWord_3380167) baseStart_3380167 baseEnd_3380167 := by
    simpa [prefixWord, tailWord_3380167, baseEnd_3380167] using wordTrace_append hprefix tailTrace_3380167
  have hstable : (prefixWord ++ tailWord_3380167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380167).length < 2 ^ (prefixWord ++ tailWord_3380167).sum := by decide
  have hdescent : baseEnd_3380167 < baseStart_3380167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380168 : List Nat := [2, 1, 3, 1, 6, 1, 2, 2, 1, 4]
def baseStart_3380168 : Nat := 118140960795 + 3380168 * 2 ^ 59
def prefixEnd_3380168 : Nat := 4983230072969 + 3 ^ 40 * 3380168 * 2
def baseEnd_3380168 : Nat := 578550292315612103618299

theorem tailTrace_3380168 : CollatzResearch.WordTrace tailWord_3380168 prefixEnd_3380168 578550292315612103618299 := by
  unfold tailWord_3380168
  simp only [CollatzResearch.WordTrace]
  refine ⟨61642427609118048789682579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82189903478824065052910105 61642427609118048789682579)
  ·
    refine ⟨92463641413677073184523869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61642427609118048789682579 92463641413677073184523869)
    ·
      refine ⟨34673865530128902444196451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92463641413677073184523869 34673865530128902444196451)
      ·
        refine ⟨52010798295193353666294677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34673865530128902444196451 52010798295193353666294677)
        ·
          refine ⟨2438006170087188453107563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52010798295193353666294677 2438006170087188453107563)
          ·
            refine ⟨3657009255130782679661345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438006170087188453107563 3657009255130782679661345)
            ·
              refine ⟨2742756941348087009746009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657009255130782679661345 2742756941348087009746009)
              ·
                refine ⟨2057067706011065257309507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742756941348087009746009 2057067706011065257309507)
                ·
                  refine ⟨3085601559016597885964261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057067706011065257309507 3085601559016597885964261)
                  ·
                    refine ⟨578550292315612103618299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085601559016597885964261 578550292315612103618299)
                    ·
                      rfl

theorem cell23_3380168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_3380168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380168 prefixEnd_3380168 := by exact prefixLift 3380168
  have htrace : WordTrace (prefixWord ++ tailWord_3380168) baseStart_3380168 baseEnd_3380168 := by
    simpa [prefixWord, tailWord_3380168, baseEnd_3380168] using wordTrace_append hprefix tailTrace_3380168
  have hstable : (prefixWord ++ tailWord_3380168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380168).length < 2 ^ (prefixWord ++ tailWord_3380168).sum := by decide
  have hdescent : baseEnd_3380168 < baseStart_3380168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380214 : List Nat := [5, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4]
def baseStart_3380214 : Nat := 118140960795 + 3380214 * 2 ^ 59
def prefixEnd_3380214 : Nat := 4983230072969 + 3 ^ 40 * 3380214 * 2
def baseEnd_3380214 : Nat := 1735674497056943130879685

theorem tailTrace_3380214 : CollatzResearch.WordTrace tailWord_3380214 prefixEnd_3380214 1735674497056943130879685 := by
  unfold tailWord_3380214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7705408311004340464721231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82191021984046298290359797 7705408311004340464721231)
  ·
    refine ⟨11558112466506510697081847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7705408311004340464721231 11558112466506510697081847)
    ·
      refine ⟨17337168699759766045622771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11558112466506510697081847 17337168699759766045622771)
      ·
        refine ⟨26005753049639649068434157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17337168699759766045622771 26005753049639649068434157)
        ·
          refine ⟨9752157393614868400662809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26005753049639649068434157 9752157393614868400662809)
          ·
            refine ⟨7314118045211151300497107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9752157393614868400662809 7314118045211151300497107)
            ·
              refine ⟨10971177067816726950745661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314118045211151300497107 10971177067816726950745661)
              ·
                refine ⟨4114191400431272606529623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10971177067816726950745661 4114191400431272606529623)
                ·
                  refine ⟨6171287100646908909794435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114191400431272606529623 6171287100646908909794435)
                  ·
                    refine ⟨9256930650970363364691653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6171287100646908909794435 9256930650970363364691653)
                    ·
                      refine ⟨1735674497056943130879685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9256930650970363364691653 1735674497056943130879685)
                      ·
                        rfl

theorem cell23_3380214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_3380214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380214 prefixEnd_3380214 := by exact prefixLift 3380214
  have htrace : WordTrace (prefixWord ++ tailWord_3380214) baseStart_3380214 baseEnd_3380214 := by
    simpa [prefixWord, tailWord_3380214, baseEnd_3380214] using wordTrace_append hprefix tailTrace_3380214
  have hstable : (prefixWord ++ tailWord_3380214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380214).length < 2 ^ (prefixWord ++ tailWord_3380214).sum := by decide
  have hdescent : baseEnd_3380214 < baseStart_3380214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380217 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3380217 : Nat := 118140960795 + 3380217 * 2 ^ 59
def prefixEnd_3380217 : Nat := 4983230072969 + 3 ^ 40 * 3380217 * 2
def baseEnd_3380217 : Nat := 1735676037498906619142171

theorem tailTrace_3380217 : CollatzResearch.WordTrace tailWord_3380217 prefixEnd_3380217 1735676037498906619142171 := by
  unfold tailWord_3380217
  simp only [CollatzResearch.WordTrace]
  refine ⟨123286642395058578947898905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82191094930039052631932603 123286642395058578947898905)
  ·
    refine ⟨92464981796293934210924179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123286642395058578947898905 92464981796293934210924179)
    ·
      refine ⟨138697472694440901316386269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92464981796293934210924179 138697472694440901316386269)
      ·
        refine ⟨52011552260415337993644851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138697472694440901316386269 52011552260415337993644851)
        ·
          refine ⟨78017328390623006990467277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52011552260415337993644851 78017328390623006990467277)
          ·
            refine ⟨29256498146483627621425229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78017328390623006990467277 29256498146483627621425229)
            ·
              refine ⟨10971186804931360358034461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29256498146483627621425229 10971186804931360358034461)
              ·
                refine ⟨4114195051849260134262923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10971186804931360358034461 4114195051849260134262923)
                ·
                  refine ⟨6171292577773890201394385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114195051849260134262923 6171292577773890201394385)
                  ·
                    refine ⟨4628469433330417651045789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6171292577773890201394385 4628469433330417651045789)
                    ·
                      refine ⟨1735676037498906619142171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4628469433330417651045789 1735676037498906619142171)
                      ·
                        rfl

theorem cell23_3380217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3380217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380217 prefixEnd_3380217 := by exact prefixLift 3380217
  have htrace : WordTrace (prefixWord ++ tailWord_3380217) baseStart_3380217 baseEnd_3380217 := by
    simpa [prefixWord, tailWord_3380217, baseEnd_3380217] using wordTrace_append hprefix tailTrace_3380217
  have hstable : (prefixWord ++ tailWord_3380217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380217).length < 2 ^ (prefixWord ++ tailWord_3380217).sum := by decide
  have hdescent : baseEnd_3380217 < baseStart_3380217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380223 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_3380223 : Nat := 118140960795 + 3380223 * 2 ^ 59
def prefixEnd_3380223 : Nat := 4983230072969 + 3 ^ 40 * 3380223 * 2
def baseEnd_3380223 : Nat := 1735679118382833595667143

theorem tailTrace_3380223 : CollatzResearch.WordTrace tailWord_3380223 prefixEnd_3380223 1735679118382833595667143 := by
  unfold tailWord_3380223
  simp only [CollatzResearch.WordTrace]
  refine ⟨123286861233036841972617323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82191240822024561315078215 123286861233036841972617323)
  ·
    refine ⟨184930291849555262958925985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123286861233036841972617323 184930291849555262958925985)
    ·
      refine ⟨138697718887166447219194489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184930291849555262958925985 138697718887166447219194489)
      ·
        refine ⟨104023289165374835414395867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138697718887166447219194489 104023289165374835414395867)
        ·
          refine ⟨156034933748062253121593801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104023289165374835414395867 156034933748062253121593801)
          ·
            refine ⟨117026200311046689841195351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156034933748062253121593801 117026200311046689841195351)
            ·
              refine ⟨175539300466570034761793027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117026200311046689841195351 175539300466570034761793027)
              ·
                refine ⟨263308950699855052142689541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175539300466570034761793027 263308950699855052142689541)
                ·
                  refine ⟨49370428256222822276754289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 263308950699855052142689541 49370428256222822276754289)
                  ·
                    refine ⟨37027821192167116707565717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49370428256222822276754289 37027821192167116707565717)
                    ·
                      refine ⟨1735679118382833595667143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37027821192167116707565717 1735679118382833595667143)
                      ·
                        rfl

theorem cell23_3380223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_3380223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380223 prefixEnd_3380223 := by exact prefixLift 3380223
  have htrace : WordTrace (prefixWord ++ tailWord_3380223) baseStart_3380223 baseEnd_3380223 := by
    simpa [prefixWord, tailWord_3380223, baseEnd_3380223] using wordTrace_append hprefix tailTrace_3380223
  have hstable : (prefixWord ++ tailWord_3380223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380223).length < 2 ^ (prefixWord ++ tailWord_3380223).sum := by decide
  have hdescent : baseEnd_3380223 < baseStart_3380223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380231 : List Nat := [1, 1, 4, 3, 1, 1, 1, 6, 1, 2, 2]
def baseStart_3380231 : Nat := 118140960795 + 3380231 * 2 ^ 59
def prefixEnd_3380231 : Nat := 4983230072969 + 3 ^ 40 * 3380231 * 2
def baseEnd_3380231 : Nat := 1735683226228069564367107

theorem tailTrace_3380231 : CollatzResearch.WordTrace tailWord_3380231 prefixEnd_3380231 1735683226228069564367107 := by
  unfold tailWord_3380231
  simp only [CollatzResearch.WordTrace]
  refine ⟨123287153017007859338908547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82191435344671906225939031 123287153017007859338908547)
  ·
    refine ⟨184930729525511789008362821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123287153017007859338908547 184930729525511789008362821)
    ·
      refine ⟨34674511786033460439068029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184930729525511789008362821 34674511786033460439068029)
      ·
        refine ⟨13002941919762547664650511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34674511786033460439068029 13002941919762547664650511)
        ·
          refine ⟨19504412879643821496975767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13002941919762547664650511 19504412879643821496975767)
          ·
            refine ⟨29256619319465732245463651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19504412879643821496975767 29256619319465732245463651)
            ·
              refine ⟨43884928979198598368195477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29256619319465732245463651 43884928979198598368195477)
              ·
                refine ⟨2057106045899934298509163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43884928979198598368195477 2057106045899934298509163)
                ·
                  refine ⟨3085659068849901447763745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057106045899934298509163 3085659068849901447763745)
                  ·
                    refine ⟨2314244301637426085822809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3085659068849901447763745 2314244301637426085822809)
                    ·
                      refine ⟨1735683226228069564367107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314244301637426085822809 1735683226228069564367107)
                      ·
                        rfl

theorem cell23_3380231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_3380231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380231 prefixEnd_3380231 := by exact prefixLift 3380231
  have htrace : WordTrace (prefixWord ++ tailWord_3380231) baseStart_3380231 baseEnd_3380231 := by
    simpa [prefixWord, tailWord_3380231, baseEnd_3380231] using wordTrace_append hprefix tailTrace_3380231
  have hstable : (prefixWord ++ tailWord_3380231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380231).length < 2 ^ (prefixWord ++ tailWord_3380231).sum := by decide
  have hdescent : baseEnd_3380231 < baseStart_3380231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380233 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 1, 9]
def baseStart_3380233 : Nat := 118140960795 + 3380233 * 2 ^ 59
def prefixEnd_3380233 : Nat := 4983230072969 + 3 ^ 40 * 3380233 * 2
def baseEnd_3380233 : Nat := 578561417729792852180699

theorem tailTrace_3380233 : CollatzResearch.WordTrace tailWord_3380233 prefixEnd_3380233 578561417729792852180699 := by
  unfold tailWord_3380233
  simp only [CollatzResearch.WordTrace]
  refine ⟨123287225963000613680481353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82191483975333742453654235 123287225963000613680481353)
  ·
    refine ⟨92465419472250460260361015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123287225963000613680481353 92465419472250460260361015)
    ·
      refine ⟨138698129208375690390541523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92465419472250460260361015 138698129208375690390541523)
      ·
        refine ⟨208047193812563535585812285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138698129208375690390541523 208047193812563535585812285)
        ·
          refine ⟨78017697679711325844679607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208047193812563535585812285 78017697679711325844679607)
          ·
            refine ⟨117026546519566988767019411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78017697679711325844679607 117026546519566988767019411)
            ·
              refine ⟨175539819779350483150529117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117026546519566988767019411 175539819779350483150529117)
              ·
                refine ⟨65827432417256431181448419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175539819779350483150529117 65827432417256431181448419)
                ·
                  refine ⟨98741148625884646772172629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65827432417256431181448419 98741148625884646772172629)
                  ·
                    refine ⟨578561417729792852180699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 98741148625884646772172629 578561417729792852180699)
                    ·
                      rfl

theorem cell23_3380233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 9].length) (baseStart_3380233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380233 prefixEnd_3380233 := by exact prefixLift 3380233
  have htrace : WordTrace (prefixWord ++ tailWord_3380233) baseStart_3380233 baseEnd_3380233 := by
    simpa [prefixWord, tailWord_3380233, baseEnd_3380233] using wordTrace_append hprefix tailTrace_3380233
  have hstable : (prefixWord ++ tailWord_3380233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380233).length < 2 ^ (prefixWord ++ tailWord_3380233).sum := by decide
  have hdescent : baseEnd_3380233 < baseStart_3380233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380274 : List Nat := [3, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2]
def baseStart_3380274 : Nat := 118140960795 + 3380274 * 2 ^ 59
def prefixEnd_3380274 : Nat := 4983230072969 + 3 ^ 40 * 3380274 * 2
def baseEnd_3380274 : Nat := 1735705305896212896129409

theorem tailTrace_3380274 : CollatzResearch.WordTrace tailWord_3380274 prefixEnd_3380274 1735705305896212896129409 := by
  unfold tailWord_3380274
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822180338963019420680969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82192480903901385121815917 30822180338963019420680969)
  ·
    refine ⟨23116635254222264565510727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30822180338963019420680969 23116635254222264565510727)
    ·
      refine ⟨34674952881333396848266091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23116635254222264565510727 34674952881333396848266091)
      ·
        refine ⟨52012429322000095272399137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34674952881333396848266091 52012429322000095272399137)
        ·
          refine ⟨39009321991500071454299353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52012429322000095272399137 39009321991500071454299353)
          ·
            refine ⟨29256991493625053590724515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39009321991500071454299353 29256991493625053590724515)
            ·
              refine ⟨43885487240437580386086773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29256991493625053590724515 43885487240437580386086773)
              ·
                refine ⟨4114264428791023161195635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43885487240437580386086773 4114264428791023161195635)
                ·
                  refine ⟨6171396643186534741793453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114264428791023161195635 6171396643186534741793453)
                  ·
                    refine ⟨2314273741194950528172545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6171396643186534741793453 2314273741194950528172545)
                    ·
                      refine ⟨1735705305896212896129409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314273741194950528172545 1735705305896212896129409)
                      ·
                        rfl

theorem cell23_3380274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_3380274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380274 prefixEnd_3380274 := by exact prefixLift 3380274
  have htrace : WordTrace (prefixWord ++ tailWord_3380274) baseStart_3380274 baseEnd_3380274 := by
    simpa [prefixWord, tailWord_3380274, baseEnd_3380274] using wordTrace_append hprefix tailTrace_3380274
  have hstable : (prefixWord ++ tailWord_3380274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380274).length < 2 ^ (prefixWord ++ tailWord_3380274).sum := by decide
  have hdescent : baseEnd_3380274 < baseStart_3380274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380300 : List Nat := [2, 2, 1, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3380300 : Nat := 118140960795 + 3380300 * 2 ^ 59
def prefixEnd_3380300 : Nat := 4983230072969 + 3 ^ 40 * 3380300 * 2
def baseEnd_3380300 : Nat := 1735718656393229794404289

theorem tailTrace_3380300 : CollatzResearch.WordTrace tailWord_3380300 prefixEnd_3380300 1735718656393229794404289 := by
  unfold tailWord_3380300
  simp only [CollatzResearch.WordTrace]
  refine ⟨61644834826878942061585177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82193113102505256082113569 61644834826878942061585177)
  ·
    refine ⟨46233626120159206546188883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61644834826878942061585177 46233626120159206546188883)
    ·
      refine ⟨69350439180238809819283325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46233626120159206546188883 69350439180238809819283325)
      ·
        refine ⟨26006414692589553682231247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69350439180238809819283325 26006414692589553682231247)
        ·
          refine ⟨39009622038884330523346871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26006414692589553682231247 39009622038884330523346871)
          ·
            refine ⟨58514433058326495785020307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39009622038884330523346871 58514433058326495785020307)
            ·
              refine ⟨87771649587489743677530461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58514433058326495785020307 87771649587489743677530461)
              ·
                refine ⟨32914368595308653879073923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87771649587489743677530461 32914368595308653879073923)
                ·
                  refine ⟨49371552892962980818610885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32914368595308653879073923 49371552892962980818610885)
                  ·
                    refine ⟨9257166167430558903489541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49371552892962980818610885 9257166167430558903489541)
                    ·
                      refine ⟨1735718656393229794404289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9257166167430558903489541 1735718656393229794404289)
                      ·
                        rfl

theorem cell23_3380300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3380300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380300 prefixEnd_3380300 := by exact prefixLift 3380300
  have htrace : WordTrace (prefixWord ++ tailWord_3380300) baseStart_3380300 baseEnd_3380300 := by
    simpa [prefixWord, tailWord_3380300, baseEnd_3380300] using wordTrace_append hprefix tailTrace_3380300
  have hstable : (prefixWord ++ tailWord_3380300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380300).length < 2 ^ (prefixWord ++ tailWord_3380300).sum := by decide
  have hdescent : baseEnd_3380300 < baseStart_3380300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380344 : List Nat := [2, 1, 2, 1, 1, 1, 8, 2, 5]
def baseStart_3380344 : Nat := 118140960795 + 3380344 * 2 ^ 59
def prefixEnd_3380344 : Nat := 4983230072969 + 3 ^ 40 * 3380344 * 2
def baseEnd_3380344 : Nat := 192860138838003069139343

theorem tailTrace_3380344 : CollatzResearch.WordTrace tailWord_3380344 prefixEnd_3380344 192860138838003069139343 := by
  unfold tailWord_3380344
  simp only [CollatzResearch.WordTrace]
  refine ⟨61645637232799239818886043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82194182977065653091848057 61645637232799239818886043)
  ·
    refine ⟨92468455849198859728329065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61645637232799239818886043 92468455849198859728329065)
    ·
      refine ⟨69351341886899144796246799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92468455849198859728329065 69351341886899144796246799)
      ·
        refine ⟨104027012830348717194370199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69351341886899144796246799 104027012830348717194370199)
        ·
          refine ⟨156040519245523075791555299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104027012830348717194370199 156040519245523075791555299)
          ·
            refine ⟨234060778868284613687332949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156040519245523075791555299 234060778868284613687332949)
            ·
              refine ⟨2742899752362710316648433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 234060778868284613687332949 2742899752362710316648433)
              ·
                refine ⟨2057174814272032737486325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742899752362710316648433 2057174814272032737486325)
                ·
                  refine ⟨192860138838003069139343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2057174814272032737486325 192860138838003069139343)
                  ·
                    rfl

theorem cell23_3380344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 5].length) (baseStart_3380344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380344 prefixEnd_3380344 := by exact prefixLift 3380344
  have htrace : WordTrace (prefixWord ++ tailWord_3380344) baseStart_3380344 baseEnd_3380344 := by
    simpa [prefixWord, tailWord_3380344, baseEnd_3380344] using wordTrace_append hprefix tailTrace_3380344
  have hstable : (prefixWord ++ tailWord_3380344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380344).length < 2 ^ (prefixWord ++ tailWord_3380344).sum := by decide
  have hdescent : baseEnd_3380344 < baseStart_3380344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380400 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 8]
def baseStart_3380400 : Nat := 118140960795 + 3380400 * 2 ^ 59
def prefixEnd_3380400 : Nat := 4983230072969 + 3 ^ 40 * 3380400 * 2
def baseEnd_3380400 : Nat := 192863333828742155905981

theorem tailTrace_3380400 : CollatzResearch.WordTrace tailWord_3380400 prefixEnd_3380400 192863333828742155905981 := by
  unfold tailWord_3380400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61646658476697800600905327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82195544635597067467873769 61646658476697800600905327)
  ·
    refine ⟨92469987715046700901357991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61646658476697800600905327 92469987715046700901357991)
    ·
      refine ⟨138704981572570051352036987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92469987715046700901357991 138704981572570051352036987)
      ·
        refine ⟨208057472358855077028055481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138704981572570051352036987 208057472358855077028055481)
        ·
          refine ⟨156043104269141307771041611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208057472358855077028055481 156043104269141307771041611)
          ·
            refine ⟨234064656403711961656562417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156043104269141307771041611 234064656403711961656562417)
            ·
              refine ⟨175548492302783971242421813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234064656403711961656562417 175548492302783971242421813)
              ·
                refine ⟨16457671153385997303977045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175548492302783971242421813 16457671153385997303977045)
                ·
                  refine ⟨192863333828742155905981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16457671153385997303977045 192863333828742155905981)
                  ·
                    rfl

theorem cell23_3380400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 8].length) (baseStart_3380400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380400 prefixEnd_3380400 := by exact prefixLift 3380400
  have htrace : WordTrace (prefixWord ++ tailWord_3380400) baseStart_3380400 baseEnd_3380400 := by
    simpa [prefixWord, tailWord_3380400, baseEnd_3380400] using wordTrace_append hprefix tailTrace_3380400
  have hstable : (prefixWord ++ tailWord_3380400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380400).length < 2 ^ (prefixWord ++ tailWord_3380400).sum := by decide
  have hdescent : baseEnd_3380400 < baseStart_3380400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380414 : List Nat := [4, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_3380414 : Nat := 118140960795 + 3380414 * 2 ^ 59
def prefixEnd_3380414 : Nat := 4983230072969 + 3 ^ 40 * 3380414 * 2
def baseEnd_3380414 : Nat := 1735777193187842348378765

theorem tailTrace_3380414 : CollatzResearch.WordTrace tailWord_3380414 prefixEnd_3380414 1735777193187842348378765 := by
  unfold tailWord_3380414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15411728446918110199102537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82195885050229921061880197 15411728446918110199102537)
  ·
    refine ⟨11558796335188582649326903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15411728446918110199102537 11558796335188582649326903)
    ·
      refine ⟨17338194502782873973990355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11558796335188582649326903 17338194502782873973990355)
      ·
        refine ⟨26007291754174310960985533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17338194502782873973990355 26007291754174310960985533)
        ·
          refine ⟨9752734407815366610369575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26007291754174310960985533 9752734407815366610369575)
          ·
            refine ⟨14629101611723049915554363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752734407815366610369575 14629101611723049915554363)
            ·
              refine ⟨21943652417584574873331545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14629101611723049915554363 21943652417584574873331545)
              ·
                refine ⟨16457739313188431154998659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21943652417584574873331545 16457739313188431154998659)
                ·
                  refine ⟨24686608969782646732497989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16457739313188431154998659 24686608969782646732497989)
                  ·
                    refine ⟨4628739181834246262343373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24686608969782646732497989 4628739181834246262343373)
                    ·
                      refine ⟨1735777193187842348378765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4628739181834246262343373 1735777193187842348378765)
                      ·
                        rfl

theorem cell23_3380414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_3380414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380414 prefixEnd_3380414 := by exact prefixLift 3380414
  have htrace : WordTrace (prefixWord ++ tailWord_3380414) baseStart_3380414 baseEnd_3380414 := by
    simpa [prefixWord, tailWord_3380414, baseEnd_3380414] using wordTrace_append hprefix tailTrace_3380414
  have hstable : (prefixWord ++ tailWord_3380414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380414).length < 2 ^ (prefixWord ++ tailWord_3380414).sum := by decide
  have hdescent : baseEnd_3380414 < baseStart_3380414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380455 : List Nat := [1, 1, 5, 3, 2, 1, 3, 2, 1, 4]
def baseStart_3380455 : Nat := 118140960795 + 3380455 * 2 ^ 59
def prefixEnd_3380455 : Nat := 4983230072969 + 3 ^ 40 * 3380455 * 2
def baseEnd_3380455 : Nat := 578599415298225562655359

theorem tailTrace_3380455 : CollatzResearch.WordTrace tailWord_3380455 prefixEnd_3380455 578599415298225562655359 := by
  unfold tailWord_3380455
  simp only [CollatzResearch.WordTrace]
  refine ⟨123295322968196345595062819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82196881978797563730041879 123295322968196345595062819)
  ·
    refine ⟨184942984452294518392594229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123295322968196345595062819 184942984452294518392594229)
    ·
      refine ⟨17338404792402611099305709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184942984452294518392594229 17338404792402611099305709)
      ·
        refine ⟨6501901797150979162239641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17338404792402611099305709 6501901797150979162239641)
        ·
          refine ⟨4876426347863234371679731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6501901797150979162239641 4876426347863234371679731)
          ·
            refine ⟨7314639521794851557519597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876426347863234371679731 7314639521794851557519597)
            ·
              refine ⟨2742989820673069334069849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7314639521794851557519597 2742989820673069334069849)
              ·
                refine ⟨2057242365504802000552387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742989820673069334069849 2057242365504802000552387)
                ·
                  refine ⟨3085863548257203000828581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057242365504802000552387 3085863548257203000828581)
                  ·
                    refine ⟨578599415298225562655359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3085863548257203000828581 578599415298225562655359)
                    ·
                      rfl

theorem cell23_3380455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_3380455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380455 prefixEnd_3380455 := by exact prefixLift 3380455
  have htrace : WordTrace (prefixWord ++ tailWord_3380455) baseStart_3380455 baseEnd_3380455 := by
    simpa [prefixWord, tailWord_3380455, baseEnd_3380455] using wordTrace_append hprefix tailTrace_3380455
  have hstable : (prefixWord ++ tailWord_3380455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380455).length < 2 ^ (prefixWord ++ tailWord_3380455).sum := by decide
  have hdescent : baseEnd_3380455 < baseStart_3380455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380481 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 1, 5]
def baseStart_3380481 : Nat := 118140960795 + 3380481 * 2 ^ 59
def prefixEnd_3380481 : Nat := 4983230072969 + 3 ^ 40 * 3380481 * 2
def baseEnd_3380481 : Nat := 578603865463897862080319

theorem tailTrace_3380481 : CollatzResearch.WordTrace tailWord_3380481 prefixEnd_3380481 578603865463897862080319 := by
  unfold tailWord_3380481
  simp only [CollatzResearch.WordTrace]
  refine ⟨123296271266102152035509297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82197514177401434690339531 123296271266102152035509297)
  ·
    refine ⟨92472203449576614026631973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123296271266102152035509297 92472203449576614026631973)
    ·
      refine ⟨17338538146795615129993495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92472203449576614026631973 17338538146795615129993495)
      ·
        refine ⟨26007807220193422694990243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17338538146795615129993495 26007807220193422694990243)
        ·
          refine ⟨39011710830290134042485365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26007807220193422694990243 39011710830290134042485365)
          ·
            refine ⟨3657347890339700066483003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39011710830290134042485365 3657347890339700066483003)
            ·
              refine ⟨5486021835509550099724505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657347890339700066483003 5486021835509550099724505)
              ·
                refine ⟨4114516376632162574793379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486021835509550099724505 4114516376632162574793379)
                ·
                  refine ⟨6171774564948243862190069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114516376632162574793379 6171774564948243862190069)
                  ·
                    refine ⟨578603865463897862080319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6171774564948243862190069 578603865463897862080319)
                    ·
                      rfl

theorem cell23_3380481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 1, 5].length) (baseStart_3380481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380481 prefixEnd_3380481 := by exact prefixLift 3380481
  have htrace : WordTrace (prefixWord ++ tailWord_3380481) baseStart_3380481 baseEnd_3380481 := by
    simpa [prefixWord, tailWord_3380481, baseEnd_3380481] using wordTrace_append hprefix tailTrace_3380481
  have hstable : (prefixWord ++ tailWord_3380481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380481).length < 2 ^ (prefixWord ++ tailWord_3380481).sum := by decide
  have hdescent : baseEnd_3380481 < baseStart_3380481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380488 : List Nat := [2, 1, 3, 2, 4, 1, 2, 1, 2, 3, 2]
def baseStart_3380488 : Nat := 118140960795 + 3380488 * 2 ^ 59
def prefixEnd_3380488 : Nat := 4983230072969 + 3 ^ 40 * 3380488 * 2
def baseEnd_3380488 : Nat := 1735815190756275058853425

theorem tailTrace_3380488 : CollatzResearch.WordTrace tailWord_3380488 prefixEnd_3380488 1735815190756275058853425 := by
  unfold tailWord_3380488
  simp only [CollatzResearch.WordTrace]
  refine ⟨61648263288538396115507059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82197684384717861487342745 61648263288538396115507059)
  ·
    refine ⟨92472394932807594173260589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61648263288538396115507059 92472394932807594173260589)
    ·
      refine ⟨34677148099802847814972721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92472394932807594173260589 34677148099802847814972721)
      ·
        refine ⟨26007861074852135861229541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34677148099802847814972721 26007861074852135861229541)
        ·
          refine ⟨4876473951534775473980539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26007861074852135861229541 4876473951534775473980539)
          ·
            refine ⟨7314710927302163210970809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876473951534775473980539 7314710927302163210970809)
            ·
              refine ⟨5486033195476622408228107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7314710927302163210970809 5486033195476622408228107)
              ·
                refine ⟨8229049793214933612342161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5486033195476622408228107 8229049793214933612342161)
                ·
                  refine ⟨6171787344911200209256621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8229049793214933612342161 6171787344911200209256621)
                  ·
                    refine ⟨2314420254341700078471233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6171787344911200209256621 2314420254341700078471233)
                    ·
                      refine ⟨1735815190756275058853425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314420254341700078471233 1735815190756275058853425)
                      ·
                        rfl

theorem cell23_3380488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_3380488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380488 prefixEnd_3380488 := by exact prefixLift 3380488
  have htrace : WordTrace (prefixWord ++ tailWord_3380488) baseStart_3380488 baseEnd_3380488 := by
    simpa [prefixWord, tailWord_3380488, baseEnd_3380488] using wordTrace_append hprefix tailTrace_3380488
  have hstable : (prefixWord ++ tailWord_3380488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380488).length < 2 ^ (prefixWord ++ tailWord_3380488).sum := by decide
  have hdescent : baseEnd_3380488 < baseStart_3380488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380494 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3380494 : Nat := 118140960795 + 3380494 * 2 ^ 59
def prefixEnd_3380494 : Nat := 4983230072969 + 3 ^ 40 * 3380494 * 2
def baseEnd_3380494 : Nat := 578606090546734011792799

theorem tailTrace_3380494 : CollatzResearch.WordTrace tailWord_3380494 prefixEnd_3380494 578606090546734011792799 := by
  unfold tailWord_3380494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412093176881881906966567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82197830276703370170488357 15412093176881881906966567)
  ·
    refine ⟨23118139765322822860449851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15412093176881881906966567 23118139765322822860449851)
    ·
      refine ⟨34677209647984234290674777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23118139765322822860449851 34677209647984234290674777)
      ·
        refine ⟨26007907235988175718006083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34677209647984234290674777 26007907235988175718006083)
        ·
          refine ⟨39011860853982263577009125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26007907235988175718006083 39011860853982263577009125)
          ·
            refine ⟨7314723910121674420689211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39011860853982263577009125 7314723910121674420689211)
            ·
              refine ⟨10972085865182511631033817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314723910121674420689211 10972085865182511631033817)
              ·
                refine ⟨8229064398886883723275363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972085865182511631033817 8229064398886883723275363)
                ·
                  refine ⟨12343596598330325584913045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229064398886883723275363 12343596598330325584913045)
                  ·
                    refine ⟨578606090546734011792799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12343596598330325584913045 578606090546734011792799)
                    ·
                      rfl

theorem cell23_3380494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3380494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380494 prefixEnd_3380494 := by exact prefixLift 3380494
  have htrace : WordTrace (prefixWord ++ tailWord_3380494) baseStart_3380494 baseEnd_3380494 := by
    simpa [prefixWord, tailWord_3380494, baseEnd_3380494] using wordTrace_append hprefix tailTrace_3380494
  have hstable : (prefixWord ++ tailWord_3380494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380494).length < 2 ^ (prefixWord ++ tailWord_3380494).sum := by decide
  have hdescent : baseEnd_3380494 < baseStart_3380494 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380504 : List Nat := [2, 1, 2, 3, 1, 3, 3, 1, 1, 1, 5]
def baseStart_3380504 : Nat := 118140960795 + 3380504 * 2 ^ 59
def prefixEnd_3380504 : Nat := 4983230072969 + 3 ^ 40 * 3380504 * 2
def baseEnd_3380504 : Nat := 1735823406446746996253351

theorem tailTrace_3380504 : CollatzResearch.WordTrace tailWord_3380504 prefixEnd_3380504 1735823406446746996253351 := by
  unfold tailWord_3380504
  simp only [CollatzResearch.WordTrace]
  refine ⟨61648555072509413481798283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82198073430012551309064377 61648555072509413481798283)
  ·
    refine ⟨92472832608764120222697425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61648555072509413481798283 92472832608764120222697425)
    ·
      refine ⟨69354624456573090167023069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92472832608764120222697425 69354624456573090167023069)
      ·
        refine ⟨26007984171214908812633651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69354624456573090167023069 26007984171214908812633651)
        ·
          refine ⟨39011976256822363218950477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26007984171214908812633651 39011976256822363218950477)
          ·
            refine ⟨14629491096308386207106429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39011976256822363218950477 14629491096308386207106429)
            ·
              refine ⟨5486059161115644827664911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14629491096308386207106429 5486059161115644827664911)
              ·
                refine ⟨8229088741673467241497367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5486059161115644827664911 8229088741673467241497367)
                ·
                  refine ⟨12343633112510200862246051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229088741673467241497367 12343633112510200862246051)
                  ·
                    refine ⟨18515449668765301293369077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12343633112510200862246051 18515449668765301293369077)
                    ·
                      refine ⟨1735823406446746996253351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18515449668765301293369077 1735823406446746996253351)
                      ·
                        rfl

theorem cell23_3380504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_3380504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380504 prefixEnd_3380504 := by exact prefixLift 3380504
  have htrace : WordTrace (prefixWord ++ tailWord_3380504) baseStart_3380504 baseEnd_3380504 := by
    simpa [prefixWord, tailWord_3380504, baseEnd_3380504] using wordTrace_append hprefix tailTrace_3380504
  have hstable : (prefixWord ++ tailWord_3380504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380504).length < 2 ^ (prefixWord ++ tailWord_3380504).sum := by decide
  have hdescent : baseEnd_3380504 < baseStart_3380504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380512 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3380512 : Nat := 118140960795 + 3380512 * 2 ^ 59
def prefixEnd_3380512 : Nat := 4983230072969 + 3 ^ 40 * 3380512 * 2
def baseEnd_3380512 : Nat := 1735827514291982964953315

theorem tailTrace_3380512 : CollatzResearch.WordTrace tailWord_3380512 prefixEnd_3380512 1735827514291982964953315 := by
  unfold tailWord_3380512
  simp only [CollatzResearch.WordTrace]
  refine ⟨61648700964494922164943895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82198267952659896219925193 61648700964494922164943895)
  ·
    refine ⟨92473051446742383247415843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61648700964494922164943895 92473051446742383247415843)
    ·
      refine ⟨138709577170113574871123765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92473051446742383247415843 138709577170113574871123765)
      ·
        refine ⟨13004022859698147644167853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138709577170113574871123765 13004022859698147644167853)
        ·
          refine ⟨4876508572386805366562945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13004022859698147644167853 4876508572386805366562945)
          ·
            refine ⟨3657381429290104024922209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4876508572386805366562945 3657381429290104024922209)
            ·
              refine ⟨2743036071967578018691657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657381429290104024922209 2743036071967578018691657)
              ·
                refine ⟨2057277053975683514018743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743036071967578018691657 2057277053975683514018743)
                ·
                  refine ⟨3085915580963525271028115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057277053975683514018743 3085915580963525271028115)
                  ·
                    refine ⟨4628873371445287906542173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3085915580963525271028115 4628873371445287906542173)
                    ·
                      refine ⟨1735827514291982964953315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4628873371445287906542173 1735827514291982964953315)
                      ·
                        rfl

theorem cell23_3380512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3380512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380512 prefixEnd_3380512 := by exact prefixLift 3380512
  have htrace : WordTrace (prefixWord ++ tailWord_3380512) baseStart_3380512 baseEnd_3380512 := by
    simpa [prefixWord, tailWord_3380512, baseEnd_3380512] using wordTrace_append hprefix tailTrace_3380512
  have hstable : (prefixWord ++ tailWord_3380512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380512).length < 2 ^ (prefixWord ++ tailWord_3380512).sum := by decide
  have hdescent : baseEnd_3380512 < baseStart_3380512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380547 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_3380547 : Nat := 118140960795 + 3380547 * 2 ^ 59
def prefixEnd_3380547 : Nat := 4983230072969 + 3 ^ 40 * 3380547 * 2
def baseEnd_3380547 : Nat := 1735845486114890328015653

theorem tailTrace_3380547 : CollatzResearch.WordTrace tailWord_3380547 prefixEnd_3380547 1735845486114890328015653 := by
  unfold tailWord_3380547
  simp only [CollatzResearch.WordTrace]
  refine ⟨123298678483863045307411895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82199118989242030204941263 123298678483863045307411895)
  ·
    refine ⟨184948017725794567961117843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123298678483863045307411895 184948017725794567961117843)
    ·
      refine ⟨277422026588691851941676765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184948017725794567961117843 277422026588691851941676765)
      ·
        refine ⟨104033259970759444478128787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277422026588691851941676765 104033259970759444478128787)
        ·
          refine ⟨156049889956139166717193181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104033259970759444478128787 156049889956139166717193181)
          ·
            refine ⟨58518708733552187518947443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156049889956139166717193181 58518708733552187518947443)
            ·
              refine ⟨87778063100328281278421165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58518708733552187518947443 87778063100328281278421165)
              ·
                refine ⟨32916773662623105479407937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87778063100328281278421165 32916773662623105479407937)
                ·
                  refine ⟨24687580246967329109555953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32916773662623105479407937 24687580246967329109555953)
                  ·
                    refine ⟨18515685185225496832166965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24687580246967329109555953 18515685185225496832166965)
                    ·
                      refine ⟨1735845486114890328015653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18515685185225496832166965 1735845486114890328015653)
                      ·
                        rfl

theorem cell23_3380547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_3380547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380547 prefixEnd_3380547 := by exact prefixLift 3380547
  have htrace : WordTrace (prefixWord ++ tailWord_3380547) baseStart_3380547 baseEnd_3380547 := by
    simpa [prefixWord, tailWord_3380547, baseEnd_3380547] using wordTrace_append hprefix tailTrace_3380547
  have hstable : (prefixWord ++ tailWord_3380547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380547).length < 2 ^ (prefixWord ++ tailWord_3380547).sum := by decide
  have hdescent : baseEnd_3380547 < baseStart_3380547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380594 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3380594 : Nat := 118140960795 + 3380594 * 2 ^ 59
def prefixEnd_3380594 : Nat := 4983230072969 + 3 ^ 40 * 3380594 * 2
def baseEnd_3380594 : Nat := 1735869619705651644127937

theorem tailTrace_3380594 : CollatzResearch.WordTrace tailWord_3380594 prefixEnd_3380594 1735869619705651644127937 := by
  unfold tailWord_3380594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30825098178673193083593209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82200261809795181556248557 30825098178673193083593209)
  ·
    refine ⟨23118823634004894812694907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30825098178673193083593209 23118823634004894812694907)
    ·
      refine ⟨34678235451007342219042361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23118823634004894812694907 34678235451007342219042361)
      ·
        refine ⟨26008676588255506664281771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34678235451007342219042361 26008676588255506664281771)
        ·
          refine ⟨39013014882383259996422657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26008676588255506664281771 39013014882383259996422657)
          ·
            refine ⟨29259761161787444997316993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39013014882383259996422657 29259761161787444997316993)
            ·
              refine ⟨21944820871340583747987745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29259761161787444997316993 21944820871340583747987745)
              ·
                refine ⟨16458615653505437810990809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21944820871340583747987745 16458615653505437810990809)
                ·
                  refine ⟨12343961740129078358243107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16458615653505437810990809 12343961740129078358243107)
                  ·
                    refine ⟨18515942610193617537364661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12343961740129078358243107 18515942610193617537364661)
                    ·
                      refine ⟨1735869619705651644127937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18515942610193617537364661 1735869619705651644127937)
                      ·
                        rfl

theorem cell23_3380594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3380594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380594 prefixEnd_3380594 := by exact prefixLift 3380594
  have htrace : WordTrace (prefixWord ++ tailWord_3380594) baseStart_3380594 baseEnd_3380594 := by
    simpa [prefixWord, tailWord_3380594, baseEnd_3380594] using wordTrace_append hprefix tailTrace_3380594
  have hstable : (prefixWord ++ tailWord_3380594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380594).length < 2 ^ (prefixWord ++ tailWord_3380594).sum := by decide
  have hdescent : baseEnd_3380594 < baseStart_3380594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380607 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_3380607 : Nat := 118140960795 + 3380607 * 2 ^ 59
def prefixEnd_3380607 : Nat := 4983230072969 + 3 ^ 40 * 3380607 * 2
def baseEnd_3380607 : Nat := 1735876294954160093265377

theorem tailTrace_3380607 : CollatzResearch.WordTrace tailWord_3380607 prefixEnd_3380607 1735876294954160093265377 := by
  unfold tailWord_3380607
  simp only [CollatzResearch.WordTrace]
  refine ⟨123300866863645675554596075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82200577909097117036397383 123300866863645675554596075)
  ·
    refine ⟨184951300295468513331894113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123300866863645675554596075 184951300295468513331894113)
    ·
      refine ⟨138713475221601384998920585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184951300295468513331894113 138713475221601384998920585)
      ·
        refine ⟨104035106416201038749190439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138713475221601384998920585 104035106416201038749190439)
        ·
          refine ⟨156052659624301558123785659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104035106416201038749190439 156052659624301558123785659)
          ·
            refine ⟨234078989436452337185678489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156052659624301558123785659 234078989436452337185678489)
            ·
              refine ⟨175559242077339252889258867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234078989436452337185678489 175559242077339252889258867)
              ·
                refine ⟨263338863116008879333888301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175559242077339252889258867 263338863116008879333888301)
                ·
                  refine ⟨98752073668503329750208113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263338863116008879333888301 98752073668503329750208113)
                  ·
                    refine ⟨74064055251377497312656085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98752073668503329750208113 74064055251377497312656085)
                    ·
                      refine ⟨1735876294954160093265377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74064055251377497312656085 1735876294954160093265377)
                      ·
                        rfl

theorem cell23_3380607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_3380607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380607 prefixEnd_3380607 := by exact prefixLift 3380607
  have htrace : WordTrace (prefixWord ++ tailWord_3380607) baseStart_3380607 baseEnd_3380607 := by
    simpa [prefixWord, tailWord_3380607, baseEnd_3380607] using wordTrace_append hprefix tailTrace_3380607
  have hstable : (prefixWord ++ tailWord_3380607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380607).length < 2 ^ (prefixWord ++ tailWord_3380607).sum := by decide
  have hdescent : baseEnd_3380607 < baseStart_3380607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380627 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 11]
def baseStart_3380627 : Nat := 118140960795 + 3380627 * 2 ^ 59
def prefixEnd_3380627 : Nat := 4983230072969 + 3 ^ 40 * 3380627 * 2
def baseEnd_3380627 : Nat := 578628854855750005005095

theorem tailTrace_3380627 : CollatzResearch.WordTrace tailWord_3380627 prefixEnd_3380627 578628854855750005005095 := by
  unfold tailWord_3380627
  simp only [CollatzResearch.WordTrace]
  refine ⟨123301596323573218970324135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82201064215715479313549423 123301596323573218970324135)
  ·
    refine ⟨184952394485359828455486203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123301596323573218970324135 184952394485359828455486203)
    ·
      refine ⟨277428591728039742683229305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184952394485359828455486203 277428591728039742683229305)
      ·
        refine ⟨208071443796029807012421979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277428591728039742683229305 208071443796029807012421979)
        ·
          refine ⟨312107165694044710518632969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208071443796029807012421979 312107165694044710518632969)
          ·
            refine ⟨234080374270533532888974727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312107165694044710518632969 234080374270533532888974727)
            ·
              refine ⟨351120561405800299333462091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234080374270533532888974727 351120561405800299333462091)
              ·
                refine ⟨526680842108700449000193137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351120561405800299333462091 526680842108700449000193137)
                ·
                  refine ⟨395010631581525336750144853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526680842108700449000193137 395010631581525336750144853)
                  ·
                    refine ⟨578628854855750005005095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 395010631581525336750144853 578628854855750005005095)
                    ·
                      rfl

theorem cell23_3380627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_3380627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380627 prefixEnd_3380627 := by exact prefixLift 3380627
  have htrace : WordTrace (prefixWord ++ tailWord_3380627) baseStart_3380627 baseEnd_3380627 := by
    simpa [prefixWord, tailWord_3380627, baseEnd_3380627] using wordTrace_append hprefix tailTrace_3380627
  have hstable : (prefixWord ++ tailWord_3380627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380627).length < 2 ^ (prefixWord ++ tailWord_3380627).sum := by decide
  have hdescent : baseEnd_3380627 < baseStart_3380627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380642 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_3380642 : Nat := 118140960795 + 3380642 * 2 ^ 59
def prefixEnd_3380642 : Nat := 4983230072969 + 3 ^ 40 * 3380642 * 2
def baseEnd_3380642 : Nat := 1735894266777067456327717

theorem tailTrace_3380642 : CollatzResearch.WordTrace tailWord_3380642 prefixEnd_3380642 1735894266777067456327717 := by
  unfold tailWord_3380642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30825535854629719133030045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82201428945679251021413453 30825535854629719133030045)
  ·
    refine ⟨11559575945486144674886267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30825535854629719133030045 11559575945486144674886267)
    ·
      refine ⟨17339363918229217012329401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559575945486144674886267 17339363918229217012329401)
      ·
        refine ⟨13004522938671912759247051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17339363918229217012329401 13004522938671912759247051)
        ·
          refine ⟨19506784408007869138870577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13004522938671912759247051 19506784408007869138870577)
          ·
            refine ⟨14630088306005901854152933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19506784408007869138870577 14630088306005901854152933)
            ·
              refine ⟨2743141557376106597653675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14630088306005901854152933 2743141557376106597653675)
              ·
                refine ⟨4114712336064159896480513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743141557376106597653675 4114712336064159896480513)
                ·
                  refine ⟨3086034252048119922360385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4114712336064159896480513 3086034252048119922360385)
                  ·
                    refine ⟨2314525689036089941770289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3086034252048119922360385 2314525689036089941770289)
                    ·
                      refine ⟨1735894266777067456327717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314525689036089941770289 1735894266777067456327717)
                      ·
                        rfl

theorem cell23_3380642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_3380642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380642 prefixEnd_3380642 := by exact prefixLift 3380642
  have htrace : WordTrace (prefixWord ++ tailWord_3380642) baseStart_3380642 baseEnd_3380642 := by
    simpa [prefixWord, tailWord_3380642, baseEnd_3380642] using wordTrace_append hprefix tailTrace_3380642
  have hstable : (prefixWord ++ tailWord_3380642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380642).length < 2 ^ (prefixWord ++ tailWord_3380642).sum := by decide
  have hdescent : baseEnd_3380642 < baseStart_3380642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380644 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_3380644 : Nat := 118140960795 + 3380644 * 2 ^ 59
def prefixEnd_3380644 : Nat := 4983230072969 + 3 ^ 40 * 3380644 * 2
def baseEnd_3380644 : Nat := 578631764579458816167569

theorem tailTrace_3380644 : CollatzResearch.WordTrace tailWord_3380644 prefixEnd_3380644 578631764579458816167569 := by
  unfold tailWord_3380644
  simp only [CollatzResearch.WordTrace]
  refine ⟨61651108182255815436846493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82201477576341087249128657 61651108182255815436846493)
  ·
    refine ⟨23119165568345930788817435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61651108182255815436846493 23119165568345930788817435)
    ·
      refine ⟨34678748352518896183226153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23119165568345930788817435 34678748352518896183226153)
      ·
        refine ⟨26009061264389172137419615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34678748352518896183226153 26009061264389172137419615)
        ·
          refine ⟨39013591896583758206129423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26009061264389172137419615 39013591896583758206129423)
          ·
            refine ⟨58520387844875637309194135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39013591896583758206129423 58520387844875637309194135)
            ·
              refine ⟨87780581767313455963791203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58520387844875637309194135 87780581767313455963791203)
              ·
                refine ⟨131670872650970183945686805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87780581767313455963791203 131670872650970183945686805)
                ·
                  refine ⟨6172072155514227372454069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131670872650970183945686805 6172072155514227372454069)
                  ·
                    refine ⟨578631764579458816167569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6172072155514227372454069 578631764579458816167569)
                    ·
                      rfl

theorem cell23_3380644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_3380644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380644 prefixEnd_3380644 := by exact prefixLift 3380644
  have htrace : WordTrace (prefixWord ++ tailWord_3380644) baseStart_3380644 baseEnd_3380644 := by
    simpa [prefixWord, tailWord_3380644, baseEnd_3380644] using wordTrace_append hprefix tailTrace_3380644
  have hstable : (prefixWord ++ tailWord_3380644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380644).length < 2 ^ (prefixWord ++ tailWord_3380644).sum := by decide
  have hdescent : baseEnd_3380644 < baseStart_3380644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380661 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3380661 : Nat := 118140960795 + 3380661 * 2 ^ 59
def prefixEnd_3380661 : Nat := 4983230072969 + 3 ^ 40 * 3380661 * 2
def baseEnd_3380661 : Nat := 578634674303167627330043

theorem tailTrace_3380661 : CollatzResearch.WordTrace tailWord_3380661 prefixEnd_3380661 578634674303167627330043 := by
  unfold tailWord_3380661
  simp only [CollatzResearch.WordTrace]
  refine ⟨123302836405450042777061837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82201890936966695184707891 123302836405450042777061837)
  ·
    refine ⟨46238563652043766041398189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123302836405450042777061837 46238563652043766041398189)
    ·
      refine ⟨17339461369516412265524321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46238563652043766041398189 17339461369516412265524321)
      ·
        refine ⟨13004596027137309199143241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17339461369516412265524321 13004596027137309199143241)
        ·
          refine ⟨9753447020352981899357431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13004596027137309199143241 9753447020352981899357431)
          ·
            refine ⟨14630170530529472849036147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753447020352981899357431 14630170530529472849036147)
            ·
              refine ⟨21945255795794209273554221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630170530529472849036147 21945255795794209273554221)
              ·
                refine ⟨8229470923422828477582833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21945255795794209273554221 8229470923422828477582833)
                ·
                  refine ⟨6172103192567121358187125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8229470923422828477582833 6172103192567121358187125)
                  ·
                    refine ⟨578634674303167627330043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6172103192567121358187125 578634674303167627330043)
                    ·
                      rfl

theorem cell23_3380661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3380661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380661 prefixEnd_3380661 := by exact prefixLift 3380661
  have htrace : WordTrace (prefixWord ++ tailWord_3380661) baseStart_3380661 baseEnd_3380661 := by
    simpa [prefixWord, tailWord_3380661, baseEnd_3380661] using wordTrace_append hprefix tailTrace_3380661
  have hstable : (prefixWord ++ tailWord_3380661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380661).length < 2 ^ (prefixWord ++ tailWord_3380661).sum := by decide
  have hdescent : baseEnd_3380661 < baseStart_3380661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380664 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 1, 3, 4]
def baseStart_3380664 : Nat := 118140960795 + 3380664 * 2 ^ 59
def prefixEnd_3380664 : Nat := 4983230072969 + 3 ^ 40 * 3380664 * 2
def baseEnd_3380664 : Nat := 1735905563351466370252615

theorem tailTrace_3380664 : CollatzResearch.WordTrace tailWord_3380664 prefixEnd_3380664 1735905563351466370252615 := by
  unfold tailWord_3380664
  simp only [CollatzResearch.WordTrace]
  refine ⟨61651472912219587144710523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82201963882959449526280697 61651472912219587144710523)
  ·
    refine ⟨92477209368329380717065785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61651472912219587144710523 92477209368329380717065785)
    ·
      refine ⟨69357907026247035537799339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92477209368329380717065785 69357907026247035537799339)
      ·
        refine ⟨104036860539370553306699009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69357907026247035537799339 104036860539370553306699009)
        ·
          refine ⟨78027645404527914980024257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104036860539370553306699009 78027645404527914980024257)
          ·
            refine ⟨58520734053395936235018193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78027645404527914980024257 58520734053395936235018193)
            ·
              refine ⟨43890550540046952176263645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58520734053395936235018193 43890550540046952176263645)
              ·
                refine ⟨16458956452517607066098867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43890550540046952176263645 16458956452517607066098867)
                ·
                  refine ⟨24688434678776410599148301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16458956452517607066098867 24688434678776410599148301)
                  ·
                    refine ⟨9258163004541153974680613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24688434678776410599148301 9258163004541153974680613)
                    ·
                      refine ⟨1735905563351466370252615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9258163004541153974680613 1735905563351466370252615)
                      ·
                        rfl

theorem cell23_3380664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_3380664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380664 prefixEnd_3380664 := by exact prefixLift 3380664
  have htrace : WordTrace (prefixWord ++ tailWord_3380664) baseStart_3380664 baseEnd_3380664 := by
    simpa [prefixWord, tailWord_3380664, baseEnd_3380664] using wordTrace_append hprefix tailTrace_3380664
  have hstable : (prefixWord ++ tailWord_3380664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380664).length < 2 ^ (prefixWord ++ tailWord_3380664).sum := by decide
  have hdescent : baseEnd_3380664 < baseStart_3380664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380681 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 2, 4, 2]
def baseStart_3380681 : Nat := 118140960795 + 3380681 * 2 ^ 59
def prefixEnd_3380681 : Nat := 4983230072969 + 3 ^ 40 * 3380681 * 2
def baseEnd_3380681 : Nat := 1735914292522592803740037

theorem tailTrace_3380681 : CollatzResearch.WordTrace tailWord_3380681 prefixEnd_3380681 1735914292522592803740037 := by
  unfold tailWord_3380681
  simp only [CollatzResearch.WordTrace]
  refine ⟨123303565865377586192789897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82202377243585057461859931 123303565865377586192789897)
  ·
    refine ⟨92477674399033189644592423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123303565865377586192789897 92477674399033189644592423)
    ·
      refine ⟨138716511598549784466888635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92477674399033189644592423 138716511598549784466888635)
      ·
        refine ⟨208074767397824676700332953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138716511598549784466888635 208074767397824676700332953)
        ·
          refine ⟨156056075548368507525249715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208074767397824676700332953 156056075548368507525249715)
          ·
            refine ⟨234084113322552761287874573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156056075548368507525249715 234084113322552761287874573)
            ·
              refine ⟨87781542495957285482952965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234084113322552761287874573 87781542495957285482952965)
              ·
                refine ⟨16459039217991991028053681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87781542495957285482952965 16459039217991991028053681)
                ·
                  refine ⟨12344279413493993271040261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16459039217991991028053681 12344279413493993271040261)
                  ·
                    refine ⟨2314552390030123738320049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12344279413493993271040261 2314552390030123738320049)
                    ·
                      refine ⟨1735914292522592803740037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314552390030123738320049 1735914292522592803740037)
                      ·
                        rfl

theorem cell23_3380681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 4, 2].length) (baseStart_3380681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380681 prefixEnd_3380681 := by exact prefixLift 3380681
  have htrace : WordTrace (prefixWord ++ tailWord_3380681) baseStart_3380681 baseEnd_3380681 := by
    simpa [prefixWord, tailWord_3380681, baseEnd_3380681] using wordTrace_append hprefix tailTrace_3380681
  have hstable : (prefixWord ++ tailWord_3380681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380681).length < 2 ^ (prefixWord ++ tailWord_3380681).sum := by decide
  have hdescent : baseEnd_3380681 < baseStart_3380681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380698 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2]
def baseStart_3380698 : Nat := 118140960795 + 3380698 * 2 ^ 59
def prefixEnd_3380698 : Nat := 4983230072969 + 3 ^ 40 * 3380698 * 2
def baseEnd_3380698 : Nat := 1735923021693719237227459

theorem tailTrace_3380698 : CollatzResearch.WordTrace tailWord_3380698 prefixEnd_3380698 1735923021693719237227459 := by
  unfold tailWord_3380698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826046476578999524039687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82202790604210665397439165 30826046476578999524039687)
  ·
    refine ⟨46239069714868499286059531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30826046476578999524039687 46239069714868499286059531)
    ·
      refine ⟨69358604572302748929089297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46239069714868499286059531 69358604572302748929089297)
      ·
        refine ⟨52018953429227061696816973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69358604572302748929089297 52018953429227061696816973)
        ·
          refine ⟨19507107535960148136306365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52018953429227061696816973 19507107535960148136306365)
          ·
            refine ⟨7315165325985055551114887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19507107535960148136306365 7315165325985055551114887)
            ·
              refine ⟨10972747988977583326672331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315165325985055551114887 10972747988977583326672331)
              ·
                refine ⟨16459121983466374990008497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10972747988977583326672331 16459121983466374990008497)
                ·
                  refine ⟨12344341487599781242506373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16459121983466374990008497 12344341487599781242506373)
                  ·
                    refine ⟨2314564028924958982969945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12344341487599781242506373 2314564028924958982969945)
                    ·
                      refine ⟨1735923021693719237227459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314564028924958982969945 1735923021693719237227459)
                      ·
                        rfl

theorem cell23_3380698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_3380698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380698 prefixEnd_3380698 := by exact prefixLift 3380698
  have htrace : WordTrace (prefixWord ++ tailWord_3380698) baseStart_3380698 baseEnd_3380698 := by
    simpa [prefixWord, tailWord_3380698, baseEnd_3380698] using wordTrace_append hprefix tailTrace_3380698
  have hstable : (prefixWord ++ tailWord_3380698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380698).length < 2 ^ (prefixWord ++ tailWord_3380698).sum := by decide
  have hdescent : baseEnd_3380698 < baseStart_3380698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380738 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_3380738 : Nat := 118140960795 + 3380738 * 2 ^ 59
def prefixEnd_3380738 : Nat := 4983230072969 + 3 ^ 40 * 3380738 * 2
def baseEnd_3380738 : Nat := 192882617879988786747475

theorem tailTrace_3380738 : CollatzResearch.WordTrace tailWord_3380738 prefixEnd_3380738 192882617879988786747475 := by
  unfold tailWord_3380738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826411206542771231903717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82203763217447389951743245 30826411206542771231903717)
  ·
    refine ⟨5779952101226769605981947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30826411206542771231903717 5779952101226769605981947)
    ·
      refine ⟨8669928151840154408972921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779952101226769605981947 8669928151840154408972921)
      ·
        refine ⟨6502446113880115806729691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8669928151840154408972921 6502446113880115806729691)
        ·
          refine ⟨9753669170820173710094537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502446113880115806729691 9753669170820173710094537)
          ·
            refine ⟨7315251878115130282570903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9753669170820173710094537 7315251878115130282570903)
            ·
              refine ⟨10972877817172695423856355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315251878115130282570903 10972877817172695423856355)
              ·
                refine ⟨16459316725759043135784533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10972877817172695423856355 16459316725759043135784533)
                ·
                  refine ⟨192882617879988786747475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16459316725759043135784533 192882617879988786747475)
                  ·
                    rfl

theorem cell23_3380738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_3380738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380738 prefixEnd_3380738 := by exact prefixLift 3380738
  have htrace : WordTrace (prefixWord ++ tailWord_3380738) baseStart_3380738 baseEnd_3380738 := by
    simpa [prefixWord, tailWord_3380738, baseEnd_3380738] using wordTrace_append hprefix tailTrace_3380738
  have hstable : (prefixWord ++ tailWord_3380738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380738).length < 2 ^ (prefixWord ++ tailWord_3380738).sum := by decide
  have hdescent : baseEnd_3380738 < baseStart_3380738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380768 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 1, 5]
def baseStart_3380768 : Nat := 118140960795 + 3380768 * 2 ^ 59
def prefixEnd_3380768 : Nat := 4983230072969 + 3 ^ 40 * 3380768 * 2
def baseEnd_3380768 : Nat := 578652988446511321117379

theorem tailTrace_3380768 : CollatzResearch.WordTrace tailWord_3380768 prefixEnd_3380768 578652988446511321117379 := by
  unfold tailWord_3380768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61653369508031200025603479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82204492677374933367471305 61653369508031200025603479)
  ·
    refine ⟨92480054262046800038405219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61653369508031200025603479 92480054262046800038405219)
    ·
      refine ⟨138720081393070200057607829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92480054262046800038405219 138720081393070200057607829)
      ·
        refine ⟨6502503815300165627700367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138720081393070200057607829 6502503815300165627700367)
        ·
          refine ⟨9753755722950248441550551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502503815300165627700367 9753755722950248441550551)
          ·
            refine ⟨14630633584425372662325827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753755722950248441550551 14630633584425372662325827)
            ·
              refine ⟨21945950376638058993488741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630633584425372662325827 21945950376638058993488741)
              ·
                refine ⟨4114865695619636061279139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21945950376638058993488741 4114865695619636061279139)
                ·
                  refine ⟨6172298543429454091918709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114865695619636061279139 6172298543429454091918709)
                  ·
                    refine ⟨578652988446511321117379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6172298543429454091918709 578652988446511321117379)
                    ·
                      rfl

theorem cell23_3380768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 1, 5].length) (baseStart_3380768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380768 prefixEnd_3380768 := by exact prefixLift 3380768
  have htrace : WordTrace (prefixWord ++ tailWord_3380768) baseStart_3380768 baseEnd_3380768 := by
    simpa [prefixWord, tailWord_3380768, baseEnd_3380768] using wordTrace_append hprefix tailTrace_3380768
  have hstable : (prefixWord ++ tailWord_3380768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380768).length < 2 ^ (prefixWord ++ tailWord_3380768).sum := by decide
  have hdescent : baseEnd_3380768 < baseStart_3380768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380791 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_3380791 : Nat := 118140960795 + 3380791 * 2 ^ 59
def prefixEnd_3380791 : Nat := 4983230072969 + 3 ^ 40 * 3380791 * 2
def baseEnd_3380791 : Nat := 1735970775394587373364531

theorem tailTrace_3380791 : CollatzResearch.WordTrace tailWord_3380791 prefixEnd_3380791 1735970775394587373364531 := by
  unfold tailWord_3380791
  simp only [CollatzResearch.WordTrace]
  refine ⟨123307577894979074979294227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82205051929986049986196151 123307577894979074979294227)
  ·
    refine ⟨184961366842468612468941341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123307577894979074979294227 184961366842468612468941341)
    ·
      refine ⟨69360512565925729675853003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184961366842468612468941341 69360512565925729675853003)
      ·
        refine ⟨104040768848888594513779505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69360512565925729675853003 104040768848888594513779505)
        ·
          refine ⟨78030576636666445885334629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104040768848888594513779505 78030576636666445885334629)
          ·
            refine ⟨14630733119374958603500243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78030576636666445885334629 14630733119374958603500243)
            ·
              refine ⟨21946099679062437905250365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630733119374958603500243 21946099679062437905250365)
              ·
                refine ⟨8229787379648414214468887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21946099679062437905250365 8229787379648414214468887)
                ·
                  refine ⟨12344681069472621321703331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229787379648414214468887 12344681069472621321703331)
                  ·
                    refine ⟨18517021604208931982554997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12344681069472621321703331 18517021604208931982554997)
                    ·
                      refine ⟨1735970775394587373364531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18517021604208931982554997 1735970775394587373364531)
                      ·
                        rfl

theorem cell23_3380791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_3380791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380791 prefixEnd_3380791 := by exact prefixLift 3380791
  have htrace : WordTrace (prefixWord ++ tailWord_3380791) baseStart_3380791 baseEnd_3380791 := by
    simpa [prefixWord, tailWord_3380791, baseEnd_3380791] using wordTrace_append hprefix tailTrace_3380791
  have hstable : (prefixWord ++ tailWord_3380791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380791).length < 2 ^ (prefixWord ++ tailWord_3380791).sum := by decide
  have hdescent : baseEnd_3380791 < baseStart_3380791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380801 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3380801 : Nat := 118140960795 + 3380801 * 2 ^ 59
def prefixEnd_3380801 : Nat := 4983230072969 + 3 ^ 40 * 3380801 * 2
def baseEnd_3380801 : Nat := 1735975910201132334239485

theorem tailTrace_3380801 : CollatzResearch.WordTrace tailWord_3380801 prefixEnd_3380801 1735975910201132334239485 := by
  unfold tailWord_3380801
  simp only [CollatzResearch.WordTrace]
  refine ⟨123307942624942846687158257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82205295083295231124772171 123307942624942846687158257)
  ·
    refine ⟨92480956968707135015368693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123307942624942846687158257 92480956968707135015368693)
    ·
      refine ⟨8670089715816293907690815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92480956968707135015368693 8670089715816293907690815)
      ·
        refine ⟨13005134573724440861536223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670089715816293907690815 13005134573724440861536223)
        ·
          refine ⟨19507701860586661292304335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005134573724440861536223 19507701860586661292304335)
          ·
            refine ⟨29261552790879991938456503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19507701860586661292304335 29261552790879991938456503)
            ·
              refine ⟨43892329186319987907684755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29261552790879991938456503 43892329186319987907684755)
              ·
                refine ⟨65838493779479981861527133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43892329186319987907684755 65838493779479981861527133)
                ·
                  refine ⟨24689435167304993198072675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65838493779479981861527133 24689435167304993198072675)
                  ·
                    refine ⟨37034152750957489797109013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24689435167304993198072675 37034152750957489797109013)
                    ·
                      refine ⟨1735975910201132334239485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37034152750957489797109013 1735975910201132334239485)
                      ·
                        rfl

theorem cell23_3380801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3380801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380801 prefixEnd_3380801 := by exact prefixLift 3380801
  have htrace : WordTrace (prefixWord ++ tailWord_3380801) baseStart_3380801 baseEnd_3380801 := by
    simpa [prefixWord, tailWord_3380801, baseEnd_3380801] using wordTrace_append hprefix tailTrace_3380801
  have hstable : (prefixWord ++ tailWord_3380801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380801).length < 2 ^ (prefixWord ++ tailWord_3380801).sum := by decide
  have hdescent : baseEnd_3380801 < baseStart_3380801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380842 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3]
def baseStart_3380842 : Nat := 118140960795 + 3380842 * 2 ^ 59
def prefixEnd_3380842 : Nat := 4983230072969 + 3 ^ 40 * 3380842 * 2
def baseEnd_3380842 : Nat := 1735996962907966673826797

theorem tailTrace_3380842 : CollatzResearch.WordTrace tailWord_3380842 prefixEnd_3380842 1735996962907966673826797 := by
  unfold tailWord_3380842
  simp only [CollatzResearch.WordTrace]
  refine ⟨30827359504448577672350195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82206292011862873792933853 30827359504448577672350195)
  ·
    refine ⟨46241039256672866508525293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30827359504448577672350195 46241039256672866508525293)
    ·
      refine ⟨17340389721252324940696985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46241039256672866508525293 17340389721252324940696985)
      ·
        refine ⟨13005292290939243705522739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17340389721252324940696985 13005292290939243705522739)
        ·
          refine ⟨19507938436408865558284109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005292290939243705522739 19507938436408865558284109)
          ·
            refine ⟨7315476913653324584356541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19507938436408865558284109 7315476913653324584356541)
            ·
              refine ⟨2743303842619996719133703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7315476913653324584356541 2743303842619996719133703)
              ·
                refine ⟨4114955763929995078700555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743303842619996719133703 4114955763929995078700555)
                ·
                  refine ⟨6172433645894992618050833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114955763929995078700555 6172433645894992618050833)
                  ·
                    refine ⟨4629325234421244463538125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6172433645894992618050833 4629325234421244463538125)
                    ·
                      refine ⟨1735996962907966673826797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4629325234421244463538125 1735996962907966673826797)
                      ·
                        rfl

theorem cell23_3380842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_3380842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380842 prefixEnd_3380842 := by exact prefixLift 3380842
  have htrace : WordTrace (prefixWord ++ tailWord_3380842) baseStart_3380842 baseEnd_3380842 := by
    simpa [prefixWord, tailWord_3380842, baseEnd_3380842] using wordTrace_append hprefix tailTrace_3380842
  have hstable : (prefixWord ++ tailWord_3380842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380842).length < 2 ^ (prefixWord ++ tailWord_3380842).sum := by decide
  have hdescent : baseEnd_3380842 < baseStart_3380842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380865 : List Nat := [1, 2, 4, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_3380865 : Nat := 118140960795 + 3380865 * 2 ^ 59
def prefixEnd_3380865 : Nat := 4983230072969 + 3 ^ 40 * 3380865 * 2
def baseEnd_3380865 : Nat := 1736008772963020083839191

theorem tailTrace_3380865 : CollatzResearch.WordTrace tailWord_3380865 prefixEnd_3380865 1736008772963020083839191 := by
  unfold tailWord_3380865
  simp only [CollatzResearch.WordTrace]
  refine ⟨123310276896710985617488049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82206851264473990411658699 123310276896710985617488049)
  ·
    refine ⟨92482707672533239213116037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123310276896710985617488049 92482707672533239213116037)
    ·
      refine ⟨17340507688599982352459257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92482707672533239213116037 17340507688599982352459257)
      ·
        refine ⟨13005380766449986764344443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17340507688599982352459257 13005380766449986764344443)
        ·
          refine ⟨19508071149674980146516665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005380766449986764344443 19508071149674980146516665)
          ·
            refine ⟨14631053362256235109887499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19508071149674980146516665 14631053362256235109887499)
            ·
              refine ⟨21946580043384352664831249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14631053362256235109887499 21946580043384352664831249)
              ·
                refine ⟨16459935032538264498623437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21946580043384352664831249 16459935032538264498623437)
                ·
                  refine ⟨6172475637201849186983789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16459935032538264498623437 6172475637201849186983789)
                  ·
                    refine ⟨2314678363950693445118921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6172475637201849186983789 2314678363950693445118921)
                    ·
                      refine ⟨1736008772963020083839191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314678363950693445118921 1736008772963020083839191)
                      ·
                        rfl

theorem cell23_3380865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_3380865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380865 prefixEnd_3380865 := by exact prefixLift 3380865
  have htrace : WordTrace (prefixWord ++ tailWord_3380865) baseStart_3380865 baseEnd_3380865 := by
    simpa [prefixWord, tailWord_3380865, baseEnd_3380865] using wordTrace_append hprefix tailTrace_3380865
  have hstable : (prefixWord ++ tailWord_3380865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380865).length < 2 ^ (prefixWord ++ tailWord_3380865).sum := by decide
  have hdescent : baseEnd_3380865 < baseStart_3380865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380871 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 1, 8]
def baseStart_3380871 : Nat := 118140960795 + 3380871 * 2 ^ 59
def prefixEnd_3380871 : Nat := 4983230072969 + 3 ^ 40 * 3380871 * 2
def baseEnd_3380871 : Nat := 578670617948982353454721

theorem tailTrace_3380871 : CollatzResearch.WordTrace tailWord_3380871 prefixEnd_3380871 578670617948982353454721 := by
  unfold tailWord_3380871
  simp only [CollatzResearch.WordTrace]
  refine ⟨123310495734689248642206467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82206997156459499094804311 123310495734689248642206467)
  ·
    refine ⟨184965743602033872963309701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123310495734689248642206467 184965743602033872963309701)
    ·
      refine ⟨34681076925381351180620569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184965743602033872963309701 34681076925381351180620569)
      ·
        refine ⟨26010807694036013385465427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34681076925381351180620569 26010807694036013385465427)
        ·
          refine ⟨39016211541054020078198141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26010807694036013385465427 39016211541054020078198141)
          ·
            refine ⟨14631079327895257529324303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39016211541054020078198141 14631079327895257529324303)
            ·
              refine ⟨21946618991842886293986455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14631079327895257529324303 21946618991842886293986455)
              ·
                refine ⟨32919928487764329440979683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21946618991842886293986455 32919928487764329440979683)
                ·
                  refine ⟨49379892731646494161469525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32919928487764329440979683 49379892731646494161469525)
                  ·
                    refine ⟨578670617948982353454721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49379892731646494161469525 578670617948982353454721)
                    ·
                      rfl

theorem cell23_3380871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_3380871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380871 prefixEnd_3380871 := by exact prefixLift 3380871
  have htrace : WordTrace (prefixWord ++ tailWord_3380871) baseStart_3380871 baseEnd_3380871 := by
    simpa [prefixWord, tailWord_3380871, baseEnd_3380871] using wordTrace_append hprefix tailTrace_3380871
  have hstable : (prefixWord ++ tailWord_3380871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380871).length < 2 ^ (prefixWord ++ tailWord_3380871).sum := by decide
  have hdescent : baseEnd_3380871 < baseStart_3380871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380872 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3380872 : Nat := 118140960795 + 3380872 * 2 ^ 59
def prefixEnd_3380872 : Nat := 4983230072969 + 3 ^ 40 * 3380872 * 2
def baseEnd_3380872 : Nat := 1736012367327601556451659

theorem tailTrace_3380872 : CollatzResearch.WordTrace tailWord_3380872 prefixEnd_3380872 1736012367327601556451659 := by
  unfold tailWord_3380872
  simp only [CollatzResearch.WordTrace]
  refine ⟨61655266103842812906496435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82207021471790417208661913 61655266103842812906496435)
  ·
    refine ⟨92482899155764219359744653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61655266103842812906496435 92482899155764219359744653)
    ·
      refine ⟨34681087183411582259904245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92482899155764219359744653 34681087183411582259904245)
      ·
        refine ⟨3251351923444835836866023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34681087183411582259904245 3251351923444835836866023)
        ·
          refine ⟨4877027885167253755299035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251351923444835836866023 4877027885167253755299035)
          ·
            refine ⟨7315541827750880632948553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877027885167253755299035 7315541827750880632948553)
            ·
              refine ⟨5486656370813160474711415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7315541827750880632948553 5486656370813160474711415)
              ·
                refine ⟨8229984556219740712067123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5486656370813160474711415 8229984556219740712067123)
                ·
                  refine ⟨12344976834329611068100685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8229984556219740712067123 12344976834329611068100685)
                  ·
                    refine ⟨4629366312873604150537757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12344976834329611068100685 4629366312873604150537757)
                    ·
                      refine ⟨1736012367327601556451659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4629366312873604150537757 1736012367327601556451659)
                      ·
                        rfl

theorem cell23_3380872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3380872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380872 prefixEnd_3380872 := by exact prefixLift 3380872
  have htrace : WordTrace (prefixWord ++ tailWord_3380872) baseStart_3380872 baseEnd_3380872 := by
    simpa [prefixWord, tailWord_3380872, baseEnd_3380872] using wordTrace_append hprefix tailTrace_3380872
  have hstable : (prefixWord ++ tailWord_3380872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380872).length < 2 ^ (prefixWord ++ tailWord_3380872).sum := by decide
  have hdescent : baseEnd_3380872 < baseStart_3380872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380881 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 5]
def baseStart_3380881 : Nat := 118140960795 + 3380881 * 2 ^ 59
def prefixEnd_3380881 : Nat := 4983230072969 + 3 ^ 40 * 3380881 * 2
def baseEnd_3380881 : Nat := 1736016988653492021239117

theorem tailTrace_3380881 : CollatzResearch.WordTrace tailWord_3380881 prefixEnd_3380881 1736016988653492021239117 := by
  unfold tailWord_3380881
  simp only [CollatzResearch.WordTrace]
  refine ⟨123310860464653020350070497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82207240309768680233380331 123310860464653020350070497)
  ·
    refine ⟨92483145348489765262552873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123310860464653020350070497 92483145348489765262552873)
    ·
      refine ⟨69362359011367323946914655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92483145348489765262552873 69362359011367323946914655)
      ·
        refine ⟨104043538517050985920371983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69362359011367323946914655 104043538517050985920371983)
        ·
          refine ⟨156065307775576478880557975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104043538517050985920371983 156065307775576478880557975)
          ·
            refine ⟨234097961663364718320836963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156065307775576478880557975 234097961663364718320836963)
            ·
              refine ⟨351146942495047077481255445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234097961663364718320836963 351146942495047077481255445)
              ·
                refine ⟨16460012929455331756933849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 351146942495047077481255445 16460012929455331756933849)
                ·
                  refine ⟨12345009697091498817700387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16460012929455331756933849 12345009697091498817700387)
                  ·
                    refine ⟨18517514545637248226550581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12345009697091498817700387 18517514545637248226550581)
                    ·
                      refine ⟨1736016988653492021239117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18517514545637248226550581 1736016988653492021239117)
                      ·
                        rfl

theorem cell23_3380881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_3380881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380881 prefixEnd_3380881 := by exact prefixLift 3380881
  have htrace : WordTrace (prefixWord ++ tailWord_3380881) baseStart_3380881 baseEnd_3380881 := by
    simpa [prefixWord, tailWord_3380881, baseEnd_3380881] using wordTrace_append hprefix tailTrace_3380881
  have hstable : (prefixWord ++ tailWord_3380881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380881).length < 2 ^ (prefixWord ++ tailWord_3380881).sum := by decide
  have hdescent : baseEnd_3380881 < baseStart_3380881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380912 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 2, 2, 2]
def baseStart_3380912 : Nat := 118140960795 + 3380912 * 2 ^ 59
def prefixEnd_3380912 : Nat := 4983230072969 + 3 ^ 40 * 3380912 * 2
def baseEnd_3380912 : Nat := 1736032906553781399951475

theorem tailTrace_3380912 : CollatzResearch.WordTrace tailWord_3380912 prefixEnd_3380912 1736032906553781399951475 := by
  unfold tailWord_3380912
  simp only [CollatzResearch.WordTrace]
  refine ⟨61655995563770356322224495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82207994085027141762965993 61655995563770356322224495)
  ·
    refine ⟨92483993345655534483336743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61655995563770356322224495 92483993345655534483336743)
    ·
      refine ⟨138725990018483301725005115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92483993345655534483336743 138725990018483301725005115)
      ·
        refine ⟨208088985027724952587507673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138725990018483301725005115 208088985027724952587507673)
        ·
          refine ⟨156066738770793714440630755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208088985027724952587507673 156066738770793714440630755)
          ·
            refine ⟨234100108156190571660946133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156066738770793714440630755 234100108156190571660946133)
            ·
              refine ⟨5486721284910716523303425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 234100108156190571660946133 5486721284910716523303425)
              ·
                refine ⟨4115040963683037392477569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486721284910716523303425 4115040963683037392477569)
                ·
                  refine ⟨3086280722762278044358177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4115040963683037392477569 3086280722762278044358177)
                  ·
                    refine ⟨2314710542071708533268633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3086280722762278044358177 2314710542071708533268633)
                    ·
                      refine ⟨1736032906553781399951475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314710542071708533268633 1736032906553781399951475)
                      ·
                        rfl

theorem cell23_3380912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 2, 2, 2].length) (baseStart_3380912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380912 prefixEnd_3380912 := by exact prefixLift 3380912
  have htrace : WordTrace (prefixWord ++ tailWord_3380912) baseStart_3380912 baseEnd_3380912 := by
    simpa [prefixWord, tailWord_3380912, baseEnd_3380912] using wordTrace_append hprefix tailTrace_3380912
  have hstable : (prefixWord ++ tailWord_3380912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380912).length < 2 ^ (prefixWord ++ tailWord_3380912).sum := by decide
  have hdescent : baseEnd_3380912 < baseStart_3380912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380928 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3]
def baseStart_3380928 : Nat := 118140960795 + 3380928 * 2 ^ 59
def prefixEnd_3380928 : Nat := 4983230072969 + 3 ^ 40 * 3380928 * 2
def baseEnd_3380928 : Nat := 1736041122244253337351401

theorem tailTrace_3380928 : CollatzResearch.WordTrace tailWord_3380928 prefixEnd_3380928 1736041122244253337351401 := by
  unfold tailWord_3380928
  simp only [CollatzResearch.WordTrace]
  refine ⟨61656287347741373688515719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82208383130321831584687625 61656287347741373688515719)
  ·
    refine ⟨92484431021612060532773579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61656287347741373688515719 92484431021612060532773579)
    ·
      refine ⟨138726646532418090799160369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92484431021612060532773579 138726646532418090799160369)
      ·
        refine ⟨104044984899313568099370277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138726646532418090799160369 104044984899313568099370277)
        ·
          refine ⟨19508434668621294018631927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104044984899313568099370277 19508434668621294018631927)
          ·
            refine ⟨29262652002931941027947891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19508434668621294018631927 29262652002931941027947891)
            ·
              refine ⟨43893978004397911541921837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29262652002931941027947891 43893978004397911541921837)
              ·
                refine ⟨16460241751649216828220689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43893978004397911541921837 16460241751649216828220689)
                ·
                  refine ⟨12345181313736912621165517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16460241751649216828220689 12345181313736912621165517)
                  ·
                    refine ⟨4629442992651342232937069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12345181313736912621165517 4629442992651342232937069)
                    ·
                      refine ⟨1736041122244253337351401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4629442992651342232937069 1736041122244253337351401)
                      ·
                        rfl

theorem cell23_3380928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_3380928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380928 prefixEnd_3380928 := by exact prefixLift 3380928
  have htrace : WordTrace (prefixWord ++ tailWord_3380928) baseStart_3380928 baseEnd_3380928 := by
    simpa [prefixWord, tailWord_3380928, baseEnd_3380928] using wordTrace_append hprefix tailTrace_3380928
  have hstable : (prefixWord ++ tailWord_3380928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380928).length < 2 ^ (prefixWord ++ tailWord_3380928).sum := by decide
  have hdescent : baseEnd_3380928 < baseStart_3380928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3380980 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3380980 : Nat := 118140960795 + 3380980 * 2 ^ 59
def prefixEnd_3380980 : Nat := 4983230072969 + 3 ^ 40 * 3380980 * 2
def baseEnd_3380980 : Nat := 1736067823238287133901163

theorem tailTrace_3380980 : CollatzResearch.WordTrace tailWord_3380980 prefixEnd_3380980 1736067823238287133901163 := by
  unfold tailWord_3380980
  simp only [CollatzResearch.WordTrace]
  refine ⟨61657235645647180128962197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82209647527529573505282929 61657235645647180128962197)
  ·
    refine ⟨2890182920889711568545103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61657235645647180128962197 2890182920889711568545103)
    ·
      refine ⟨4335274381334567352817655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2890182920889711568545103 4335274381334567352817655)
      ·
        refine ⟨6502911572001851029226483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335274381334567352817655 6502911572001851029226483)
        ·
          refine ⟨9754367358002776543839725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6502911572001851029226483 9754367358002776543839725)
          ·
            refine ⟨3657887759251041203939897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9754367358002776543839725 3657887759251041203939897)
            ·
              refine ⟨2743415819438280902954923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657887759251041203939897 2743415819438280902954923)
              ·
                refine ⟨4115123729157421354432385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743415819438280902954923 4115123729157421354432385)
                ·
                  refine ⟨3086342796868066015824289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4115123729157421354432385 3086342796868066015824289)
                  ·
                    refine ⟨2314757097651049511868217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3086342796868066015824289 2314757097651049511868217)
                    ·
                      refine ⟨1736067823238287133901163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314757097651049511868217 1736067823238287133901163)
                      ·
                        rfl

theorem cell23_3380980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3380980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3380980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3380980 prefixEnd_3380980 := by exact prefixLift 3380980
  have htrace : WordTrace (prefixWord ++ tailWord_3380980) baseStart_3380980 baseEnd_3380980 := by
    simpa [prefixWord, tailWord_3380980, baseEnd_3380980] using wordTrace_append hprefix tailTrace_3380980
  have hstable : (prefixWord ++ tailWord_3380980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3380980).length < 2 ^ (prefixWord ++ tailWord_3380980).sum := by decide
  have hdescent : baseEnd_3380980 < baseStart_3380980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3380980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381025 : List Nat := [1, 2, 3, 2, 1, 4, 2, 2, 6]
def baseStart_3381025 : Nat := 118140960795 + 3381025 * 2 ^ 59
def prefixEnd_3381025 : Nat := 4983230072969 + 3 ^ 40 * 3381025 * 2
def baseEnd_3381025 : Nat := 192898992207526606426495

theorem tailTrace_3381025 : CollatzResearch.WordTrace tailWord_3381025 prefixEnd_3381025 192898992207526606426495 := by
  unfold tailWord_3381025
  simp only [CollatzResearch.WordTrace]
  refine ⟨123316112576131332943312529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82210741717420888628875019 123316112576131332943312529)
  ·
    refine ⟨92487084432098499707484397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123316112576131332943312529 92487084432098499707484397)
    ·
      refine ⟨34682656662036937390306649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92487084432098499707484397 34682656662036937390306649)
      ·
        refine ⟨26011992496527703042729987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34682656662036937390306649 26011992496527703042729987)
        ·
          refine ⟨39017988744791554564094981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26011992496527703042729987 39017988744791554564094981)
          ·
            refine ⟨7315872889648416480767809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39017988744791554564094981 7315872889648416480767809)
            ·
              refine ⟨5486904667236312360575857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7315872889648416480767809 5486904667236312360575857)
              ·
                refine ⟨4115178500427234270431893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5486904667236312360575857 4115178500427234270431893)
                ·
                  refine ⟨192898992207526606426495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4115178500427234270431893 192898992207526606426495)
                  ·
                    rfl

theorem cell23_3381025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 6].length) (baseStart_3381025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381025 prefixEnd_3381025 := by exact prefixLift 3381025
  have htrace : WordTrace (prefixWord ++ tailWord_3381025) baseStart_3381025 baseEnd_3381025 := by
    simpa [prefixWord, tailWord_3381025, baseEnd_3381025] using wordTrace_append hprefix tailTrace_3381025
  have hstable : (prefixWord ++ tailWord_3381025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381025).length < 2 ^ (prefixWord ++ tailWord_3381025).sum := by decide
  have hdescent : baseEnd_3381025 < baseStart_3381025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381029 : List Nat := [1, 3, 1, 2, 3, 2, 4, 2, 1, 4]
def baseStart_3381029 : Nat := 118140960795 + 3381029 * 2 ^ 59
def prefixEnd_3381029 : Nat := 4983230072969 + 3 ^ 40 * 3381029 * 2
def baseEnd_3381029 : Nat := 578697661263452480729479

theorem tailTrace_3381029 : CollatzResearch.WordTrace tailWord_3381029 prefixEnd_3381029 578697661263452480729479 := by
  unfold tailWord_3381029
  simp only [CollatzResearch.WordTrace]
  refine ⟨123316258468116841626458141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82210838978744561084305427 123316258468116841626458141)
  ·
    refine ⟨46243596925543815609921803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123316258468116841626458141 46243596925543815609921803)
    ·
      refine ⟨69365395388315723414882705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46243596925543815609921803 69365395388315723414882705)
      ·
        refine ⟨52024046541236792561162029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69365395388315723414882705 52024046541236792561162029)
        ·
          refine ⟨19509017452963797210435761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52024046541236792561162029 19509017452963797210435761)
          ·
            refine ⟨14631763089722847907826821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19509017452963797210435761 14631763089722847907826821)
            ·
              refine ⟨2743455579323033982717529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14631763089722847907826821 2743455579323033982717529)
              ·
                refine ⟨2057591684492275487038147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743455579323033982717529 2057591684492275487038147)
                ·
                  refine ⟨3086387526738413230557221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057591684492275487038147 3086387526738413230557221)
                  ·
                    refine ⟨578697661263452480729479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3086387526738413230557221 578697661263452480729479)
                    ·
                      rfl

theorem cell23_3381029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2, 1, 4].length) (baseStart_3381029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381029 prefixEnd_3381029 := by exact prefixLift 3381029
  have htrace : WordTrace (prefixWord ++ tailWord_3381029) baseStart_3381029 baseEnd_3381029 := by
    simpa [prefixWord, tailWord_3381029, baseEnd_3381029] using wordTrace_append hprefix tailTrace_3381029
  have hstable : (prefixWord ++ tailWord_3381029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381029).length < 2 ^ (prefixWord ++ tailWord_3381029).sum := by decide
  have hdescent : baseEnd_3381029 < baseStart_3381029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381095 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_3381095 : Nat := 118140960795 + 3381095 * 2 ^ 59
def prefixEnd_3381095 : Nat := 4983230072969 + 3 ^ 40 * 3381095 * 2
def baseEnd_3381095 : Nat := 1736126873513554183963133

theorem tailTrace_3381095 : CollatzResearch.WordTrace tailWord_3381095 prefixEnd_3381095 1736126873513554183963133 := by
  unfold tailWord_3381095
  simp only [CollatzResearch.WordTrace]
  refine ⟨123318665685877734898360739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82212443790585156598907159 123318665685877734898360739)
  ·
    refine ⟨184977998528816602347541109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123318665685877734898360739 184977998528816602347541109)
    ·
      refine ⟨17341687362076556470081979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184977998528816602347541109 17341687362076556470081979)
      ·
        refine ⟨26012531043114834705122969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17341687362076556470081979 26012531043114834705122969)
        ·
          refine ⟨19509398282336126028842227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26012531043114834705122969 19509398282336126028842227)
          ·
            refine ⟨29264097423504189043263341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19509398282336126028842227 29264097423504189043263341)
            ·
              refine ⟨10974036533814070891223753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29264097423504189043263341 10974036533814070891223753)
              ·
                refine ⟨8230527400360553168417815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10974036533814070891223753 8230527400360553168417815)
                ·
                  refine ⟨12345791100540829752626723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230527400360553168417815 12345791100540829752626723)
                  ·
                    refine ⟨18518686650811244628940085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12345791100540829752626723 18518686650811244628940085)
                    ·
                      refine ⟨1736126873513554183963133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18518686650811244628940085 1736126873513554183963133)
                      ·
                        rfl

theorem cell23_3381095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_3381095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381095 prefixEnd_3381095 := by exact prefixLift 3381095
  have htrace : WordTrace (prefixWord ++ tailWord_3381095) baseStart_3381095 baseEnd_3381095 := by
    simpa [prefixWord, tailWord_3381095, baseEnd_3381095] using wordTrace_append hprefix tailTrace_3381095
  have hstable : (prefixWord ++ tailWord_3381095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381095).length < 2 ^ (prefixWord ++ tailWord_3381095).sum := by decide
  have hdescent : baseEnd_3381095 < baseStart_3381095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381102 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3381102 : Nat := 118140960795 + 3381102 * 2 ^ 59
def prefixEnd_3381102 : Nat := 4983230072969 + 3 ^ 40 * 3381102 * 2
def baseEnd_3381102 : Nat := 578710155959378552191867

theorem tailTrace_3381102 : CollatzResearch.WordTrace tailWord_3381102 prefixEnd_3381102 578710155959378552191867 := by
  unfold tailWord_3381102
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414865124606546886733195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82212613997901583395910373 15414865124606546886733195)
  ·
    refine ⟨23122297686909820330099793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15414865124606546886733195 23122297686909820330099793)
    ·
      refine ⟨17341723265182365247574845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23122297686909820330099793 17341723265182365247574845)
      ·
        refine ⟨6503146224443386967840567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17341723265182365247574845 6503146224443386967840567)
        ·
          refine ⟨9754719336665080451760851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6503146224443386967840567 9754719336665080451760851)
          ·
            refine ⟨14632079004997620677641277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754719336665080451760851 14632079004997620677641277)
            ·
              refine ⟨5487029626874107754115479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14632079004997620677641277 5487029626874107754115479)
              ·
                refine ⟨8230544440311161631173219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487029626874107754115479 8230544440311161631173219)
                ·
                  refine ⟨12345816660466742446759829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230544440311161631173219 12345816660466742446759829)
                  ·
                    refine ⟨578710155959378552191867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12345816660466742446759829 578710155959378552191867)
                    ·
                      rfl

theorem cell23_3381102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3381102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381102 prefixEnd_3381102 := by exact prefixLift 3381102
  have htrace : WordTrace (prefixWord ++ tailWord_3381102) baseStart_3381102 baseEnd_3381102 := by
    simpa [prefixWord, tailWord_3381102, baseEnd_3381102] using wordTrace_append hprefix tailTrace_3381102
  have hstable : (prefixWord ++ tailWord_3381102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381102).length < 2 ^ (prefixWord ++ tailWord_3381102).sum := by decide
  have hdescent : baseEnd_3381102 < baseStart_3381102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381109 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_3381109 : Nat := 118140960795 + 3381109 * 2 ^ 59
def prefixEnd_3381109 : Nat := 4983230072969 + 3 ^ 40 * 3381109 * 2
def baseEnd_3381109 : Nat := 1736134062242717129188069

theorem tailTrace_3381109 : CollatzResearch.WordTrace tailWord_3381109 prefixEnd_3381109 1736134062242717129188069 := by
  unfold tailWord_3381109
  simp only [CollatzResearch.WordTrace]
  refine ⟨123319176307827015289370381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82212784205218010192913587 123319176307827015289370381)
  ·
    refine ⟨46244691115435130733513893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123319176307827015289370381 46244691115435130733513893)
    ·
      refine ⟨8670879584144087012533855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46244691115435130733513893 8670879584144087012533855)
      ·
        refine ⟨13006319376216130518800783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670879584144087012533855 13006319376216130518800783)
        ·
          refine ⟨19509479064324195778201175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13006319376216130518800783 19509479064324195778201175)
          ·
            refine ⟨29264218596486293667301763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19509479064324195778201175 29264218596486293667301763)
            ·
              refine ⟨43896327894729440500952645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29264218596486293667301763 43896327894729440500952645)
              ·
                refine ⟨8230561480261770093928621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43896327894729440500952645 8230561480261770093928621)
                ·
                  refine ⟨3086460555098163785223233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8230561480261770093928621 3086460555098163785223233)
                  ·
                    refine ⟨2314845416323622838917425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3086460555098163785223233 2314845416323622838917425)
                    ·
                      refine ⟨1736134062242717129188069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314845416323622838917425 1736134062242717129188069)
                      ·
                        rfl

theorem cell23_3381109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_3381109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381109 prefixEnd_3381109 := by exact prefixLift 3381109
  have htrace : WordTrace (prefixWord ++ tailWord_3381109) baseStart_3381109 baseEnd_3381109 := by
    simpa [prefixWord, tailWord_3381109, baseEnd_3381109] using wordTrace_append hprefix tailTrace_3381109
  have hstable : (prefixWord ++ tailWord_3381109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381109).length < 2 ^ (prefixWord ++ tailWord_3381109).sum := by decide
  have hdescent : baseEnd_3381109 < baseStart_3381109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381125 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 3]
def baseStart_3381125 : Nat := 118140960795 + 3381125 * 2 ^ 59
def prefixEnd_3381125 : Nat := 4983230072969 + 3 ^ 40 * 3381125 * 2
def baseEnd_3381125 : Nat := 1736142277933189066587995

theorem tailTrace_3381125 : CollatzResearch.WordTrace tailWord_3381125 prefixEnd_3381125 1736142277933189066587995 := by
  unfold tailWord_3381125
  simp only [CollatzResearch.WordTrace]
  refine ⟨123319759875769050021952829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82213173250512700014635219 123319759875769050021952829)
  ·
    refine ⟨46244909953413393758232311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123319759875769050021952829 46244909953413393758232311)
    ·
      refine ⟨69367364930120090637348467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46244909953413393758232311 69367364930120090637348467)
      ·
        refine ⟨104051047395180135956022701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69367364930120090637348467 104051047395180135956022701)
        ·
          refine ⟨39019142773192550983508513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104051047395180135956022701 39019142773192550983508513)
          ·
            refine ⟨29264357079894413237631385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39019142773192550983508513 29264357079894413237631385)
            ·
              refine ⟨21948267809920809928223539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29264357079894413237631385 21948267809920809928223539)
              ·
                refine ⟨32922401714881214892335309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21948267809920809928223539 32922401714881214892335309)
                ·
                  refine ⟨12345900643080455584625741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32922401714881214892335309 12345900643080455584625741)
                  ·
                    refine ⟨4629712741155170844234653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12345900643080455584625741 4629712741155170844234653)
                    ·
                      refine ⟨1736142277933189066587995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4629712741155170844234653 1736142277933189066587995)
                      ·
                        rfl

theorem cell23_3381125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_3381125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381125 prefixEnd_3381125 := by exact prefixLift 3381125
  have htrace : WordTrace (prefixWord ++ tailWord_3381125) baseStart_3381125 baseEnd_3381125 := by
    simpa [prefixWord, tailWord_3381125, baseEnd_3381125] using wordTrace_append hprefix tailTrace_3381125
  have hstable : (prefixWord ++ tailWord_3381125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381125).length < 2 ^ (prefixWord ++ tailWord_3381125).sum := by decide
  have hdescent : baseEnd_3381125 < baseStart_3381125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381135 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 9, 2]
def baseStart_3381135 : Nat := 118140960795 + 3381135 * 2 ^ 59
def prefixEnd_3381135 : Nat := 4983230072969 + 3 ^ 40 * 3381135 * 2
def baseEnd_3381135 : Nat := 1736147412739734027462949

theorem tailTrace_3381135 : CollatzResearch.WordTrace tailWord_3381135 prefixEnd_3381135 1736147412739734027462949 := by
  unfold tailWord_3381135
  simp only [CollatzResearch.WordTrace]
  refine ⟨123320124605732821729816859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82213416403821881153211239 123320124605732821729816859)
  ·
    refine ⟨184980186908599232594725289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123320124605732821729816859 184980186908599232594725289)
    ·
      refine ⟨138735140181449424446043967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184980186908599232594725289 138735140181449424446043967)
      ·
        refine ⟨208102710272174136669065951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138735140181449424446043967 208102710272174136669065951)
        ·
          refine ⟨312154065408261205003598927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208102710272174136669065951 312154065408261205003598927)
          ·
            refine ⟨468231098112391807505398391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312154065408261205003598927 468231098112391807505398391)
            ·
              refine ⟨702346647168587711258097587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468231098112391807505398391 702346647168587711258097587)
              ·
                refine ⟨1053519970752881566887146381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702346647168587711258097587 1053519970752881566887146381)
                ·
                  refine ⟨395069989032330587582679893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053519970752881566887146381 395069989032330587582679893)
                  ·
                    refine ⟨2314863216986312036617265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 395069989032330587582679893 2314863216986312036617265)
                    ·
                      refine ⟨1736147412739734027462949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314863216986312036617265 1736147412739734027462949)
                      ·
                        rfl

theorem cell23_3381135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9, 2].length) (baseStart_3381135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381135 prefixEnd_3381135 := by exact prefixLift 3381135
  have htrace : WordTrace (prefixWord ++ tailWord_3381135) baseStart_3381135 baseEnd_3381135 := by
    simpa [prefixWord, tailWord_3381135, baseEnd_3381135] using wordTrace_append hprefix tailTrace_3381135
  have hstable : (prefixWord ++ tailWord_3381135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381135).length < 2 ^ (prefixWord ++ tailWord_3381135).sum := by decide
  have hdescent : baseEnd_3381135 < baseStart_3381135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381143 : List Nat := [1, 1, 3, 3, 1, 4, 3, 2, 1, 2, 2]
def baseStart_3381143 : Nat := 118140960795 + 3381143 * 2 ^ 59
def prefixEnd_3381143 : Nat := 4983230072969 + 3 ^ 40 * 3381143 * 2
def baseEnd_3381143 : Nat := 1736151520584969996162913

theorem tailTrace_3381143 : CollatzResearch.WordTrace tailWord_3381143 prefixEnd_3381143 1736151520584969996162913 := by
  unfold tailWord_3381143
  simp only [CollatzResearch.WordTrace]
  refine ⟨123320416389703839096108083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82213610926469226064072055 123320416389703839096108083)
  ·
    refine ⟨184980624584555758644162125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123320416389703839096108083 184980624584555758644162125)
    ·
      refine ⟨69367734219208409491560797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184980624584555758644162125 69367734219208409491560797)
      ·
        refine ⟨26012900332203153559335299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69367734219208409491560797 26012900332203153559335299)
        ·
          refine ⟨39019350498304730339002949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26012900332203153559335299 39019350498304730339002949)
          ·
            refine ⟨7316128218432136938563053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39019350498304730339002949 7316128218432136938563053)
            ·
              refine ⟨2743548081912051351961145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7316128218432136938563053 2743548081912051351961145)
              ·
                refine ⟨2057661061434038513970859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743548081912051351961145 2057661061434038513970859)
                ·
                  refine ⟨3086491592151057770956289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057661061434038513970859 3086491592151057770956289)
                  ·
                    refine ⟨2314868694113293328217217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3086491592151057770956289 2314868694113293328217217)
                    ·
                      refine ⟨1736151520584969996162913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314868694113293328217217 1736151520584969996162913)
                      ·
                        rfl

theorem cell23_3381143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_3381143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381143 prefixEnd_3381143 := by exact prefixLift 3381143
  have htrace : WordTrace (prefixWord ++ tailWord_3381143) baseStart_3381143 baseEnd_3381143 := by
    simpa [prefixWord, tailWord_3381143, baseEnd_3381143] using wordTrace_append hprefix tailTrace_3381143
  have hstable : (prefixWord ++ tailWord_3381143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381143).length < 2 ^ (prefixWord ++ tailWord_3381143).sum := by decide
  have hdescent : baseEnd_3381143 < baseStart_3381143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381152 : List Nat := [2, 1, 1, 4, 1, 1, 1, 4, 3, 3, 2]
def baseStart_3381152 : Nat := 118140960795 + 3381152 * 2 ^ 59
def prefixEnd_3381152 : Nat := 4983230072969 + 3 ^ 40 * 3381152 * 2
def baseEnd_3381152 : Nat := 1736156141910860460950371

theorem tailTrace_3381152 : CollatzResearch.WordTrace tailWord_3381152 prefixEnd_3381152 1736156141910860460950371 := by
  unfold tailWord_3381152
  simp only [CollatzResearch.WordTrace]
  refine ⟨61660372323335616816592855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82213829764447489088790473 61660372323335616816592855)
  ·
    refine ⟨92490558485003425224889283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61660372323335616816592855 92490558485003425224889283)
    ·
      refine ⟨138735837727505137837333925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92490558485003425224889283 138735837727505137837333925)
      ·
        refine ⟨26012969573907213344500111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138735837727505137837333925 26012969573907213344500111)
        ·
          refine ⟨39019454360860820016750167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26012969573907213344500111 39019454360860820016750167)
          ·
            refine ⟨58529181541291230025125251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39019454360860820016750167 58529181541291230025125251)
            ·
              refine ⟨87793772311936845037687877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58529181541291230025125251 87793772311936845037687877)
              ·
                refine ⟨16461332308488158444566477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87793772311936845037687877 16461332308488158444566477)
                ·
                  refine ⟨6172999615683059416712429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16461332308488158444566477 6172999615683059416712429)
                  ·
                    refine ⟨2314874855881147281267161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6172999615683059416712429 2314874855881147281267161)
                    ·
                      refine ⟨1736156141910860460950371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314874855881147281267161 1736156141910860460950371)
                      ·
                        rfl

theorem cell23_3381152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_3381152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381152 prefixEnd_3381152 := by exact prefixLift 3381152
  have htrace : WordTrace (prefixWord ++ tailWord_3381152) baseStart_3381152 baseEnd_3381152 := by
    simpa [prefixWord, tailWord_3381152, baseEnd_3381152] using wordTrace_append hprefix tailTrace_3381152
  have hstable : (prefixWord ++ tailWord_3381152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381152).length < 2 ^ (prefixWord ++ tailWord_3381152).sum := by decide
  have hdescent : baseEnd_3381152 < baseStart_3381152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381153 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 2, 4]
def baseStart_3381153 : Nat := 118140960795 + 3381153 * 2 ^ 59
def prefixEnd_3381153 : Nat := 4983230072969 + 3 ^ 40 * 3381153 * 2
def baseEnd_3381153 : Nat := 578718885130504985679289

theorem tailTrace_3381153 : CollatzResearch.WordTrace tailWord_3381153 prefixEnd_3381153 578718885130504985679289 := by
  unfold tailWord_3381153
  simp only [CollatzResearch.WordTrace]
  refine ⟨123320781119667610803972113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82213854079778407202648075 123320781119667610803972113)
  ·
    refine ⟨92490585839750708102979085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123320781119667610803972113 92490585839750708102979085)
    ·
      refine ⟨34683969689906515538617157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92490585839750708102979085 34683969689906515538617157)
      ·
        refine ⟨6503244316857471663490717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34683969689906515538617157 6503244316857471663490717)
        ·
          refine ⟨2438716618821551873809019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6503244316857471663490717 2438716618821551873809019)
          ·
            refine ⟨3658074928232327810713529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438716618821551873809019 3658074928232327810713529)
            ·
              refine ⟨2743556196174245858035147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3658074928232327810713529 2743556196174245858035147)
              ·
                refine ⟨4115334294261368787052721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743556196174245858035147 4115334294261368787052721)
                ·
                  refine ⟨3086500720696026590289541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4115334294261368787052721 3086500720696026590289541)
                  ·
                    refine ⟨578718885130504985679289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3086500720696026590289541 578718885130504985679289)
                    ·
                      rfl

theorem cell23_3381153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_3381153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381153 prefixEnd_3381153 := by exact prefixLift 3381153
  have htrace : WordTrace (prefixWord ++ tailWord_3381153) baseStart_3381153 baseEnd_3381153 := by
    simpa [prefixWord, tailWord_3381153, baseEnd_3381153] using wordTrace_append hprefix tailTrace_3381153
  have hstable : (prefixWord ++ tailWord_3381153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381153).length < 2 ^ (prefixWord ++ tailWord_3381153).sum := by decide
  have hdescent : baseEnd_3381153 < baseStart_3381153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381168 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9]
def baseStart_3381168 : Nat := 118140960795 + 3381168 * 2 ^ 59
def prefixEnd_3381168 : Nat := 4983230072969 + 3 ^ 40 * 3381168 * 2
def baseEnd_3381168 : Nat := 1736164357601332398350297

theorem tailTrace_3381168 : CollatzResearch.WordTrace tailWord_3381168 prefixEnd_3381168 1736164357601332398350297 := by
  unfold tailWord_3381168
  simp only [CollatzResearch.WordTrace]
  refine ⟨61660664107306634182884079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82214218809742178910512105 61660664107306634182884079)
  ·
    refine ⟨92490996160959951274326119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61660664107306634182884079 92490996160959951274326119)
    ·
      refine ⟨138736494241439926911489179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92490996160959951274326119 138736494241439926911489179)
      ·
        refine ⟨208104741362159890367233769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138736494241439926911489179 208104741362159890367233769)
        ·
          refine ⟨156078556021619917775425327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208104741362159890367233769 156078556021619917775425327)
          ·
            refine ⟨234117834032429876663137991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156078556021619917775425327 234117834032429876663137991)
            ·
              refine ⟨351176751048644814994706987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234117834032429876663137991 351176751048644814994706987)
              ·
                refine ⟨526765126572967222492060481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351176751048644814994706987 526765126572967222492060481)
                ·
                  refine ⟨395073844929725416869045361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526765126572967222492060481 395073844929725416869045361)
                  ·
                    refine ⟨296305383697294062651784021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 395073844929725416869045361 296305383697294062651784021)
                    ·
                      refine ⟨1736164357601332398350297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 296305383697294062651784021 1736164357601332398350297)
                      ·
                        rfl

theorem cell23_3381168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 9].length) (baseStart_3381168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381168 prefixEnd_3381168 := by exact prefixLift 3381168
  have htrace : WordTrace (prefixWord ++ tailWord_3381168) baseStart_3381168 baseEnd_3381168 := by
    simpa [prefixWord, tailWord_3381168, baseEnd_3381168] using wordTrace_append hprefix tailTrace_3381168
  have hstable : (prefixWord ++ tailWord_3381168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381168).length < 2 ^ (prefixWord ++ tailWord_3381168).sum := by decide
  have hdescent : baseEnd_3381168 < baseStart_3381168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381169 : List Nat := [1, 2, 2, 4, 2, 2, 1, 1, 3, 3, 2]
def baseStart_3381169 : Nat := 118140960795 + 3381169 * 2 ^ 59
def prefixEnd_3381169 : Nat := 4983230072969 + 3 ^ 40 * 3381169 * 2
def baseEnd_3381169 : Nat := 1736164871081986894437793

theorem tailTrace_3381169 : CollatzResearch.WordTrace tailWord_3381169 prefixEnd_3381169 1736164871081986894437793 := by
  unfold tailWord_3381169
  simp only [CollatzResearch.WordTrace]
  refine ⟨123321364687609645536554561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82214243125073097024369707 123321364687609645536554561)
  ·
    refine ⟨92491023515707234152415921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123321364687609645536554561 92491023515707234152415921)
    ·
      refine ⟨69368267636780425614311941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92491023515707234152415921 69368267636780425614311941)
      ·
        refine ⟨13006550181896329802683489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69368267636780425614311941 13006550181896329802683489)
        ·
          refine ⟨9754912636422247352012617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13006550181896329802683489 9754912636422247352012617)
          ·
            refine ⟨7316184477316685514009463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9754912636422247352012617 7316184477316685514009463)
            ·
              refine ⟨10974276715975028271014195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7316184477316685514009463 10974276715975028271014195)
              ·
                refine ⟨16461415073962542406521293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10974276715975028271014195 16461415073962542406521293)
                ·
                  refine ⟨6173030652735953402445485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16461415073962542406521293 6173030652735953402445485)
                  ·
                    refine ⟨2314886494775982525917057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6173030652735953402445485 2314886494775982525917057)
                    ·
                      refine ⟨1736164871081986894437793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2314886494775982525917057 1736164871081986894437793)
                      ·
                        rfl

theorem cell23_3381169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_3381169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381169 prefixEnd_3381169 := by exact prefixLift 3381169
  have htrace : WordTrace (prefixWord ++ tailWord_3381169) baseStart_3381169 baseEnd_3381169 := by
    simpa [prefixWord, tailWord_3381169, baseEnd_3381169] using wordTrace_append hprefix tailTrace_3381169
  have hstable : (prefixWord ++ tailWord_3381169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381169).length < 2 ^ (prefixWord ++ tailWord_3381169).sum := by decide
  have hdescent : baseEnd_3381169 < baseStart_3381169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381195 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4]
def baseStart_3381195 : Nat := 118140960795 + 3381195 * 2 ^ 59
def prefixEnd_3381195 : Nat := 4983230072969 + 3 ^ 40 * 3381195 * 2
def baseEnd_3381195 : Nat := 1736178221579003792712673

theorem tailTrace_3381195 : CollatzResearch.WordTrace tailWord_3381195 prefixEnd_3381195 1736178221579003792712673 := by
  unfold tailWord_3381195
  simp only [CollatzResearch.WordTrace]
  refine ⟨123322312985515451977001039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82214875323676967984667359 123322312985515451977001039)
  ·
    refine ⟨184983469478273177965501559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123322312985515451977001039 184983469478273177965501559)
    ·
      refine ⟨277475204217409766948252339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184983469478273177965501559 277475204217409766948252339)
      ·
        refine ⟨416212806326114650422378509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277475204217409766948252339 416212806326114650422378509)
        ·
          refine ⟨156079802372292993908391941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 416212806326114650422378509 156079802372292993908391941)
          ·
            refine ⟨29264962944804936357823489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156079802372292993908391941 29264962944804936357823489)
            ·
              refine ⟨21948722208603702268367617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29264962944804936357823489 21948722208603702268367617)
              ·
                refine ⟨16461541656452776701275713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21948722208603702268367617 16461541656452776701275713)
                ·
                  refine ⟨12346156242339582525956785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16461541656452776701275713 12346156242339582525956785)
                  ·
                    refine ⟨9259617181754686894467589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12346156242339582525956785 9259617181754686894467589)
                    ·
                      refine ⟨1736178221579003792712673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9259617181754686894467589 1736178221579003792712673)
                      ·
                        rfl

theorem cell23_3381195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_3381195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381195 prefixEnd_3381195 := by exact prefixLift 3381195
  have htrace : WordTrace (prefixWord ++ tailWord_3381195) baseStart_3381195 baseEnd_3381195 := by
    simpa [prefixWord, tailWord_3381195, baseEnd_3381195] using wordTrace_append hprefix tailTrace_3381195
  have hstable : (prefixWord ++ tailWord_3381195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381195).length < 2 ^ (prefixWord ++ tailWord_3381195).sum := by decide
  have hdescent : baseEnd_3381195 < baseStart_3381195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381245 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3381245 : Nat := 118140960795 + 3381245 * 2 ^ 59
def prefixEnd_3381245 : Nat := 4983230072969 + 3 ^ 40 * 3381245 * 2
def baseEnd_3381245 : Nat := 1736203895611728597087443

theorem tailTrace_3381245 : CollatzResearch.WordTrace tailWord_3381245 prefixEnd_3381245 1736203895611728597087443 := by
  unfold tailWord_3381245
  simp only [CollatzResearch.WordTrace]
  refine ⟨123324136635334310516321189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82216091090222873677547459 123324136635334310516321189)
  ·
    refine ⟨23123275619125183221810223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123324136635334310516321189 23123275619125183221810223)
    ·
      refine ⟨34684913428687774832715335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23123275619125183221810223 34684913428687774832715335)
      ·
        refine ⟨52027370143031662249073003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34684913428687774832715335 52027370143031662249073003)
        ·
          refine ⟨78041055214547493373609505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52027370143031662249073003 78041055214547493373609505)
          ·
            refine ⟨58530791410910620030207129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78041055214547493373609505 58530791410910620030207129)
            ·
              refine ⟨43898093558182965022655347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58530791410910620030207129 43898093558182965022655347)
              ·
                refine ⟨65847140337274447533983021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43898093558182965022655347 65847140337274447533983021)
                ·
                  refine ⟨24692677626477917825243633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65847140337274447533983021 24692677626477917825243633)
                  ·
                    refine ⟨18519508219858438368932725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24692677626477917825243633 18519508219858438368932725)
                    ·
                      refine ⟨1736203895611728597087443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18519508219858438368932725 1736203895611728597087443)
                      ·
                        rfl

theorem cell23_3381245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3381245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381245 prefixEnd_3381245 := by exact prefixLift 3381245
  have htrace : WordTrace (prefixWord ++ tailWord_3381245) baseStart_3381245 baseEnd_3381245 := by
    simpa [prefixWord, tailWord_3381245, baseEnd_3381245] using wordTrace_append hprefix tailTrace_3381245
  have hstable : (prefixWord ++ tailWord_3381245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381245).length < 2 ^ (prefixWord ++ tailWord_3381245).sum := by decide
  have hdescent : baseEnd_3381245 < baseStart_3381245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381309 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_3381309 : Nat := 118140960795 + 3381309 * 2 ^ 59
def prefixEnd_3381309 : Nat := 4983230072969 + 3 ^ 40 * 3381309 * 2
def baseEnd_3381309 : Nat := 1736236758373616346687149

theorem tailTrace_3381309 : CollatzResearch.WordTrace tailWord_3381309 prefixEnd_3381309 1736236758373616346687149 := by
  unfold tailWord_3381309
  simp only [CollatzResearch.WordTrace]
  refine ⟨123326470907102449446650981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82217647271401632964433987 123326470907102449446650981)
  ·
    refine ⟨23123713295081709271247059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123326470907102449446650981 23123713295081709271247059)
    ·
      refine ⟨34685569942622563906870589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23123713295081709271247059 34685569942622563906870589)
      ·
        refine ⟨13007088728483461465076471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34685569942622563906870589 13007088728483461465076471)
        ·
          refine ⟨19510633092725192197614707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13007088728483461465076471 19510633092725192197614707)
          ·
            refine ⟨29265949639087788296422061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19510633092725192197614707 29265949639087788296422061)
            ·
              refine ⟨10974731114657920611158273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29265949639087788296422061 10974731114657920611158273)
              ·
                refine ⟨8231048335993440458368705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10974731114657920611158273 8231048335993440458368705)
                ·
                  refine ⟨6173286251995080343776529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231048335993440458368705 6173286251995080343776529)
                  ·
                    refine ⟨4629964688996310257832397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6173286251995080343776529 4629964688996310257832397)
                    ·
                      refine ⟨1736236758373616346687149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4629964688996310257832397 1736236758373616346687149)
                      ·
                        rfl

theorem cell23_3381309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_3381309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381309 prefixEnd_3381309 := by exact prefixLift 3381309
  have htrace : WordTrace (prefixWord ++ tailWord_3381309) baseStart_3381309 baseEnd_3381309 := by
    simpa [prefixWord, tailWord_3381309, baseEnd_3381309] using wordTrace_append hprefix tailTrace_3381309
  have hstable : (prefixWord ++ tailWord_3381309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381309).length < 2 ^ (prefixWord ++ tailWord_3381309).sum := by decide
  have hdescent : baseEnd_3381309 < baseStart_3381309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381315 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_3381315 : Nat := 118140960795 + 3381315 * 2 ^ 59
def prefixEnd_3381315 : Nat := 4983230072969 + 3 ^ 40 * 3381315 * 2
def baseEnd_3381315 : Nat := 1736239839257543323212121

theorem tailTrace_3381315 : CollatzResearch.WordTrace tailWord_3381315 prefixEnd_3381315 1736239839257543323212121 := by
  unfold tailWord_3381315
  simp only [CollatzResearch.WordTrace]
  refine ⟨123326689745080712471369399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82217793163387141647579599 123326689745080712471369399)
  ·
    refine ⟨184990034617621068707054099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123326689745080712471369399 184990034617621068707054099)
    ·
      refine ⟨277485051926431603060581149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184990034617621068707054099 277485051926431603060581149)
      ·
        refine ⟨104056894472411851147717931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 277485051926431603060581149 104056894472411851147717931)
        ·
          refine ⟨156085341708617776721576897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104056894472411851147717931 156085341708617776721576897)
          ·
            refine ⟨117064006281463332541182673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156085341708617776721576897 117064006281463332541182673)
            ·
              refine ⟨87798004711097499405887005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117064006281463332541182673 87798004711097499405887005)
              ·
                refine ⟨32924251766661562277207627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87798004711097499405887005 32924251766661562277207627)
                ·
                  refine ⟨49386377649992343415811441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32924251766661562277207627 49386377649992343415811441)
                  ·
                    refine ⟨37039783237494257561858581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49386377649992343415811441 37039783237494257561858581)
                    ·
                      refine ⟨1736239839257543323212121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37039783237494257561858581 1736239839257543323212121)
                      ·
                        rfl

theorem cell23_3381315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_3381315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381315 prefixEnd_3381315 := by exact prefixLift 3381315
  have htrace : WordTrace (prefixWord ++ tailWord_3381315) baseStart_3381315 baseEnd_3381315 := by
    simpa [prefixWord, tailWord_3381315, baseEnd_3381315] using wordTrace_append hprefix tailTrace_3381315
  have hstable : (prefixWord ++ tailWord_3381315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381315).length < 2 ^ (prefixWord ++ tailWord_3381315).sum := by decide
  have hdescent : baseEnd_3381315 < baseStart_3381315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381373 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 1, 1, 3]
def baseStart_3381373 : Nat := 118140960795 + 3381373 * 2 ^ 59
def prefixEnd_3381373 : Nat := 4983230072969 + 3 ^ 40 * 3381373 * 2
def baseEnd_3381373 : Nat := 1736269621135504096286855

theorem tailTrace_3381373 : CollatzResearch.WordTrace tailWord_3381373 prefixEnd_3381373 1736269621135504096286855 := by
  unfold tailWord_3381373
  simp only [CollatzResearch.WordTrace]
  refine ⟨123328805178870588376980773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82219203452580392251320515 123328805178870588376980773)
  ·
    refine ⟨23124150971038235320683895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123328805178870588376980773 23124150971038235320683895)
    ·
      refine ⟨34686226456557352981025843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23124150971038235320683895 34686226456557352981025843)
      ·
        refine ⟨52029339684836029471538765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34686226456557352981025843 52029339684836029471538765)
        ·
          refine ⟨19511002381813511051827037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52029339684836029471538765 19511002381813511051827037)
          ·
            refine ⟨7316625893180066644435139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19511002381813511051827037 7316625893180066644435139)
            ·
              refine ⟨10974938839770099966652709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7316625893180066644435139 10974938839770099966652709)
              ·
                refine ⟨2057801032456893743747383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10974938839770099966652709 2057801032456893743747383)
                ·
                  refine ⟨3086701548685340615621075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057801032456893743747383 3086701548685340615621075)
                  ·
                    refine ⟨4630052323028010923431613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3086701548685340615621075 4630052323028010923431613)
                    ·
                      refine ⟨1736269621135504096286855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4630052323028010923431613 1736269621135504096286855)
                      ·
                        rfl

theorem cell23_3381373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_3381373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381373 prefixEnd_3381373 := by exact prefixLift 3381373
  have htrace : WordTrace (prefixWord ++ tailWord_3381373) baseStart_3381373 baseEnd_3381373 := by
    simpa [prefixWord, tailWord_3381373, baseEnd_3381373] using wordTrace_append hprefix tailTrace_3381373
  have hstable : (prefixWord ++ tailWord_3381373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381373).length < 2 ^ (prefixWord ++ tailWord_3381373).sum := by decide
  have hdescent : baseEnd_3381373 < baseStart_3381373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381400 : List Nat := [2, 1, 2, 4, 4, 1, 1, 1, 2, 3, 2]
def baseStart_3381400 : Nat := 118140960795 + 3381400 * 2 ^ 59
def prefixEnd_3381400 : Nat := 4983230072969 + 3 ^ 40 * 3381400 * 2
def baseEnd_3381400 : Nat := 1736283485113175490649231

theorem tailTrace_3381400 : CollatzResearch.WordTrace tailWord_3381400 prefixEnd_3381400 1736283485113175490649231 := by
  unfold tailWord_3381400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61664894974886385994106827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82219859966515181325475769 61664894974886385994106827)
  ·
    refine ⟨92497342462329578991160241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61664894974886385994106827 92497342462329578991160241)
    ·
      refine ⟨69373006846747184243370181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92497342462329578991160241 69373006846747184243370181)
      ·
        refine ⟨13007438783765097045631909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69373006846747184243370181 13007438783765097045631909)
        ·
          refine ⟨2438894771955955696055983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13007438783765097045631909 2438894771955955696055983)
          ·
            refine ⟨3658342157933933544083975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438894771955955696055983 3658342157933933544083975)
            ·
              refine ⟨5487513236900900316125963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658342157933933544083975 5487513236900900316125963)
              ·
                refine ⟨8231269855351350474188945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487513236900900316125963 8231269855351350474188945)
                ·
                  refine ⟨6173452391513512855641709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231269855351350474188945 6173452391513512855641709)
                  ·
                    refine ⟨2315044646817567320865641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6173452391513512855641709 2315044646817567320865641)
                    ·
                      refine ⟨1736283485113175490649231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2315044646817567320865641 1736283485113175490649231)
                      ·
                        rfl

theorem cell23_3381400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_3381400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381400 prefixEnd_3381400 := by exact prefixLift 3381400
  have htrace : WordTrace (prefixWord ++ tailWord_3381400) baseStart_3381400 baseEnd_3381400 := by
    simpa [prefixWord, tailWord_3381400, baseEnd_3381400] using wordTrace_append hprefix tailTrace_3381400
  have hstable : (prefixWord ++ tailWord_3381400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381400).length < 2 ^ (prefixWord ++ tailWord_3381400).sum := by decide
  have hdescent : baseEnd_3381400 < baseStart_3381400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381409 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3381409 : Nat := 118140960795 + 3381409 * 2 ^ 59
def prefixEnd_3381409 : Nat := 4983230072969 + 3 ^ 40 * 3381409 * 2
def baseEnd_3381409 : Nat := 1736288106439065955436689

theorem tailTrace_3381409 : CollatzResearch.WordTrace tailWord_3381409 prefixEnd_3381409 1736288106439065955436689 := by
  unfold tailWord_3381409
  simp only [CollatzResearch.WordTrace]
  refine ⟨123330118206740166525291281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82220078804493444350194187 123330118206740166525291281)
  ·
    refine ⟨92497588655055124893968461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123330118206740166525291281 92497588655055124893968461)
    ·
      refine ⟨34686595745645671835238173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92497588655055124893968461 34686595745645671835238173)
      ·
        refine ⟨13007473404617126938214315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34686595745645671835238173 13007473404617126938214315)
        ·
          refine ⟨19511210106925690407321473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13007473404617126938214315 19511210106925690407321473)
          ·
            refine ⟨14633407580194267805491105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19511210106925690407321473 14633407580194267805491105)
            ·
              refine ⟨10975055685145700854118329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14633407580194267805491105 10975055685145700854118329)
              ·
                refine ⟨8231291763859275640588747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10975055685145700854118329 8231291763859275640588747)
                ·
                  refine ⟨12346937645788913460883121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8231291763859275640588747 12346937645788913460883121)
                  ·
                    refine ⟨9260203234341685095662341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12346937645788913460883121 9260203234341685095662341)
                    ·
                      refine ⟨1736288106439065955436689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9260203234341685095662341 1736288106439065955436689)
                      ·
                        rfl

theorem cell23_3381409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3381409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381409 prefixEnd_3381409 := by exact prefixLift 3381409
  have htrace : WordTrace (prefixWord ++ tailWord_3381409) baseStart_3381409 baseEnd_3381409 := by
    simpa [prefixWord, tailWord_3381409, baseEnd_3381409] using wordTrace_append hprefix tailTrace_3381409
  have hstable : (prefixWord ++ tailWord_3381409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381409).length < 2 ^ (prefixWord ++ tailWord_3381409).sum := by decide
  have hdescent : baseEnd_3381409 < baseStart_3381409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381503 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 2, 2, 2]
def baseStart_3381503 : Nat := 118140960795 + 3381503 * 2 ^ 59
def prefixEnd_3381503 : Nat := 4983230072969 + 3 ^ 40 * 3381503 * 2
def baseEnd_3381503 : Nat := 1736336373620588587661257

theorem tailTrace_3381503 : CollatzResearch.WordTrace tailWord_3381503 prefixEnd_3381503 1736336373620588587661257 := by
  unfold tailWord_3381503
  simp only [CollatzResearch.WordTrace]
  refine ⟨123333546668399620579213163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82222364445599747052808775 123333546668399620579213163)
  ·
    refine ⟨185000320002599430868819745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123333546668399620579213163 185000320002599430868819745)
    ·
      refine ⟨138750240001949573151614809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185000320002599430868819745 138750240001949573151614809)
      ·
        refine ⟨104062680001462179863711107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138750240001949573151614809 104062680001462179863711107)
        ·
          refine ⟨156094020002193269795566661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104062680001462179863711107 156094020002193269795566661)
          ·
            refine ⟨29267628750411238086668749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156094020002193269795566661 29267628750411238086668749)
            ·
              refine ⟨10975360781404214282500781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29267628750411238086668749 10975360781404214282500781)
              ·
                refine ⟨4115760293026580355937793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10975360781404214282500781 4115760293026580355937793)
                ·
                  refine ⟨3086820219769935266953345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4115760293026580355937793 3086820219769935266953345)
                  ·
                    refine ⟨2315115164827451450215009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3086820219769935266953345 2315115164827451450215009)
                    ·
                      refine ⟨1736336373620588587661257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2315115164827451450215009 1736336373620588587661257)
                      ·
                        rfl

theorem cell23_3381503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 2, 2, 2].length) (baseStart_3381503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381503 prefixEnd_3381503 := by exact prefixLift 3381503
  have htrace : WordTrace (prefixWord ++ tailWord_3381503) baseStart_3381503 baseEnd_3381503 := by
    simpa [prefixWord, tailWord_3381503, baseEnd_3381503] using wordTrace_append hprefix tailTrace_3381503
  have hstable : (prefixWord ++ tailWord_3381503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381503).length < 2 ^ (prefixWord ++ tailWord_3381503).sum := by decide
  have hdescent : baseEnd_3381503 < baseStart_3381503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381506 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_3381506 : Nat := 118140960795 + 3381506 * 2 ^ 59
def prefixEnd_3381506 : Nat := 4983230072969 + 3 ^ 40 * 3381506 * 2
def baseEnd_3381506 : Nat := 1736337914062552075923743

theorem tailTrace_3381506 : CollatzResearch.WordTrace tailWord_3381506 prefixEnd_3381506 1736337914062552075923743 := by
  unfold tailWord_3381506
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833414021847188022893093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82222437391592501394381581 30833414021847188022893093)
  ·
    refine ⟨5781265129096347754292455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30833414021847188022893093 5781265129096347754292455)
    ·
      refine ⟨8671897693644521631438683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5781265129096347754292455 8671897693644521631438683)
      ·
        refine ⟨13007846540466782447158025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8671897693644521631438683 13007846540466782447158025)
        ·
          refine ⟨9755884905350086835368519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13007846540466782447158025 9755884905350086835368519)
          ·
            refine ⟨14633827358025130253052779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9755884905350086835368519 14633827358025130253052779)
            ·
              refine ⟨21950741037037695379579169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14633827358025130253052779 21950741037037695379579169)
              ·
                refine ⟨16463055777778271534684377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21950741037037695379579169 16463055777778271534684377)
                ·
                  refine ⟨12347291833333703651013283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16463055777778271534684377 12347291833333703651013283)
                  ·
                    refine ⟨18520937750000555476519925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12347291833333703651013283 18520937750000555476519925)
                    ·
                      refine ⟨1736337914062552075923743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18520937750000555476519925 1736337914062552075923743)
                      ·
                        rfl

theorem cell23_3381506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_3381506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381506 prefixEnd_3381506 := by exact prefixLift 3381506
  have htrace : WordTrace (prefixWord ++ tailWord_3381506) baseStart_3381506 baseEnd_3381506 := by
    simpa [prefixWord, tailWord_3381506, baseEnd_3381506] using wordTrace_append hprefix tailTrace_3381506
  have hstable : (prefixWord ++ tailWord_3381506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381506).length < 2 ^ (prefixWord ++ tailWord_3381506).sum := by decide
  have hdescent : baseEnd_3381506 < baseStart_3381506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381539 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 2, 5]
def baseStart_3381539 : Nat := 118140960795 + 3381539 * 2 ^ 59
def prefixEnd_3381539 : Nat := 4983230072969 + 3 ^ 40 * 3381539 * 2
def baseEnd_3381539 : Nat := 578784952974716815603697

theorem tailTrace_3381539 : CollatzResearch.WordTrace tailWord_3381539 prefixEnd_3381539 578784952974716815603697 := by
  unfold tailWord_3381539
  simp only [CollatzResearch.WordTrace]
  refine ⟨123334859696269198727523671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82223239797512799151682447 123334859696269198727523671)
  ·
    refine ⟨185002289544403798091285507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123334859696269198727523671 185002289544403798091285507)
    ·
      refine ⟨277503434316605697136928261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185002289544403798091285507 277503434316605697136928261)
      ·
        refine ⟨52031893934363568213174049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 277503434316605697136928261 52031893934363568213174049)
        ·
          refine ⟨39023920450772676159880537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52031893934363568213174049 39023920450772676159880537)
          ·
            refine ⟨29267940338079507119910403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39023920450772676159880537 29267940338079507119910403)
            ·
              refine ⟨43901910507119260679865605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29267940338079507119910403 43901910507119260679865605)
              ·
                refine ⟨8231608220084861377474801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43901910507119260679865605 8231608220084861377474801)
                ·
                  refine ⟨6173706165063646033106101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231608220084861377474801 6173706165063646033106101)
                  ·
                    refine ⟨578784952974716815603697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6173706165063646033106101 578784952974716815603697)
                    ·
                      rfl

theorem cell23_3381539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 5].length) (baseStart_3381539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381539 prefixEnd_3381539 := by exact prefixLift 3381539
  have htrace : WordTrace (prefixWord ++ tailWord_3381539) baseStart_3381539 baseEnd_3381539 := by
    simpa [prefixWord, tailWord_3381539, baseEnd_3381539] using wordTrace_append hprefix tailTrace_3381539
  have hstable : (prefixWord ++ tailWord_3381539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381539).length < 2 ^ (prefixWord ++ tailWord_3381539).sum := by decide
  have hdescent : baseEnd_3381539 < baseStart_3381539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381559 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 4]
def baseStart_3381559 : Nat := 118140960795 + 3381559 * 2 ^ 59
def prefixEnd_3381559 : Nat := 4983230072969 + 3 ^ 40 * 3381559 * 2
def baseEnd_3381559 : Nat := 1736365128537240368560999

theorem tailTrace_3381559 : CollatzResearch.WordTrace tailWord_3381559 prefixEnd_3381559 1736365128537240368560999 := by
  unfold tailWord_3381559
  simp only [CollatzResearch.WordTrace]
  refine ⟨123335589156196742143251731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82223726104131161428834487 123335589156196742143251731)
  ·
    refine ⟨185003383734295113214877597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123335589156196742143251731 185003383734295113214877597)
    ·
      refine ⟨69376268900360667455579099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185003383734295113214877597 69376268900360667455579099)
      ·
        refine ⟨104064403350541001183368649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69376268900360667455579099 104064403350541001183368649)
        ·
          refine ⟨78048302512905750887526487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104064403350541001183368649 78048302512905750887526487)
          ·
            refine ⟨117072453769358626331289731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78048302512905750887526487 117072453769358626331289731)
            ·
              refine ⟨175608680654037939496934597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117072453769358626331289731 175608680654037939496934597)
              ·
                refine ⟨32926627622632113655675237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175608680654037939496934597 32926627622632113655675237)
                ·
                  refine ⟨6173742679243521310439107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32926627622632113655675237 6173742679243521310439107)
                  ·
                    refine ⟨9260614018865281965658661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173742679243521310439107 9260614018865281965658661)
                    ·
                      refine ⟨1736365128537240368560999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9260614018865281965658661 1736365128537240368560999)
                      ·
                        rfl

theorem cell23_3381559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 4, 1, 4].length) (baseStart_3381559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381559 prefixEnd_3381559 := by exact prefixLift 3381559
  have htrace : WordTrace (prefixWord ++ tailWord_3381559) baseStart_3381559 baseEnd_3381559 := by
    simpa [prefixWord, tailWord_3381559, baseEnd_3381559] using wordTrace_append hprefix tailTrace_3381559
  have hstable : (prefixWord ++ tailWord_3381559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381559).length < 2 ^ (prefixWord ++ tailWord_3381559).sum := by decide
  have hdescent : baseEnd_3381559 < baseStart_3381559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381576 : List Nat := [2, 1, 3, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_3381576 : Nat := 118140960795 + 3381576 * 2 ^ 59
def prefixEnd_3381576 : Nat := 4983230072969 + 3 ^ 40 * 3381576 * 2
def baseEnd_3381576 : Nat := 1736373857708366802048421

theorem tailTrace_3381576 : CollatzResearch.WordTrace tailWord_3381576 prefixEnd_3381576 1736373857708366802048421 := by
  unfold tailWord_3381576
  simp only [CollatzResearch.WordTrace]
  refine ⟨61668104598567577023310291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82224139464756769364413721 61668104598567577023310291)
  ·
    refine ⟨92502156897851365534965437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61668104598567577023310291 92502156897851365534965437)
    ·
      refine ⟨34688308836694262075612039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92502156897851365534965437 34688308836694262075612039)
      ·
        refine ⟨52032463255041393113418059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34688308836694262075612039 52032463255041393113418059)
        ·
          refine ⟨78048694882562089670127089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52032463255041393113418059 78048694882562089670127089)
          ·
            refine ⟨58536521161921567252595317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78048694882562089670127089 58536521161921567252595317)
            ·
              refine ⟨5487798858930146929930811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58536521161921567252595317 5487798858930146929930811)
              ·
                refine ⟨8231698288395220394896217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487798858930146929930811 8231698288395220394896217)
                ·
                  refine ⟨6173773716296415296172163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8231698288395220394896217 6173773716296415296172163)
                  ·
                    refine ⟨9260660574444622944258245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6173773716296415296172163 9260660574444622944258245)
                    ·
                      refine ⟨1736373857708366802048421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9260660574444622944258245 1736373857708366802048421)
                      ·
                        rfl

theorem cell23_3381576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_3381576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381576 prefixEnd_3381576 := by exact prefixLift 3381576
  have htrace : WordTrace (prefixWord ++ tailWord_3381576) baseStart_3381576 baseEnd_3381576 := by
    simpa [prefixWord, tailWord_3381576, baseEnd_3381576] using wordTrace_append hprefix tailTrace_3381576
  have hstable : (prefixWord ++ tailWord_3381576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381576).length < 2 ^ (prefixWord ++ tailWord_3381576).sum := by decide
  have hdescent : baseEnd_3381576 < baseStart_3381576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381603 : List Nat := [1, 1, 1, 5, 2, 1, 1, 6, 1, 4]
def baseStart_3381603 : Nat := 118140960795 + 3381603 * 2 ^ 59
def prefixEnd_3381603 : Nat := 4983230072969 + 3 ^ 40 * 3381603 * 2
def baseEnd_3381603 : Nat := 578795907228679398803599

theorem tailTrace_3381603 : CollatzResearch.WordTrace tailWord_3381603 prefixEnd_3381603 578795907228679398803599 := by
  unfold tailWord_3381603
  simp only [CollatzResearch.WordTrace]
  refine ⟨123337193968037337657853463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82224795978691558438568975 123337193968037337657853463)
  ·
    refine ⟨185005790952056006486780195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123337193968037337657853463 185005790952056006486780195)
    ·
      refine ⟨277508686428084009730170293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185005790952056006486780195 277508686428084009730170293)
      ·
        refine ⟨26016439352632875912203465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 277508686428084009730170293 26016439352632875912203465)
        ·
          refine ⟨19512329514474656934152599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26016439352632875912203465 19512329514474656934152599)
          ·
            refine ⟨29268494271711985401228899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19512329514474656934152599 29268494271711985401228899)
            ·
              refine ⟨43902741407567978101843349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29268494271711985401228899 43902741407567978101843349)
              ·
                refine ⟨2057941003479748973523907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43902741407567978101843349 2057941003479748973523907)
                ·
                  refine ⟨3086911505219623460285861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057941003479748973523907 3086911505219623460285861)
                  ·
                    refine ⟨578795907228679398803599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3086911505219623460285861 578795907228679398803599)
                    ·
                      rfl

theorem cell23_3381603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 1, 4].length) (baseStart_3381603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381603 prefixEnd_3381603 := by exact prefixLift 3381603
  have htrace : WordTrace (prefixWord ++ tailWord_3381603) baseStart_3381603 baseEnd_3381603 := by
    simpa [prefixWord, tailWord_3381603, baseEnd_3381603] using wordTrace_append hprefix tailTrace_3381603
  have hstable : (prefixWord ++ tailWord_3381603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381603).length < 2 ^ (prefixWord ++ tailWord_3381603).sum := by decide
  have hdescent : baseEnd_3381603 < baseStart_3381603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381703 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 5]
def baseStart_3381703 : Nat := 118140960795 + 3381703 * 2 ^ 59
def prefixEnd_3381703 : Nat := 4983230072969 + 3 ^ 40 * 3381703 * 2
def baseEnd_3381703 : Nat := 1736439069751487805160337

theorem tailTrace_3381703 : CollatzResearch.WordTrace tailWord_3381703 prefixEnd_3381703 1736439069751487805160337 := by
  unfold tailWord_3381703
  simp only [CollatzResearch.WordTrace]
  refine ⟨123340841267675054736493763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82227227511783369824329175 123340841267675054736493763)
  ·
    refine ⟨185011261901512582104740645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123340841267675054736493763 185011261901512582104740645)
    ·
      refine ⟨34689611606533609144638871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185011261901512582104740645 34689611606533609144638871)
      ·
        refine ⟨52034417409800413716958307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34689611606533609144638871 52034417409800413716958307)
        ·
          refine ⟨78051626114700620575437461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52034417409800413716958307 78051626114700620575437461)
          ·
            refine ⟨3658669974126591589473631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78051626114700620575437461 3658669974126591589473631)
            ·
              refine ⟨5488004961189887384210447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658669974126591589473631 5488004961189887384210447)
              ·
                refine ⟨8232007441784831076315671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488004961189887384210447 8232007441784831076315671)
                ·
                  refine ⟨12348011162677246614473507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8232007441784831076315671 12348011162677246614473507)
                  ·
                    refine ⟨18522016744015869921710261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12348011162677246614473507 18522016744015869921710261)
                    ·
                      refine ⟨1736439069751487805160337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18522016744015869921710261 1736439069751487805160337)
                      ·
                        rfl

theorem cell23_3381703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_3381703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381703 prefixEnd_3381703 := by exact prefixLift 3381703
  have htrace : WordTrace (prefixWord ++ tailWord_3381703) baseStart_3381703 baseEnd_3381703 := by
    simpa [prefixWord, tailWord_3381703, baseEnd_3381703] using wordTrace_append hprefix tailTrace_3381703
  have hstable : (prefixWord ++ tailWord_3381703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381703).length < 2 ^ (prefixWord ++ tailWord_3381703).sum := by decide
  have hdescent : baseEnd_3381703 < baseStart_3381703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381750 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3]
def baseStart_3381750 : Nat := 118140960795 + 3381750 * 2 ^ 59
def prefixEnd_3381750 : Nat := 4983230072969 + 3 ^ 40 * 3381750 * 2
def baseEnd_3381750 : Nat := 1736463203342249121272621

theorem tailTrace_3381750 : CollatzResearch.WordTrace tailWord_3381750 prefixEnd_3381750 1736463203342249121272621 := by
  unfold tailWord_3381750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7708909718656548860215919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82228370332336521175636469 7708909718656548860215919)
  ·
    refine ⟨11563364577984823290323879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7708909718656548860215919 11563364577984823290323879)
    ·
      refine ⟨17345046866977234935485819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11563364577984823290323879 17345046866977234935485819)
      ·
        refine ⟨26017570300465852403228729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17345046866977234935485819 26017570300465852403228729)
        ·
          refine ⟨19513177725349389302421547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26017570300465852403228729 19513177725349389302421547)
          ·
            refine ⟨29269766588024083953632321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19513177725349389302421547 29269766588024083953632321)
            ·
              refine ⟨21952324941018062965224241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29269766588024083953632321 21952324941018062965224241)
              ·
                refine ⟨16464243705763547223918181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21952324941018062965224241 16464243705763547223918181)
                ·
                  refine ⟨3087045694830665104484659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16464243705763547223918181 3087045694830665104484659)
                  ·
                    refine ⟨4630568542245997656726989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3087045694830665104484659 4630568542245997656726989)
                    ·
                      refine ⟨1736463203342249121272621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4630568542245997656726989 1736463203342249121272621)
                      ·
                        rfl

theorem cell23_3381750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_3381750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381750 prefixEnd_3381750 := by exact prefixLift 3381750
  have htrace : WordTrace (prefixWord ++ tailWord_3381750) baseStart_3381750 baseEnd_3381750 := by
    simpa [prefixWord, tailWord_3381750, baseEnd_3381750] using wordTrace_append hprefix tailTrace_3381750
  have hstable : (prefixWord ++ tailWord_3381750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381750).length < 2 ^ (prefixWord ++ tailWord_3381750).sum := by decide
  have hdescent : baseEnd_3381750 < baseStart_3381750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381776 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3]
def baseStart_3381776 : Nat := 118140960795 + 3381776 * 2 ^ 59
def prefixEnd_3381776 : Nat := 4983230072969 + 3 ^ 40 * 3381776 * 2
def baseEnd_3381776 : Nat := 1736476553839266019547501

theorem tailTrace_3381776 : CollatzResearch.WordTrace tailWord_3381776 prefixEnd_3381776 1736476553839266019547501 := by
  unfold tailWord_3381776
  simp only [CollatzResearch.WordTrace]
  refine ⟨61671751898205294101950591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82229002530940392135934121 61671751898205294101950591)
  ·
    refine ⟨92507627847307941152925887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61671751898205294101950591 92507627847307941152925887)
    ·
      refine ⟨138761441770961911729388831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92507627847307941152925887 138761441770961911729388831)
      ·
        refine ⟨208142162656442867594083247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138761441770961911729388831 208142162656442867594083247)
        ·
          refine ⟨312213243984664301391124871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208142162656442867594083247 312213243984664301391124871)
          ·
            refine ⟨468319865976996452086687307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312213243984664301391124871 468319865976996452086687307)
            ·
              refine ⟨702479798965494678130030961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468319865976996452086687307 702479798965494678130030961)
              ·
                refine ⟨526859849224121008597523221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702479798965494678130030961 526859849224121008597523221)
                ·
                  refine ⟨24696555432380672278008901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 526859849224121008597523221 24696555432380672278008901)
                  ·
                    refine ⟨4630604143571376052126669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24696555432380672278008901 4630604143571376052126669)
                    ·
                      refine ⟨1736476553839266019547501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4630604143571376052126669 1736476553839266019547501)
                      ·
                        rfl

theorem cell23_3381776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 3].length) (baseStart_3381776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381776 prefixEnd_3381776 := by exact prefixLift 3381776
  have htrace : WordTrace (prefixWord ++ tailWord_3381776) baseStart_3381776 baseEnd_3381776 := by
    simpa [prefixWord, tailWord_3381776, baseEnd_3381776] using wordTrace_append hprefix tailTrace_3381776
  have hstable : (prefixWord ++ tailWord_3381776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381776).length < 2 ^ (prefixWord ++ tailWord_3381776).sum := by decide
  have hdescent : baseEnd_3381776 < baseStart_3381776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381856 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 2, 8]
def baseStart_3381856 : Nat := 118140960795 + 3381856 * 2 ^ 59
def prefixEnd_3381856 : Nat := 4983230072969 + 3 ^ 40 * 3381856 * 2
def baseEnd_3381856 : Nat := 578839210763875235515711

theorem tailTrace_3381856 : CollatzResearch.WordTrace tailWord_3381856 prefixEnd_3381856 578839210763875235515711 := by
  unfold tailWord_3381856
  simp only [CollatzResearch.WordTrace]
  refine ⟨61673210818060380933406711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82230947757413841244542281 61673210818060380933406711)
  ·
    refine ⟨92509816227090571400110067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61673210818060380933406711 92509816227090571400110067)
    ·
      refine ⟨138764724340635857100165101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92509816227090571400110067 138764724340635857100165101)
      ·
        refine ⟨52036771627738446412561913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138764724340635857100165101 52036771627738446412561913)
        ·
          refine ⟨39027578720803834809421435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52036771627738446412561913 39027578720803834809421435)
          ·
            refine ⟨58541368081205752214132153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39027578720803834809421435 58541368081205752214132153)
            ·
              refine ⟨43906026060904314160599115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58541368081205752214132153 43906026060904314160599115)
              ·
                refine ⟨65859039091356471240898673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43906026060904314160599115 65859039091356471240898673)
                ·
                  refine ⟨49394279318517353430674005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65859039091356471240898673 49394279318517353430674005)
                  ·
                    refine ⟨578839210763875235515711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49394279318517353430674005 578839210763875235515711)
                    ·
                      rfl

theorem cell23_3381856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 2, 8].length) (baseStart_3381856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381856 prefixEnd_3381856 := by exact prefixLift 3381856
  have htrace : WordTrace (prefixWord ++ tailWord_3381856) baseStart_3381856 baseEnd_3381856 := by
    simpa [prefixWord, tailWord_3381856, baseEnd_3381856] using wordTrace_append hprefix tailTrace_3381856
  have hstable : (prefixWord ++ tailWord_3381856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381856).length < 2 ^ (prefixWord ++ tailWord_3381856).sum := by decide
  have hdescent : baseEnd_3381856 < baseStart_3381856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381883 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 3]
def baseStart_3381883 : Nat := 118140960795 + 3381883 * 2 ^ 59
def prefixEnd_3381883 : Nat := 4983230072969 + 3 ^ 40 * 3381883 * 2
def baseEnd_3381883 : Nat := 1736531496269297100909509

theorem tailTrace_3381883 : CollatzResearch.WordTrace tailWord_3381883 prefixEnd_3381883 1736531496269297100909509 := by
  unfold tailWord_3381883
  simp only [CollatzResearch.WordTrace]
  refine ⟨123347406407022945478046303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82231604271348630318697535 123347406407022945478046303)
  ·
    refine ⟨185021109610534418217069455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123347406407022945478046303 185021109610534418217069455)
    ·
      refine ⟨277531664415801627325604183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185021109610534418217069455 277531664415801627325604183)
      ·
        refine ⟨416297496623702440988406275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277531664415801627325604183 416297496623702440988406275)
        ·
          refine ⟨624446244935553661482609413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416297496623702440988406275 624446244935553661482609413)
          ·
            refine ⟨117083670925416311527989265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 624446244935553661482609413 117083670925416311527989265)
            ·
              refine ⟨87812753194062233645991949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117083670925416311527989265 87812753194062233645991949)
              ·
                refine ⟨32929782447773337617246981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87812753194062233645991949 32929782447773337617246981)
                ·
                  refine ⟨6174334208957500803233809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32929782447773337617246981 6174334208957500803233809)
                  ·
                    refine ⟨4630750656718125602425357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6174334208957500803233809 4630750656718125602425357)
                    ·
                      refine ⟨1736531496269297100909509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4630750656718125602425357 1736531496269297100909509)
                      ·
                        rfl

theorem cell23_3381883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 4, 2, 3].length) (baseStart_3381883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381883 prefixEnd_3381883 := by exact prefixLift 3381883
  have htrace : WordTrace (prefixWord ++ tailWord_3381883) baseStart_3381883 baseEnd_3381883 := by
    simpa [prefixWord, tailWord_3381883, baseEnd_3381883] using wordTrace_append hprefix tailTrace_3381883
  have hstable : (prefixWord ++ tailWord_3381883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381883).length < 2 ^ (prefixWord ++ tailWord_3381883).sum := by decide
  have hdescent : baseEnd_3381883 < baseStart_3381883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381914 : List Nat := [3, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3381914 : Nat := 118140960795 + 3381914 * 2 ^ 59
def prefixEnd_3381914 : Nat := 4983230072969 + 3 ^ 40 * 3381914 * 2
def baseEnd_3381914 : Nat := 1736547414169586479621867

theorem tailTrace_3381914 : CollatzResearch.WordTrace tailWord_3381914 prefixEnd_3381914 1736547414169586479621867 := by
  unfold tailWord_3381914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30837134267477659443106199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82232358046607091848283197 30837134267477659443106199)
  ·
    refine ⟨46255701401216489164659299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30837134267477659443106199 46255701401216489164659299)
    ·
      refine ⟨69383552101824733746988949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46255701401216489164659299 69383552101824733746988949)
      ·
        refine ⟨3252354004773034394390107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69383552101824733746988949 3252354004773034394390107)
        ·
          refine ⟨4878531007159551591585161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3252354004773034394390107 4878531007159551591585161)
          ·
            refine ⟨3658898255369663693688871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4878531007159551591585161 3658898255369663693688871)
            ·
              refine ⟨5488347383054495540533307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658898255369663693688871 5488347383054495540533307)
              ·
                refine ⟨8232521074581743310799961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488347383054495540533307 8232521074581743310799961)
                ·
                  refine ⟨6174390805936307483099971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8232521074581743310799961 6174390805936307483099971)
                  ·
                    refine ⟨9261586208904461224649957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174390805936307483099971 9261586208904461224649957)
                    ·
                      refine ⟨1736547414169586479621867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9261586208904461224649957 1736547414169586479621867)
                      ·
                        rfl

theorem cell23_3381914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3381914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381914 prefixEnd_3381914 := by exact prefixLift 3381914
  have htrace : WordTrace (prefixWord ++ tailWord_3381914) baseStart_3381914 baseEnd_3381914 := by
    simpa [prefixWord, tailWord_3381914, baseEnd_3381914] using wordTrace_append hprefix tailTrace_3381914
  have hstable : (prefixWord ++ tailWord_3381914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381914).length < 2 ^ (prefixWord ++ tailWord_3381914).sum := by decide
  have hdescent : baseEnd_3381914 < baseStart_3381914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381987 : List Nat := [1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 4]
def baseStart_3381987 : Nat := 118140960795 + 3381987 * 2 ^ 59
def prefixEnd_3381987 : Nat := 4983230072969 + 3 ^ 40 * 3381987 * 2
def baseEnd_3381987 : Nat := 1736584898257364694009031

theorem tailTrace_3381987 : CollatzResearch.WordTrace tailWord_3381987 prefixEnd_3381987 1736584898257364694009031 := by
  unfold tailWord_3381987
  simp only [CollatzResearch.WordTrace]
  refine ⟨123351199598646171239832215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82234133065764114159888143 123351199598646171239832215)
  ·
    refine ⟨185026799397969256859748323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123351199598646171239832215 185026799397969256859748323)
    ·
      refine ⟨277540199096953885289622485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185026799397969256859748323 277540199096953885289622485)
      ·
        refine ⟨6504848416334856686475527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 277540199096953885289622485 6504848416334856686475527)
        ·
          refine ⟨9757272624502285029713291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6504848416334856686475527 9757272624502285029713291)
          ·
            refine ⟨14635908936753427544569937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9757272624502285029713291 14635908936753427544569937)
            ·
              refine ⟨10976931702565070658427453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14635908936753427544569937 10976931702565070658427453)
              ·
                refine ⟨4116349388461901496910295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10976931702565070658427453 4116349388461901496910295)
                ·
                  refine ⟨6174524082692852245365443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116349388461901496910295 6174524082692852245365443)
                  ·
                    refine ⟨9261786124039278368048165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174524082692852245365443 9261786124039278368048165)
                    ·
                      refine ⟨1736584898257364694009031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9261786124039278368048165 1736584898257364694009031)
                      ·
                        rfl

theorem cell23_3381987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_3381987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381987 prefixEnd_3381987 := by exact prefixLift 3381987
  have htrace : WordTrace (prefixWord ++ tailWord_3381987) baseStart_3381987 baseEnd_3381987 := by
    simpa [prefixWord, tailWord_3381987, baseEnd_3381987] using wordTrace_append hprefix tailTrace_3381987
  have hstable : (prefixWord ++ tailWord_3381987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381987).length < 2 ^ (prefixWord ++ tailWord_3381987).sum := by decide
  have hdescent : baseEnd_3381987 < baseStart_3381987 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3381997 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 2, 4]
def baseStart_3381997 : Nat := 118140960795 + 3381997 * 2 ^ 59
def prefixEnd_3381997 : Nat := 4983230072969 + 3 ^ 40 * 3381997 * 2
def baseEnd_3381997 : Nat := 578863344354636551627995

theorem tailTrace_3381997 : CollatzResearch.WordTrace tailWord_3381997 prefixEnd_3381997 578863344354636551627995 := by
  unfold tailWord_3381997
  simp only [CollatzResearch.WordTrace]
  refine ⟨123351564328609942947696245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82234376219073295298464163 123351564328609942947696245)
  ·
    refine ⟨11564209155807182151346523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123351564328609942947696245 11564209155807182151346523)
    ·
      refine ⟨17346313733710773227019785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564209155807182151346523 17346313733710773227019785)
      ·
        refine ⟨13009735300283079920264839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17346313733710773227019785 13009735300283079920264839)
        ·
          refine ⟨19514602950424619880397259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13009735300283079920264839 19514602950424619880397259)
          ·
            refine ⟨29271904425636929820595889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19514602950424619880397259 29271904425636929820595889)
            ·
              refine ⟨21953928319227697365446917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29271904425636929820595889 21953928319227697365446917)
              ·
                refine ⟨4116361559855193256021297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21953928319227697365446917 4116361559855193256021297)
                ·
                  refine ⟨3087271169891394942015973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4116361559855193256021297 3087271169891394942015973)
                  ·
                    refine ⟨578863344354636551627995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087271169891394942015973 578863344354636551627995)
                    ·
                      rfl

theorem cell23_3381997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_3381997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3381997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3381997 prefixEnd_3381997 := by exact prefixLift 3381997
  have htrace : WordTrace (prefixWord ++ tailWord_3381997) baseStart_3381997 baseEnd_3381997 := by
    simpa [prefixWord, tailWord_3381997, baseEnd_3381997] using wordTrace_append hprefix tailTrace_3381997
  have hstable : (prefixWord ++ tailWord_3381997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3381997).length < 2 ^ (prefixWord ++ tailWord_3381997).sum := by decide
  have hdescent : baseEnd_3381997 < baseStart_3381997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3381997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382013 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3382013 : Nat := 118140960795 + 3382013 * 2 ^ 59
def prefixEnd_3382013 : Nat := 4983230072969 + 3 ^ 40 * 3382013 * 2
def baseEnd_3382013 : Nat := 1736598248754381592283911

theorem tailTrace_3382013 : CollatzResearch.WordTrace tailWord_3382013 prefixEnd_3382013 1736598248754381592283911 := by
  unfold tailWord_3382013
  simp only [CollatzResearch.WordTrace]
  refine ⟨123352147896551977680278693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82234765264367985120185795 123352147896551977680278693)
  ·
    refine ⟨23128527730603495815052255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123352147896551977680278693 23128527730603495815052255)
    ·
      refine ⟨34692791595905243722578383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23128527730603495815052255 34692791595905243722578383)
      ·
        refine ⟨52039187393857865583867575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34692791595905243722578383 52039187393857865583867575)
        ·
          refine ⟨78058781090786798375801363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52039187393857865583867575 78058781090786798375801363)
          ·
            refine ⟨117088171636180197563702045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78058781090786798375801363 117088171636180197563702045)
            ·
              refine ⟨43908064363567574086388267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117088171636180197563702045 43908064363567574086388267)
              ·
                refine ⟨65862096545351361129582401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43908064363567574086388267 65862096545351361129582401)
                ·
                  refine ⟨49396572409013520847186801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65862096545351361129582401 49396572409013520847186801)
                  ·
                    refine ⟨37047429306760140635390101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49396572409013520847186801 37047429306760140635390101)
                    ·
                      refine ⟨1736598248754381592283911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37047429306760140635390101 1736598248754381592283911)
                      ·
                        rfl

theorem cell23_3382013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3382013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382013 prefixEnd_3382013 := by exact prefixLift 3382013
  have htrace : WordTrace (prefixWord ++ tailWord_3382013) baseStart_3382013 baseEnd_3382013 := by
    simpa [prefixWord, tailWord_3382013, baseEnd_3382013] using wordTrace_append hprefix tailTrace_3382013
  have hstable : (prefixWord ++ tailWord_3382013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382013).length < 2 ^ (prefixWord ++ tailWord_3382013).sum := by decide
  have hdescent : baseEnd_3382013 < baseStart_3382013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382014 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_3382014 : Nat := 118140960795 + 3382014 * 2 ^ 59
def prefixEnd_3382014 : Nat := 4983230072969 + 3 ^ 40 * 3382014 * 2
def baseEnd_3382014 : Nat := 578866254078345362790469

theorem tailTrace_3382014 : CollatzResearch.WordTrace tailWord_3382014 prefixEnd_3382014 578866254078345362790469 := by
  unfold tailWord_3382014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15419023046193544356383137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82234789579698903234043397 15419023046193544356383137)
  ·
    refine ⟨11564267284645158267287353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15419023046193544356383137 11564267284645158267287353)
    ·
      refine ⟨8673200463483868700465515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11564267284645158267287353 8673200463483868700465515)
      ·
        refine ⟨13009800695225803050698273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673200463483868700465515 13009800695225803050698273)
        ·
          refine ⟨9757350521419352288023705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13009800695225803050698273 9757350521419352288023705)
          ·
            refine ⟨7318012891064514216017779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9757350521419352288023705 7318012891064514216017779)
            ·
              refine ⟨10977019336596771324026669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318012891064514216017779 10977019336596771324026669)
              ·
                refine ⟨4116382251223789246510001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10977019336596771324026669 4116382251223789246510001)
                ·
                  refine ⟨3087286688417841934882501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4116382251223789246510001 3087286688417841934882501)
                  ·
                    refine ⟨578866254078345362790469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3087286688417841934882501 578866254078345362790469)
                    ·
                      rfl

theorem cell23_3382014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_3382014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382014 prefixEnd_3382014 := by exact prefixLift 3382014
  have htrace : WordTrace (prefixWord ++ tailWord_3382014) baseStart_3382014 baseEnd_3382014 := by
    simpa [prefixWord, tailWord_3382014, baseEnd_3382014] using wordTrace_append hprefix tailTrace_3382014
  have hstable : (prefixWord ++ tailWord_3382014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382014).length < 2 ^ (prefixWord ++ tailWord_3382014).sum := by decide
  have hdescent : baseEnd_3382014 < baseStart_3382014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382024 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3382024 : Nat := 118140960795 + 3382024 * 2 ^ 59
def prefixEnd_3382024 : Nat := 4983230072969 + 3 ^ 40 * 3382024 * 2
def baseEnd_3382024 : Nat := 1736603897041581049246361

theorem tailTrace_3382024 : CollatzResearch.WordTrace tailWord_3382024 prefixEnd_3382024 1736603897041581049246361 := by
  unfold tailWord_3382024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61676274549756063279464563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82235032733008084372619417 61676274549756063279464563)
  ·
    refine ⟨92514411824634094919196845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61676274549756063279464563 92514411824634094919196845)
    ·
      refine ⟨34692904434237785594698817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92514411824634094919196845 34692904434237785594698817)
      ·
        refine ⟨26019678325678339196024113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34692904434237785594698817 26019678325678339196024113)
        ·
          refine ⟨19514758744258754397018085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26019678325678339196024113 19514758744258754397018085)
          ·
            refine ⟨3659017264548516449440891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19514758744258754397018085 3659017264548516449440891)
            ·
              refine ⟨5488525896822774674161337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659017264548516449440891 5488525896822774674161337)
              ·
                refine ⟨4116394422617081005621003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5488525896822774674161337 4116394422617081005621003)
                ·
                  refine ⟨6174591633925621508431505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116394422617081005621003 6174591633925621508431505)
                  ·
                    refine ⟨4630943725444216131323629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6174591633925621508431505 4630943725444216131323629)
                    ·
                      refine ⟨1736603897041581049246361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4630943725444216131323629 1736603897041581049246361)
                      ·
                        rfl

theorem cell23_3382024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3382024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382024 prefixEnd_3382024 := by exact prefixLift 3382024
  have htrace : WordTrace (prefixWord ++ tailWord_3382024) baseStart_3382024 baseEnd_3382024 := by
    simpa [prefixWord, tailWord_3382024, baseEnd_3382024] using wordTrace_append hprefix tailTrace_3382024
  have hstable : (prefixWord ++ tailWord_3382024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382024).length < 2 ^ (prefixWord ++ tailWord_3382024).sum := by decide
  have hdescent : baseEnd_3382024 < baseStart_3382024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382033 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 5]
def baseStart_3382033 : Nat := 118140960795 + 3382033 * 2 ^ 59
def prefixEnd_3382033 : Nat := 4983230072969 + 3 ^ 40 * 3382033 * 2
def baseEnd_3382033 : Nat := 1736608518367471514033819

theorem tailTrace_3382033 : CollatzResearch.WordTrace tailWord_3382033 prefixEnd_3382033 1736608518367471514033819 := by
  unfold tailWord_3382033
  simp only [CollatzResearch.WordTrace]
  refine ⟨123352877356479521096006753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82235251570986347397337835 123352877356479521096006753)
  ·
    refine ⟨92514658017359640822005065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123352877356479521096006753 92514658017359640822005065)
    ·
      refine ⟨69385993513019730616503799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92514658017359640822005065 69385993513019730616503799)
      ·
        refine ⟨104078990269529595924755699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69385993513019730616503799 104078990269529595924755699)
        ·
          refine ⟨156118485404294393887133549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104078990269529595924755699 156118485404294393887133549)
          ·
            refine ⟨58544432026610397707675081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156118485404294393887133549 58544432026610397707675081)
            ·
              refine ⟨43908324019957798280756311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58544432026610397707675081 43908324019957798280756311)
              ·
                refine ⟨65862486029936697421134467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43908324019957798280756311 65862486029936697421134467)
                ·
                  refine ⟨98793729044905046131701701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65862486029936697421134467 98793729044905046131701701)
                  ·
                    refine ⟨18523824195919696149694069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98793729044905046131701701 18523824195919696149694069)
                    ·
                      refine ⟨1736608518367471514033819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18523824195919696149694069 1736608518367471514033819)
                      ·
                        rfl

theorem cell23_3382033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 5].length) (baseStart_3382033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382033 prefixEnd_3382033 := by exact prefixLift 3382033
  have htrace : WordTrace (prefixWord ++ tailWord_3382033) baseStart_3382033 baseEnd_3382033 := by
    simpa [prefixWord, tailWord_3382033, baseEnd_3382033] using wordTrace_append hprefix tailTrace_3382033
  have hstable : (prefixWord ++ tailWord_3382033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382033).length < 2 ^ (prefixWord ++ tailWord_3382033).sum := by decide
  have hdescent : baseEnd_3382033 < baseStart_3382033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382034 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_3382034 : Nat := 118140960795 + 3382034 * 2 ^ 59
def prefixEnd_3382034 : Nat := 4983230072969 + 3 ^ 40 * 3382034 * 2
def baseEnd_3382034 : Nat := 1736609031848126010121315

theorem tailTrace_3382034 : CollatzResearch.WordTrace tailWord_3382034 prefixEnd_3382034 1736609031848126010121315 := by
  unfold tailWord_3382034
  simp only [CollatzResearch.WordTrace]
  refine ⟨30838228457368974566698289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82235275886317265511195437 30838228457368974566698289)
  ·
    refine ⟨23128671343026730925023717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30838228457368974566698289 23128671343026730925023717)
    ·
      refine ⟨4336625876817512048441947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23128671343026730925023717 4336625876817512048441947)
      ·
        refine ⟨6504938815226268072662921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4336625876817512048441947 6504938815226268072662921)
        ·
          refine ⟨4878704111419701054497191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6504938815226268072662921 4878704111419701054497191)
          ·
            refine ⟨7318056167129551581745787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878704111419701054497191 7318056167129551581745787)
            ·
              refine ⟨10977084250694327372618681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318056167129551581745787 10977084250694327372618681)
              ·
                refine ⟨8232813188020745529464011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10977084250694327372618681 8232813188020745529464011)
                ·
                  refine ⟨12349219782031118294196017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8232813188020745529464011 12349219782031118294196017)
                  ·
                    refine ⟨9261914836523338720647013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12349219782031118294196017 9261914836523338720647013)
                    ·
                      refine ⟨1736609031848126010121315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9261914836523338720647013 1736609031848126010121315)
                      ·
                        rfl

theorem cell23_3382034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_3382034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382034 prefixEnd_3382034 := by exact prefixLift 3382034
  have htrace : WordTrace (prefixWord ++ tailWord_3382034) baseStart_3382034 baseEnd_3382034 := by
    simpa [prefixWord, tailWord_3382034, baseEnd_3382034] using wordTrace_append hprefix tailTrace_3382034
  have hstable : (prefixWord ++ tailWord_3382034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382034).length < 2 ^ (prefixWord ++ tailWord_3382034).sum := by decide
  have hdescent : baseEnd_3382034 < baseStart_3382034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382043 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4]
def baseStart_3382043 : Nat := 118140960795 + 3382043 * 2 ^ 59
def prefixEnd_3382043 : Nat := 4983230072969 + 3 ^ 40 * 3382043 * 2
def baseEnd_3382043 : Nat := 1736613653174016474908773

theorem tailTrace_3382043 : CollatzResearch.WordTrace tailWord_3382043 prefixEnd_3382043 1736613653174016474908773 := by
  unfold tailWord_3382043
  simp only [CollatzResearch.WordTrace]
  refine ⟨123353242086443292803870783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82235494724295528535913855 123353242086443292803870783)
  ·
    refine ⟨185029863129664939205806175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123353242086443292803870783 185029863129664939205806175)
    ·
      refine ⟨277544794694497408808709263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185029863129664939205806175 277544794694497408808709263)
      ·
        refine ⟨416317192041746113213063895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277544794694497408808709263 416317192041746113213063895)
        ·
          refine ⟨624475788062619169819595843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 416317192041746113213063895 624475788062619169819595843)
          ·
            refine ⟨936713682093928754729393765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624475788062619169819595843 936713682093928754729393765)
            ·
              refine ⟨175633815392611641511761331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 936713682093928754729393765 175633815392611641511761331)
              ·
                refine ⟨263450723088917462267641997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175633815392611641511761331 263450723088917462267641997)
                ·
                  refine ⟨98794021158344048350365749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 263450723088917462267641997 98794021158344048350365749)
                  ·
                    refine ⟨9261939483594754532846789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98794021158344048350365749 9261939483594754532846789)
                    ·
                      refine ⟨1736613653174016474908773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9261939483594754532846789 1736613653174016474908773)
                      ·
                        rfl

theorem cell23_3382043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 4].length) (baseStart_3382043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382043 prefixEnd_3382043 := by exact prefixLift 3382043
  have htrace : WordTrace (prefixWord ++ tailWord_3382043) baseStart_3382043 baseEnd_3382043 := by
    simpa [prefixWord, tailWord_3382043, baseEnd_3382043] using wordTrace_append hprefix tailTrace_3382043
  have hstable : (prefixWord ++ tailWord_3382043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382043).length < 2 ^ (prefixWord ++ tailWord_3382043).sum := by decide
  have hdescent : baseEnd_3382043 < baseStart_3382043 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382061 : List Nat := [1, 5, 3, 2, 2, 1, 1, 8]
def baseStart_3382061 : Nat := 118140960795 + 3382061 * 2 ^ 59
def prefixEnd_3382061 : Nat := 4983230072969 + 3 ^ 40 * 3382061 * 2
def baseEnd_3382061 : Nat := 64319366512066570536433

theorem tailTrace_3382061 : CollatzResearch.WordTrace tailWord_3382061 prefixEnd_3382061 64319366512066570536433 := by
  unfold tailWord_3382061
  simp only [CollatzResearch.WordTrace]
  refine ⟨123353898600378081878026037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82235932400252054585350691 123353898600378081878026037)
  ·
    refine ⟨11564427993785445176064941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123353898600378081878026037 11564427993785445176064941)
    ·
      refine ⟨4336660497669541941024353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11564427993785445176064941 4336660497669541941024353)
      ·
        refine ⟨3252495373252156455768265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4336660497669541941024353 3252495373252156455768265)
        ·
          refine ⟨2439371529939117341826199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3252495373252156455768265 2439371529939117341826199)
          ·
            refine ⟨3659057294908676012739299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439371529939117341826199 3659057294908676012739299)
            ·
              refine ⟨5488585942363014019108949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3659057294908676012739299 5488585942363014019108949)
              ·
                refine ⟨64319366512066570536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5488585942363014019108949 64319366512066570536433)
                ·
                  rfl

theorem cell23_3382061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 8].length) (baseStart_3382061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382061 prefixEnd_3382061 := by exact prefixLift 3382061
  have htrace : WordTrace (prefixWord ++ tailWord_3382061) baseStart_3382061 baseEnd_3382061 := by
    simpa [prefixWord, tailWord_3382061, baseEnd_3382061] using wordTrace_append hprefix tailTrace_3382061
  have hstable : (prefixWord ++ tailWord_3382061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382061).length < 2 ^ (prefixWord ++ tailWord_3382061).sum := by decide
  have hdescent : baseEnd_3382061 < baseStart_3382061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3382117 : List Nat := [1, 3, 1, 3, 1, 1, 4, 4, 5]
def baseStart_3382117 : Nat := 118140960795 + 3382117 * 2 ^ 59
def prefixEnd_3382117 : Nat := 4983230072969 + 3 ^ 40 * 3382117 * 2
def baseEnd_3382117 : Nat := 192961294526938798375937

theorem tailTrace_3382117 : CollatzResearch.WordTrace tailWord_3382117 prefixEnd_3382117 192961294526938798375937 := by
  unfold tailWord_3382117
  simp only [CollatzResearch.WordTrace]
  refine ⟨123355941088175203442064605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82237294058783468961376403 123355941088175203442064605)
  ·
    refine ⟨46258477908065701290774227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123355941088175203442064605 46258477908065701290774227)
    ·
      refine ⟨69387716862098551936161341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46258477908065701290774227 69387716862098551936161341)
      ·
        refine ⟨26020393823286956976060503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69387716862098551936161341 26020393823286956976060503)
        ·
          refine ⟨39030590734930435464090755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26020393823286956976060503 39030590734930435464090755)
          ·
            refine ⟨58545886102395653196136133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39030590734930435464090755 58545886102395653196136133)
            ·
              refine ⟨10977353644199184974275525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58545886102395653196136133 10977353644199184974275525)
              ·
                refine ⟨2058253808287347182676661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10977353644199184974275525 2058253808287347182676661)
                ·
                  refine ⟨192961294526938798375937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2058253808287347182676661 192961294526938798375937)
                  ·
                    rfl

theorem cell23_3382117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 5].length) (baseStart_3382117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3382117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3382117 prefixEnd_3382117 := by exact prefixLift 3382117
  have htrace : WordTrace (prefixWord ++ tailWord_3382117) baseStart_3382117 baseEnd_3382117 := by
    simpa [prefixWord, tailWord_3382117, baseEnd_3382117] using wordTrace_append hprefix tailTrace_3382117
  have hstable : (prefixWord ++ tailWord_3382117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3382117).length < 2 ^ (prefixWord ++ tailWord_3382117).sum := by decide
  have hdescent : baseEnd_3382117 < baseStart_3382117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3382117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
