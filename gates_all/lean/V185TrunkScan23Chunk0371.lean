import V185TrunkScan23Chunk0370

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2193954 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2193954 : Nat := 118140960795 + 2193954 * 2 ^ 59
def prefixEnd_2193954 : Nat := 4983230072969 + 3 ^ 40 * 2193954 * 2
def baseEnd_2193954 : Nat := 1126552935854414378585195

theorem tailTrace_2193954 : CollatzResearch.WordTrace tailWord_2193954 prefixEnd_2193954 1126552935854414378585195 := by
  unfold tailWord_2193954
  simp only [CollatzResearch.WordTrace]
  refine ⟨20005019073421707589279229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53346717529124553571411277 20005019073421707589279229)
  ·
    refine ⟨7501882152533140345979711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20005019073421707589279229 7501882152533140345979711)
    ·
      refine ⟨11252823228799710518969567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7501882152533140345979711 11252823228799710518969567)
      ·
        refine ⟨16879234843199565778454351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11252823228799710518969567 16879234843199565778454351)
        ·
          refine ⟨25318852264799348667681527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16879234843199565778454351 25318852264799348667681527)
          ·
            refine ⟨37978278397199023001522291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25318852264799348667681527 37978278397199023001522291)
            ·
              refine ⟨56967417595798534502283437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37978278397199023001522291 56967417595798534502283437)
              ·
                refine ⟨21362781598424450438356289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56967417595798534502283437 21362781598424450438356289)
                ·
                  refine ⟨16022086198818337828767217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21362781598424450438356289 16022086198818337828767217)
                  ·
                    refine ⟨12016564649113753371575413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16022086198818337828767217 12016564649113753371575413)
                    ·
                      refine ⟨1126552935854414378585195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12016564649113753371575413 1126552935854414378585195)
                      ·
                        rfl

theorem cell23_2193954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2193954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193954 prefixEnd_2193954 := by exact prefixLift 2193954
  have htrace : WordTrace (prefixWord ++ tailWord_2193954) baseStart_2193954 baseEnd_2193954 := by
    simpa [prefixWord, tailWord_2193954, baseEnd_2193954] using wordTrace_append hprefix tailTrace_2193954
  have hstable : (prefixWord ++ tailWord_2193954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193954).length < 2 ^ (prefixWord ++ tailWord_2193954).sum := by decide
  have hdescent : baseEnd_2193954 < baseStart_2193954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193959 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2193959 : Nat := 118140960795 + 2193959 * 2 ^ 59
def prefixEnd_2193959 : Nat := 4983230072969 + 3 ^ 40 * 2193959 * 2
def baseEnd_2193959 : Nat := 1126555503257686859022673

theorem tailTrace_2193959 : CollatzResearch.WordTrace tailWord_2193959 prefixEnd_2193959 1126555503257686859022673 := by
  unfold tailWord_2193959
  simp only [CollatzResearch.WordTrace]
  refine ⟨80020258658668716211048931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53346839105779144140699287 80020258658668716211048931)
  ·
    refine ⟨120030387988003074316573397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80020258658668716211048931 120030387988003074316573397)
    ·
      refine ⟨2813212218468822054294689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 120030387988003074316573397 2813212218468822054294689)
      ·
        refine ⟨2109909163851616540721017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2813212218468822054294689 2109909163851616540721017)
        ·
          refine ⟨1582431872888712405540763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2109909163851616540721017 1582431872888712405540763)
          ·
            refine ⟨2373647809333068608311145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1582431872888712405540763 2373647809333068608311145)
            ·
              refine ⟨1780235856999801456233359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2373647809333068608311145 1780235856999801456233359)
              ·
                refine ⟨2670353785499702184350039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780235856999801456233359 2670353785499702184350039)
                ·
                  refine ⟨4005530678249553276525059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670353785499702184350039 4005530678249553276525059)
                  ·
                    refine ⟨6008296017374329914787589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4005530678249553276525059 6008296017374329914787589)
                    ·
                      refine ⟨1126555503257686859022673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6008296017374329914787589 1126555503257686859022673)
                      ·
                        rfl

theorem cell23_2193959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2193959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193959 prefixEnd_2193959 := by exact prefixLift 2193959
  have htrace : WordTrace (prefixWord ++ tailWord_2193959) baseStart_2193959 baseEnd_2193959 := by
    simpa [prefixWord, tailWord_2193959, baseEnd_2193959] using wordTrace_append hprefix tailTrace_2193959
  have hstable : (prefixWord ++ tailWord_2193959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193959).length < 2 ^ (prefixWord ++ tailWord_2193959).sum := by decide
  have hdescent : baseEnd_2193959 < baseStart_2193959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193984 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3]
def baseStart_2193984 : Nat := 118140960795 + 2193984 * 2 ^ 59
def prefixEnd_2193984 : Nat := 4983230072969 + 3 ^ 40 * 2193984 * 2
def baseEnd_2193984 : Nat := 1126568340274049261210057

theorem tailTrace_2193984 : CollatzResearch.WordTrace tailWord_2193984 prefixEnd_2193984 1126568340274049261210057 := by
  unfold tailWord_2193984
  simp only [CollatzResearch.WordTrace]
  refine ⟨40010585241789072740354503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53347446989052096987139337 40010585241789072740354503)
  ·
    refine ⟨60015877862683609110531755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40010585241789072740354503 60015877862683609110531755)
    ·
      refine ⟨90023816794025413665797633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60015877862683609110531755 90023816794025413665797633)
      ·
        refine ⟨67517862595519060249348225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90023816794025413665797633 67517862595519060249348225)
        ·
          refine ⟨50638396946639295187011169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67517862595519060249348225 50638396946639295187011169)
          ·
            refine ⟨37978797709979471390258377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50638396946639295187011169 37978797709979471390258377)
            ·
              refine ⟨28484098282484603542693783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37978797709979471390258377 28484098282484603542693783)
              ·
                refine ⟨42726147423726905314040675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28484098282484603542693783 42726147423726905314040675)
                ·
                  refine ⟨64089221135590357971061013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42726147423726905314040675 64089221135590357971061013)
                  ·
                    refine ⟨3004182240730798029893485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64089221135590357971061013 3004182240730798029893485)
                    ·
                      refine ⟨1126568340274049261210057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3004182240730798029893485 1126568340274049261210057)
                      ·
                        rfl

theorem cell23_2193984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_2193984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193984 prefixEnd_2193984 := by exact prefixLift 2193984
  have htrace : WordTrace (prefixWord ++ tailWord_2193984) baseStart_2193984 baseEnd_2193984 := by
    simpa [prefixWord, tailWord_2193984, baseEnd_2193984] using wordTrace_append hprefix tailTrace_2193984
  have hstable : (prefixWord ++ tailWord_2193984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193984).length < 2 ^ (prefixWord ++ tailWord_2193984).sum := by decide
  have hdescent : baseEnd_2193984 < baseStart_2193984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2193998 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2]
def baseStart_2193998 : Nat := 118140960795 + 2193998 * 2 ^ 59
def prefixEnd_2193998 : Nat := 4983230072969 + 3 ^ 40 * 2193998 * 2
def baseEnd_2193998 : Nat := 1126575529003212206434993

theorem tailTrace_2193998 : CollatzResearch.WordTrace tailWord_2193998 prefixEnd_2193998 1126575529003212206434993 := by
  unfold tailWord_2193998
  simp only [CollatzResearch.WordTrace]
  refine ⟨10002710138190928233964831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53347787403684950581145765 10002710138190928233964831)
  ·
    refine ⟨15004065207286392350947247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10002710138190928233964831 15004065207286392350947247)
    ·
      refine ⟨22506097810929588526420871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15004065207286392350947247 22506097810929588526420871)
      ·
        refine ⟨33759146716394382789631307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22506097810929588526420871 33759146716394382789631307)
        ·
          refine ⟨50638720074591574184446961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33759146716394382789631307 50638720074591574184446961)
          ·
            refine ⟨37979040055943680638335221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50638720074591574184446961 37979040055943680638335221)
            ·
              refine ⟨3560535005244720059843927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37979040055943680638335221 3560535005244720059843927)
              ·
                refine ⟨5340802507867080089765891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3560535005244720059843927 5340802507867080089765891)
                ·
                  refine ⟨8011203761800620134648837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5340802507867080089765891 8011203761800620134648837)
                  ·
                    refine ⟨1502100705337616275246657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8011203761800620134648837 1502100705337616275246657)
                    ·
                      refine ⟨1126575529003212206434993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502100705337616275246657 1126575529003212206434993)
                      ·
                        rfl

theorem cell23_2193998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2].length) (baseStart_2193998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2193998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2193998 prefixEnd_2193998 := by exact prefixLift 2193998
  have htrace : WordTrace (prefixWord ++ tailWord_2193998) baseStart_2193998 baseEnd_2193998 := by
    simpa [prefixWord, tailWord_2193998, baseEnd_2193998] using wordTrace_append hprefix tailTrace_2193998
  have hstable : (prefixWord ++ tailWord_2193998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2193998).length < 2 ^ (prefixWord ++ tailWord_2193998).sum := by decide
  have hdescent : baseEnd_2193998 < baseStart_2193998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2193998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194044 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_2194044 : Nat := 118140960795 + 2194044 * 2 ^ 59
def prefixEnd_2194044 : Nat := 4983230072969 + 3 ^ 40 * 2194044 * 2
def baseEnd_2194044 : Nat := 1126599149113319026459781

theorem tailTrace_2194044 : CollatzResearch.WordTrace tailWord_2194044 prefixEnd_2194044 1126599149113319026459781 := by
  unfold tailWord_2194044
  simp only [CollatzResearch.WordTrace]
  refine ⟨40011679431680387863946593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53348905908907183818595457 40011679431680387863946593)
  ·
    refine ⟨30008759573760290897959945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40011679431680387863946593 30008759573760290897959945)
    ·
      refine ⟨22506569680320218173469959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30008759573760290897959945 22506569680320218173469959)
      ·
        refine ⟨33759854520480327260204939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22506569680320218173469959 33759854520480327260204939)
        ·
          refine ⟨50639781780720490890307409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33759854520480327260204939 50639781780720490890307409)
          ·
            refine ⟨37979836335540368167730557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50639781780720490890307409 37979836335540368167730557)
            ·
              refine ⟨14242438625827638062898959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37979836335540368167730557 14242438625827638062898959)
              ·
                refine ⟨21363657938741457094348439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14242438625827638062898959 21363657938741457094348439)
                ·
                  refine ⟨32045486908112185641522659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21363657938741457094348439 32045486908112185641522659)
                  ·
                    refine ⟨48068230362168278462283989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32045486908112185641522659 48068230362168278462283989)
                    ·
                      refine ⟨1126599149113319026459781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48068230362168278462283989 1126599149113319026459781)
                      ·
                        rfl

theorem cell23_2194044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_2194044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194044 prefixEnd_2194044 := by exact prefixLift 2194044
  have htrace : WordTrace (prefixWord ++ tailWord_2194044) baseStart_2194044 baseEnd_2194044 := by
    simpa [prefixWord, tailWord_2194044, baseEnd_2194044] using wordTrace_append hprefix tailTrace_2194044
  have hstable : (prefixWord ++ tailWord_2194044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194044).length < 2 ^ (prefixWord ++ tailWord_2194044).sum := by decide
  have hdescent : baseEnd_2194044 < baseStart_2194044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194068 : List Nat := [2, 4, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_2194068 : Nat := 118140960795 + 2194068 * 2 ^ 59
def prefixEnd_2194068 : Nat := 4983230072969 + 3 ^ 40 * 2194068 * 2
def baseEnd_2194068 : Nat := 375537157549675644186557

theorem tailTrace_2194068 : CollatzResearch.WordTrace tailWord_2194068 prefixEnd_2194068 375537157549675644186557 := by
  unfold tailWord_2194068
  simp only [CollatzResearch.WordTrace]
  refine ⟨40012117107636913913383429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53349489476849218551177905 40012117107636913913383429)
  ·
    refine ⟨7502271957681921358759393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40012117107636913913383429 7502271957681921358759393)
    ·
      refine ⟨5626703968261441019069545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7502271957681921358759393 5626703968261441019069545)
      ·
        refine ⟨4220027976196080764302159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5626703968261441019069545 4220027976196080764302159)
        ·
          refine ⟨6330041964294121146453239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220027976196080764302159 6330041964294121146453239)
          ·
            refine ⟨9495062946441181719679859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330041964294121146453239 9495062946441181719679859)
            ·
              refine ⟨14242594419661772579519789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9495062946441181719679859 14242594419661772579519789)
              ·
                refine ⟨5340972907373164717319921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14242594419661772579519789 5340972907373164717319921)
                ·
                  refine ⟨4005729680529873537989941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5340972907373164717319921 4005729680529873537989941)
                  ·
                    refine ⟨375537157549675644186557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4005729680529873537989941 375537157549675644186557)
                    ·
                      rfl

theorem cell23_2194068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_2194068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194068 prefixEnd_2194068 := by exact prefixLift 2194068
  have htrace : WordTrace (prefixWord ++ tailWord_2194068) baseStart_2194068 baseEnd_2194068 := by
    simpa [prefixWord, tailWord_2194068, baseEnd_2194068] using wordTrace_append hprefix tailTrace_2194068
  have hstable : (prefixWord ++ tailWord_2194068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194068).length < 2 ^ (prefixWord ++ tailWord_2194068).sum := by decide
  have hdescent : baseEnd_2194068 < baseStart_2194068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194111 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 6]
def baseStart_2194111 : Nat := 118140960795 + 2194111 * 2 ^ 59
def prefixEnd_2194111 : Nat := 4983230072969 + 3 ^ 40 * 2194111 * 2
def baseEnd_2194111 : Nat := 125181505813018918257997

theorem tailTrace_2194111 : CollatzResearch.WordTrace tailWord_2194111 prefixEnd_2194111 125181505813018918257997 := by
  unfold tailWord_2194111
  simp only [CollatzResearch.WordTrace]
  refine ⟨80025802554118046170582187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53350535036078697447054791 80025802554118046170582187)
  ·
    refine ⟨120038703831177069255873281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80025802554118046170582187 120038703831177069255873281)
    ·
      refine ⟨90029027873382801941904961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120038703831177069255873281 90029027873382801941904961)
      ·
        refine ⟨67521770905037101456428721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90029027873382801941904961 67521770905037101456428721)
        ·
          refine ⟨50641328178777826092321541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67521770905037101456428721 50641328178777826092321541)
          ·
            refine ⟨9495249033520842392310289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50641328178777826092321541 9495249033520842392310289)
            ·
              refine ⟨7121436775140631794232717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9495249033520842392310289 7121436775140631794232717)
              ·
                refine ⟨2670538790677736922837269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7121436775140631794232717 2670538790677736922837269)
                ·
                  refine ⟨125181505813018918257997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2670538790677736922837269 125181505813018918257997)
                  ·
                    rfl

theorem cell23_2194111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 6].length) (baseStart_2194111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194111 prefixEnd_2194111 := by exact prefixLift 2194111
  have htrace : WordTrace (prefixWord ++ tailWord_2194111) baseStart_2194111 baseEnd_2194111 := by
    simpa [prefixWord, tailWord_2194111, baseEnd_2194111] using wordTrace_append hprefix tailTrace_2194111
  have hstable : (prefixWord ++ tailWord_2194111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194111).length < 2 ^ (prefixWord ++ tailWord_2194111).sum := by decide
  have hdescent : baseEnd_2194111 < baseStart_2194111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194138 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3]
def baseStart_2194138 : Nat := 118140960795 + 2194138 * 2 ^ 59
def prefixEnd_2194138 : Nat := 4983230072969 + 3 ^ 40 * 2194138 * 2
def baseEnd_2194138 : Nat := 1126647416294841658684349

theorem tailTrace_2194138 : CollatzResearch.WordTrace tailWord_2194138 prefixEnd_2194138 1126647416294841658684349 := by
  unfold tailWord_2194138
  simp only [CollatzResearch.WordTrace]
  refine ⟨20006696831255057445453767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53351191550013486521210045 20006696831255057445453767)
  ·
    refine ⟨30010045246882586168180651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20006696831255057445453767 30010045246882586168180651)
    ·
      refine ⟨45015067870323879252270977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30010045246882586168180651 45015067870323879252270977)
      ·
        refine ⟨33761300902742909439203233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45015067870323879252270977 33761300902742909439203233)
        ·
          refine ⟨25320975677057182079402425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33761300902742909439203233 25320975677057182079402425)
          ·
            refine ⟨18990731757792886559551819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25320975677057182079402425 18990731757792886559551819)
            ·
              refine ⟨28486097636689329839327729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18990731757792886559551819 28486097636689329839327729)
              ·
                refine ⟨21364573227516997379495797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28486097636689329839327729 21364573227516997379495797)
                ·
                  refine ⟨2002928740079718504327731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21364573227516997379495797 2002928740079718504327731)
                  ·
                    refine ⟨3004393110119577756491597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2002928740079718504327731 3004393110119577756491597)
                    ·
                      refine ⟨1126647416294841658684349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3004393110119577756491597 1126647416294841658684349)
                      ·
                        rfl

theorem cell23_2194138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 1, 3].length) (baseStart_2194138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194138 prefixEnd_2194138 := by exact prefixLift 2194138
  have htrace : WordTrace (prefixWord ++ tailWord_2194138) baseStart_2194138 baseEnd_2194138 := by
    simpa [prefixWord, tailWord_2194138, baseEnd_2194138] using wordTrace_append hprefix tailTrace_2194138
  have hstable : (prefixWord ++ tailWord_2194138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194138).length < 2 ^ (prefixWord ++ tailWord_2194138).sum := by decide
  have hdescent : baseEnd_2194138 < baseStart_2194138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194181 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_2194181 : Nat := 118140960795 + 2194181 * 2 ^ 59
def prefixEnd_2194181 : Nat := 4983230072969 + 3 ^ 40 * 2194181 * 2
def baseEnd_2194181 : Nat := 1126669495962984990446651

theorem tailTrace_2194181 : CollatzResearch.WordTrace tailWord_2194181 prefixEnd_2194181 1126669495962984990446651 := by
  unfold tailWord_2194181
  simp only [CollatzResearch.WordTrace]
  refine ⟨80028355663864448125630397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53352237109242965417086931 80028355663864448125630397)
  ·
    refine ⟨30010633373949168047111399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80028355663864448125630397 30010633373949168047111399)
    ·
      refine ⟨45015950060923752070667099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30010633373949168047111399 45015950060923752070667099)
      ·
        refine ⟨67523925091385628106000649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45015950060923752070667099 67523925091385628106000649)
        ·
          refine ⟨50642943818539221079500487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67523925091385628106000649 50642943818539221079500487)
          ·
            refine ⟨75964415727808831619250731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50642943818539221079500487 75964415727808831619250731)
            ·
              refine ⟨113946623591713247428876097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75964415727808831619250731 113946623591713247428876097)
              ·
                refine ⟨85459967693784935571657073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113946623591713247428876097 85459967693784935571657073)
                ·
                  refine ⟨64094975770338701678742805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85459967693784935571657073 64094975770338701678742805)
                  ·
                    refine ⟨3004451989234626641191069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64094975770338701678742805 3004451989234626641191069)
                    ·
                      refine ⟨1126669495962984990446651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3004451989234626641191069 1126669495962984990446651)
                      ·
                        rfl

theorem cell23_2194181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_2194181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194181 prefixEnd_2194181 := by exact prefixLift 2194181
  have htrace : WordTrace (prefixWord ++ tailWord_2194181) baseStart_2194181 baseEnd_2194181 := by
    simpa [prefixWord, tailWord_2194181, baseEnd_2194181] using wordTrace_append hprefix tailTrace_2194181
  have hstable : (prefixWord ++ tailWord_2194181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194181).length < 2 ^ (prefixWord ++ tailWord_2194181).sum := by decide
  have hdescent : baseEnd_2194181 < baseStart_2194181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194191 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 4]
def baseStart_2194191 : Nat := 118140960795 + 2194191 * 2 ^ 59
def prefixEnd_2194191 : Nat := 4983230072969 + 3 ^ 40 * 2194191 * 2
def baseEnd_2194191 : Nat := 1126674630769529951321605

theorem tailTrace_2194191 : CollatzResearch.WordTrace tailWord_2194191 prefixEnd_2194191 1126674630769529951321605 := by
  unfold tailWord_2194191
  simp only [CollatzResearch.WordTrace]
  refine ⟨80028720393828219833494427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53352480262552146555662951 80028720393828219833494427)
  ·
    refine ⟨120043080590742329750241641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80028720393828219833494427 120043080590742329750241641)
    ·
      refine ⟨90032310443056747312681231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120043080590742329750241641 90032310443056747312681231)
      ·
        refine ⟨135048465664585120969021847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90032310443056747312681231 135048465664585120969021847)
        ·
          refine ⟨202572698496877681453532771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135048465664585120969021847 202572698496877681453532771)
          ·
            refine ⟨303859047745316522180299157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202572698496877681453532771 303859047745316522180299157)
            ·
              refine ⟨14243392863061711977201523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 303859047745316522180299157 14243392863061711977201523)
              ·
                refine ⟨21365089294592567965802285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14243392863061711977201523 21365089294592567965802285)
                ·
                  refine ⟨8011908485472212987175857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21365089294592567965802285 8011908485472212987175857)
                  ·
                    refine ⟨6008931364104159740381893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8011908485472212987175857 6008931364104159740381893)
                    ·
                      refine ⟨1126674630769529951321605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6008931364104159740381893 1126674630769529951321605)
                      ·
                        rfl

theorem cell23_2194191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 4].length) (baseStart_2194191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194191 prefixEnd_2194191 := by exact prefixLift 2194191
  have htrace : WordTrace (prefixWord ++ tailWord_2194191) baseStart_2194191 baseEnd_2194191 := by
    simpa [prefixWord, tailWord_2194191, baseEnd_2194191] using wordTrace_append hprefix tailTrace_2194191
  have hstable : (prefixWord ++ tailWord_2194191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194191).length < 2 ^ (prefixWord ++ tailWord_2194191).sum := by decide
  have hdescent : baseEnd_2194191 < baseStart_2194191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194222 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 2, 4]
def baseStart_2194222 : Nat := 118140960795 + 2194222 * 2 ^ 59
def prefixEnd_2194222 : Nat := 4983230072969 + 3 ^ 40 * 2194222 * 2
def baseEnd_2194222 : Nat := 375563516223273110011321

theorem tailTrace_2194222 : CollatzResearch.WordTrace tailWord_2194222 prefixEnd_2194222 375563516223273110011321 := by
  unfold tailWord_2194222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10003731382089489015984115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53353234037810608085248613 10003731382089489015984115)
  ·
    refine ⟨15005597073134233523976173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10003731382089489015984115 15005597073134233523976173)
    ·
      refine ⟨5627098902425337571491065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15005597073134233523976173 5627098902425337571491065)
      ·
        refine ⟨4220324176819003178618299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5627098902425337571491065 4220324176819003178618299)
        ·
          refine ⟨6330486265228504767927449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220324176819003178618299 6330486265228504767927449)
          ·
            refine ⟨4747864698921378575945587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6330486265228504767927449 4747864698921378575945587)
            ·
              refine ⟨7121797048382067863918381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4747864698921378575945587 7121797048382067863918381)
              ·
                refine ⟨2670673893143275448969393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7121797048382067863918381 2670673893143275448969393)
                ·
                  refine ⟨2003005419857456586727045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2670673893143275448969393 2003005419857456586727045)
                  ·
                    refine ⟨375563516223273110011321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003005419857456586727045 375563516223273110011321)
                    ·
                      rfl

theorem cell23_2194222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_2194222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194222 prefixEnd_2194222 := by exact prefixLift 2194222
  have htrace : WordTrace (prefixWord ++ tailWord_2194222) baseStart_2194222 baseEnd_2194222 := by
    simpa [prefixWord, tailWord_2194222, baseEnd_2194222] using wordTrace_append hprefix tailTrace_2194222
  have hstable : (prefixWord ++ tailWord_2194222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194222).length < 2 ^ (prefixWord ++ tailWord_2194222).sum := by decide
  have hdescent : baseEnd_2194222 < baseStart_2194222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194246 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2194246 : Nat := 118140960795 + 2194246 * 2 ^ 59
def prefixEnd_2194246 : Nat := 4983230072969 + 3 ^ 40 * 2194246 * 2
def baseEnd_2194246 : Nat := 1126702872205527236133853

theorem tailTrace_2194246 : CollatzResearch.WordTrace tailWord_2194246 prefixEnd_2194246 1126702872205527236133853 := by
  unfold tailWord_2194246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500960200269655132085831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53353817605752642817831061 2500960200269655132085831)
  ·
    refine ⟨3751440300404482698128747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2500960200269655132085831 3751440300404482698128747)
    ·
      refine ⟨5627160450606724047193121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3751440300404482698128747 5627160450606724047193121)
      ·
        refine ⟨4220370337955043035394841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5627160450606724047193121 4220370337955043035394841)
        ·
          refine ⟨3165277753466282276546131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4220370337955043035394841 3165277753466282276546131)
          ·
            refine ⟨4747916630199423414819197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3165277753466282276546131 4747916630199423414819197)
            ·
              refine ⟨1780468736324783780557199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4747916630199423414819197 1780468736324783780557199)
              ·
                refine ⟨2670703104487175670835799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780468736324783780557199 2670703104487175670835799)
                ·
                  refine ⟨4006054656730763506253699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670703104487175670835799 4006054656730763506253699)
                  ·
                    refine ⟨6009081985096145259380549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4006054656730763506253699 6009081985096145259380549)
                    ·
                      refine ⟨1126702872205527236133853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6009081985096145259380549 1126702872205527236133853)
                      ·
                        rfl

theorem cell23_2194246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2194246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194246 prefixEnd_2194246 := by exact prefixLift 2194246
  have htrace : WordTrace (prefixWord ++ tailWord_2194246) baseStart_2194246 baseEnd_2194246 := by
    simpa [prefixWord, tailWord_2194246, baseEnd_2194246] using wordTrace_append hprefix tailTrace_2194246
  have hstable : (prefixWord ++ tailWord_2194246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194246).length < 2 ^ (prefixWord ++ tailWord_2194246).sum := by decide
  have hdescent : baseEnd_2194246 < baseStart_2194246 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194251 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4]
def baseStart_2194251 : Nat := 118140960795 + 2194251 * 2 ^ 59
def prefixEnd_2194251 : Nat := 4983230072969 + 3 ^ 40 * 2194251 * 2
def baseEnd_2194251 : Nat := 1126705439608799716571329

theorem tailTrace_2194251 : CollatzResearch.WordTrace tailWord_2194251 prefixEnd_2194251 1126705439608799716571329 := by
  unfold tailWord_2194251
  simp only [CollatzResearch.WordTrace]
  refine ⟨80030908773610850080678607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53353939182407233387119071 80030908773610850080678607)
  ·
    refine ⟨120046363160416275121017911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80030908773610850080678607 120046363160416275121017911)
    ·
      refine ⟨180069544740624412681526867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120046363160416275121017911 180069544740624412681526867)
      ·
        refine ⟨270104317110936619022290301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180069544740624412681526867 270104317110936619022290301)
        ·
          refine ⟨101289118916601232133358863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270104317110936619022290301 101289118916601232133358863)
          ·
            refine ⟨151933678374901848200038295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101289118916601232133358863 151933678374901848200038295)
            ·
              refine ⟨227900517562352772300057443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151933678374901848200038295 227900517562352772300057443)
              ·
                refine ⟨341850776343529158450086165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227900517562352772300057443 341850776343529158450086165)
                ·
                  refine ⟨16024255141102929302347789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 341850776343529158450086165 16024255141102929302347789)
                  ·
                    refine ⟨6009095677913598488380421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16024255141102929302347789 6009095677913598488380421)
                    ·
                      refine ⟨1126705439608799716571329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6009095677913598488380421 1126705439608799716571329)
                      ·
                        rfl

theorem cell23_2194251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 3, 4].length) (baseStart_2194251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194251 prefixEnd_2194251 := by exact prefixLift 2194251
  have htrace : WordTrace (prefixWord ++ tailWord_2194251) baseStart_2194251 baseEnd_2194251 := by
    simpa [prefixWord, tailWord_2194251, baseEnd_2194251] using wordTrace_append hprefix tailTrace_2194251
  have hstable : (prefixWord ++ tailWord_2194251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194251).length < 2 ^ (prefixWord ++ tailWord_2194251).sum := by decide
  have hdescent : baseEnd_2194251 < baseStart_2194251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194291 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 9]
def baseStart_2194291 : Nat := 118140960795 + 2194291 * 2 ^ 59
def prefixEnd_2194291 : Nat := 4983230072969 + 3 ^ 40 * 2194291 * 2
def baseEnd_2194291 : Nat := 125191775426108840007905

theorem tailTrace_2194291 : CollatzResearch.WordTrace tailWord_2194291 prefixEnd_2194291 125191775426108840007905 := by
  unfold tailWord_2194291
  simp only [CollatzResearch.WordTrace]
  refine ⟨80032367693465936912134727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53354911795643957941423151 80032367693465936912134727)
  ·
    refine ⟨120048551540198905368202091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80032367693465936912134727 120048551540198905368202091)
    ·
      refine ⟨180072827310298358052303137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120048551540198905368202091 180072827310298358052303137)
      ·
        refine ⟨135054620482723768539227353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180072827310298358052303137 135054620482723768539227353)
        ·
          refine ⟨101290965362042826404420515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135054620482723768539227353 101290965362042826404420515)
          ·
            refine ⟨151936448043064239606630773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101290965362042826404420515 151936448043064239606630773)
            ·
              refine ⟨14244042004037272463121635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151936448043064239606630773 14244042004037272463121635)
              ·
                refine ⟨21366063006055908694682453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14244042004037272463121635 21366063006055908694682453)
                ·
                  refine ⟨125191775426108840007905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21366063006055908694682453 125191775426108840007905)
                  ·
                    rfl

theorem cell23_2194291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 9].length) (baseStart_2194291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194291 prefixEnd_2194291 := by exact prefixLift 2194291
  have htrace : WordTrace (prefixWord ++ tailWord_2194291) baseStart_2194291 baseEnd_2194291 := by
    simpa [prefixWord, tailWord_2194291, baseEnd_2194291] using wordTrace_append hprefix tailTrace_2194291
  have hstable : (prefixWord ++ tailWord_2194291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194291).length < 2 ^ (prefixWord ++ tailWord_2194291).sum := by decide
  have hdescent : baseEnd_2194291 < baseStart_2194291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194325 : List Nat := [1, 3, 2, 1, 1, 4, 2, 4, 5]
def baseStart_2194325 : Nat := 118140960795 + 2194325 * 2 ^ 59
def prefixEnd_2194325 : Nat := 4983230072969 + 3 ^ 40 * 2194325 * 2
def baseEnd_2194325 : Nat := 125193715241914714116221

theorem tailTrace_2194325 : CollatzResearch.WordTrace tailWord_2194325 prefixEnd_2194325 125193715241914714116221 := by
  unfold tailWord_2194325
  simp only [CollatzResearch.WordTrace]
  refine ⟨80033607775342760718872429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53355738516895173812581619 80033607775342760718872429)
  ·
    refine ⟨30012602915753535269577161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80033607775342760718872429 30012602915753535269577161)
    ·
      refine ⟨22509452186815151452182871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30012602915753535269577161 22509452186815151452182871)
      ·
        refine ⟨33764178280222727178274307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22509452186815151452182871 33764178280222727178274307)
        ·
          refine ⟨50646267420334090767411461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33764178280222727178274307 50646267420334090767411461)
          ·
            refine ⟨9496175141312642018889649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50646267420334090767411461 9496175141312642018889649)
            ·
              refine ⟨7122131355984481514167237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9496175141312642018889649 7122131355984481514167237)
              ·
                refine ⟨1335399629247090283906357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7122131355984481514167237 1335399629247090283906357)
                ·
                  refine ⟨125193715241914714116221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1335399629247090283906357 125193715241914714116221)
                  ·
                    rfl

theorem cell23_2194325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_2194325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194325 prefixEnd_2194325 := by exact prefixLift 2194325
  have htrace : WordTrace (prefixWord ++ tailWord_2194325) baseStart_2194325 baseEnd_2194325 := by
    simpa [prefixWord, tailWord_2194325, baseEnd_2194325] using wordTrace_append hprefix tailTrace_2194325
  have hstable : (prefixWord ++ tailWord_2194325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194325).length < 2 ^ (prefixWord ++ tailWord_2194325).sum := by decide
  have hdescent : baseEnd_2194325 < baseStart_2194325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194335 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2194335 : Nat := 118140960795 + 2194335 * 2 ^ 59
def prefixEnd_2194335 : Nat := 4983230072969 + 3 ^ 40 * 2194335 * 2
def baseEnd_2194335 : Nat := 1126748571983777387920943

theorem tailTrace_2194335 : CollatzResearch.WordTrace tailWord_2194335 prefixEnd_2194335 1126748571983777387920943 := by
  unfold tailWord_2194335
  simp only [CollatzResearch.WordTrace]
  refine ⟨80033972505306532426736459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53355981670204354951157639 80033972505306532426736459)
  ·
    refine ⟨120050958757959798640104689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80033972505306532426736459 120050958757959798640104689)
    ·
      refine ⟨90038219068469848980078517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120050958757959798640104689 90038219068469848980078517)
      ·
        refine ⟨8441083037669048341882361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90038219068469848980078517 8441083037669048341882361)
        ·
          refine ⟨6330812278251786256411771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8441083037669048341882361 6330812278251786256411771)
          ·
            refine ⟨9496218417377679384617657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6330812278251786256411771 9496218417377679384617657)
            ·
              refine ⟨7122163813033259538463243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9496218417377679384617657 7122163813033259538463243)
              ·
                refine ⟨10683245719549889307694865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122163813033259538463243 10683245719549889307694865)
                ·
                  refine ⟨8012434289662416980771149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10683245719549889307694865 8012434289662416980771149)
                  ·
                    refine ⟨3004662858623406367789181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8012434289662416980771149 3004662858623406367789181)
                    ·
                      refine ⟨1126748571983777387920943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3004662858623406367789181 1126748571983777387920943)
                      ·
                        rfl

theorem cell23_2194335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2194335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194335 prefixEnd_2194335 := by exact prefixLift 2194335
  have htrace : WordTrace (prefixWord ++ tailWord_2194335) baseStart_2194335 baseEnd_2194335 := by
    simpa [prefixWord, tailWord_2194335, baseEnd_2194335] using wordTrace_append hprefix tailTrace_2194335
  have hstable : (prefixWord ++ tailWord_2194335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194335).length < 2 ^ (prefixWord ++ tailWord_2194335).sum := by decide
  have hdescent : baseEnd_2194335 < baseStart_2194335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194375 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 4, 4, 2]
def baseStart_2194375 : Nat := 118140960795 + 2194375 * 2 ^ 59
def prefixEnd_2194375 : Nat := 4983230072969 + 3 ^ 40 * 2194375 * 2
def baseEnd_2194375 : Nat := 1126769111209957231420759

theorem tailTrace_2194375 : CollatzResearch.WordTrace tailWord_2194375 prefixEnd_2194375 1126769111209957231420759 := by
  unfold tailWord_2194375
  simp only [CollatzResearch.WordTrace]
  refine ⟨80035431425161619258192579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53356954283441079505461719 80035431425161619258192579)
  ·
    refine ⟨120053147137742428887288869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80035431425161619258192579 120053147137742428887288869)
    ·
      refine ⟨22509965088326705416366663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120053147137742428887288869 22509965088326705416366663)
      ·
        refine ⟨33764947632490058124549995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22509965088326705416366663 33764947632490058124549995)
        ·
          refine ⟨50647421448735087186824993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33764947632490058124549995 50647421448735087186824993)
          ·
            refine ⟨37985566086551315390118745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50647421448735087186824993 37985566086551315390118745)
            ·
              refine ⟨28489174564913486542589059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37985566086551315390118745 28489174564913486542589059)
              ·
                refine ⟨42733761847370229813883589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28489174564913486542589059 42733761847370229813883589)
                ·
                  refine ⟨8012580346381918090103173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42733761847370229813883589 8012580346381918090103173)
                  ·
                    refine ⟨1502358814946609641894345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8012580346381918090103173 1502358814946609641894345)
                    ·
                      refine ⟨1126769111209957231420759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502358814946609641894345 1126769111209957231420759)
                      ·
                        rfl

theorem cell23_2194375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_2194375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194375 prefixEnd_2194375 := by exact prefixLift 2194375
  have htrace : WordTrace (prefixWord ++ tailWord_2194375) baseStart_2194375 baseEnd_2194375 := by
    simpa [prefixWord, tailWord_2194375, baseEnd_2194375] using wordTrace_append hprefix tailTrace_2194375
  have hstable : (prefixWord ++ tailWord_2194375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194375).length < 2 ^ (prefixWord ++ tailWord_2194375).sum := by decide
  have hdescent : baseEnd_2194375 < baseStart_2194375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194435 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 5, 5, 2]
def baseStart_2194435 : Nat := 118140960795 + 2194435 * 2 ^ 59
def prefixEnd_2194435 : Nat := 4983230072969 + 3 ^ 40 * 2194435 * 2
def baseEnd_2194435 : Nat := 1126799920049226996670483

theorem tailTrace_2194435 : CollatzResearch.WordTrace tailWord_2194435 prefixEnd_2194435 1126799920049226996670483 := by
  unfold tailWord_2194435
  simp only [CollatzResearch.WordTrace]
  refine ⟨80037619804944249505376759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53358413203296166336917839 80037619804944249505376759)
  ·
    refine ⟨120056429707416374258065139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80037619804944249505376759 120056429707416374258065139)
    ·
      refine ⟨180084644561124561387097709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120056429707416374258065139 180084644561124561387097709)
      ·
        refine ⟨67531741710421710520161641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180084644561124561387097709 67531741710421710520161641)
        ·
          refine ⟨50648806282816282890121231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67531741710421710520161641 50648806282816282890121231)
          ·
            refine ⟨75973209424224424335181847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50648806282816282890121231 75973209424224424335181847)
            ·
              refine ⟨113959814136336636502772771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75973209424224424335181847 113959814136336636502772771)
              ·
                refine ⟨170939721204504954754159157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113959814136336636502772771 170939721204504954754159157)
                ·
                  refine ⟨16025598862922339508202421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170939721204504954754159157 16025598862922339508202421)
                  ·
                    refine ⟨1502399893398969328893977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16025598862922339508202421 1502399893398969328893977)
                    ·
                      refine ⟨1126799920049226996670483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502399893398969328893977 1126799920049226996670483)
                      ·
                        rfl

theorem cell23_2194435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 5, 2].length) (baseStart_2194435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194435 prefixEnd_2194435 := by exact prefixLift 2194435
  have htrace : WordTrace (prefixWord ++ tailWord_2194435) baseStart_2194435 baseEnd_2194435 := by
    simpa [prefixWord, tailWord_2194435, baseEnd_2194435] using wordTrace_append hprefix tailTrace_2194435
  have hstable : (prefixWord ++ tailWord_2194435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194435).length < 2 ^ (prefixWord ++ tailWord_2194435).sum := by decide
  have hdescent : baseEnd_2194435 < baseStart_2194435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194448 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4]
def baseStart_2194448 : Nat := 118140960795 + 2194448 * 2 ^ 59
def prefixEnd_2194448 : Nat := 4983230072969 + 3 ^ 40 * 2194448 * 2
def baseEnd_2194448 : Nat := 1126806595297735445807923

theorem tailTrace_2194448 : CollatzResearch.WordTrace tailWord_2194448 prefixEnd_2194448 1126806595297735445807923 := by
  unfold tailWord_2194448
  simp only [CollatzResearch.WordTrace]
  refine ⟨40019046976948576362799999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53358729302598101817066665 40019046976948576362799999)
  ·
    refine ⟨60028570465422864544199999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40019046976948576362799999 60028570465422864544199999)
    ·
      refine ⟨90042855698134296816299999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60028570465422864544199999 90042855698134296816299999)
      ·
        refine ⟨135064283547201445224449999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90042855698134296816299999 135064283547201445224449999)
        ·
          refine ⟨202596425320802167836674999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135064283547201445224449999 202596425320802167836674999)
          ·
            refine ⟨303894637981203251755012499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202596425320802167836674999 303894637981203251755012499)
            ·
              refine ⟨455841956971804877632518749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303894637981203251755012499 455841956971804877632518749)
              ·
                refine ⟨170940733864426829112194531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455841956971804877632518749 170940733864426829112194531)
                ·
                  refine ⟨256411100796640243668291797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170940733864426829112194531 256411100796640243668291797)
                  ·
                    refine ⟨6009635174921255710975589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 256411100796640243668291797 6009635174921255710975589)
                    ·
                      refine ⟨1126806595297735445807923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6009635174921255710975589 1126806595297735445807923)
                      ·
                        rfl

theorem cell23_2194448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_2194448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194448 prefixEnd_2194448 := by exact prefixLift 2194448
  have htrace : WordTrace (prefixWord ++ tailWord_2194448) baseStart_2194448 baseEnd_2194448 := by
    simpa [prefixWord, tailWord_2194448, baseEnd_2194448] using wordTrace_append hprefix tailTrace_2194448
  have hstable : (prefixWord ++ tailWord_2194448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194448).length < 2 ^ (prefixWord ++ tailWord_2194448).sum := by decide
  have hdescent : baseEnd_2194448 < baseStart_2194448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194475 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 4, 4]
def baseStart_2194475 : Nat := 118140960795 + 2194475 * 2 ^ 59
def prefixEnd_2194475 : Nat := 4983230072969 + 3 ^ 40 * 2194475 * 2
def baseEnd_2194475 : Nat := 375606819758468946723433

theorem tailTrace_2194475 : CollatzResearch.WordTrace tailWord_2194475 prefixEnd_2194475 375606819758468946723433 := by
  unfold tailWord_2194475
  simp only [CollatzResearch.WordTrace]
  refine ⟨80039078724799336336832879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53359385816532890891221919 80039078724799336336832879)
  ·
    refine ⟨120058618087199004505249319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80039078724799336336832879 120058618087199004505249319)
    ·
      refine ⟨180087927130798506757873979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120058618087199004505249319 180087927130798506757873979)
      ·
        refine ⟨270131890696197760136810969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180087927130798506757873979 270131890696197760136810969)
        ·
          refine ⟨202598918022148320102608227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270131890696197760136810969 202598918022148320102608227)
          ·
            refine ⟨303898377033222480153912341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202598918022148320102608227 303898377033222480153912341)
            ·
              refine ⟨14245236423432303757214641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 303898377033222480153912341 14245236423432303757214641)
              ·
                refine ⟨10683927317574227817910981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14245236423432303757214641 10683927317574227817910981)
                ·
                  refine ⟨2003236372045167715858309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10683927317574227817910981 2003236372045167715858309)
                  ·
                    refine ⟨375606819758468946723433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003236372045167715858309 375606819758468946723433)
                    ·
                      rfl

theorem cell23_2194475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 4].length) (baseStart_2194475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194475 prefixEnd_2194475 := by exact prefixLift 2194475
  have htrace : WordTrace (prefixWord ++ tailWord_2194475) baseStart_2194475 baseEnd_2194475 := by
    simpa [prefixWord, tailWord_2194475, baseEnd_2194475] using wordTrace_append hprefix tailTrace_2194475
  have hstable : (prefixWord ++ tailWord_2194475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194475).length < 2 ^ (prefixWord ++ tailWord_2194475).sum := by decide
  have hdescent : baseEnd_2194475 < baseStart_2194475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194482 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_2194482 : Nat := 118140960795 + 2194482 * 2 ^ 59
def prefixEnd_2194482 : Nat := 4983230072969 + 3 ^ 40 * 2194482 * 2
def baseEnd_2194482 : Nat := 1126824053639988312782767

theorem tailTrace_2194482 : CollatzResearch.WordTrace tailWord_2194482 prefixEnd_2194482 1126824053639988312782767 := by
  unfold tailWord_2194482
  simp only [CollatzResearch.WordTrace]
  refine ⟨20009833508943494133084425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53359556023849317688225133 20009833508943494133084425)
  ·
    refine ⟨15007375131707620599813319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20009833508943494133084425 15007375131707620599813319)
    ·
      refine ⟨22511062697561430899719979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15007375131707620599813319 22511062697561430899719979)
      ·
        refine ⟨33766594046342146349579969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22511062697561430899719979 33766594046342146349579969)
        ·
          refine ⟨25324945534756609762184977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33766594046342146349579969 25324945534756609762184977)
          ·
            refine ⟨18993709151067457321638733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25324945534756609762184977 18993709151067457321638733)
            ·
              refine ⟨7122640931650296495614525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18993709151067457321638733 7122640931650296495614525)
              ·
                refine ⟨2670990349368861185855447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7122640931650296495614525 2670990349368861185855447)
                ·
                  refine ⟨4006485524053291778783171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2670990349368861185855447 4006485524053291778783171)
                  ·
                    refine ⟨6009728286079937668174757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4006485524053291778783171 6009728286079937668174757)
                    ·
                      refine ⟨1126824053639988312782767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6009728286079937668174757 1126824053639988312782767)
                      ·
                        rfl

theorem cell23_2194482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_2194482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194482 prefixEnd_2194482 := by exact prefixLift 2194482
  have htrace : WordTrace (prefixWord ++ tailWord_2194482) baseStart_2194482 baseEnd_2194482 := by
    simpa [prefixWord, tailWord_2194482, baseEnd_2194482] using wordTrace_append hprefix tailTrace_2194482
  have hstable : (prefixWord ++ tailWord_2194482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194482).length < 2 ^ (prefixWord ++ tailWord_2194482).sum := by decide
  have hdescent : baseEnd_2194482 < baseStart_2194482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194485 : List Nat := [1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2194485 : Nat := 118140960795 + 2194485 * 2 ^ 59
def prefixEnd_2194485 : Nat := 4983230072969 + 3 ^ 40 * 2194485 * 2
def baseEnd_2194485 : Nat := 1126825594081951801045253

theorem tailTrace_2194485 : CollatzResearch.WordTrace tailWord_2194485 prefixEnd_2194485 1126825594081951801045253 := by
  unfold tailWord_2194485
  simp only [CollatzResearch.WordTrace]
  refine ⟨80039443454763108044696909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53359628969842072029797939 80039443454763108044696909)
  ·
    refine ⟨30014791295536165516761341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80039443454763108044696909 30014791295536165516761341)
    ·
      refine ⟨11255546735826062068785503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30014791295536165516761341 11255546735826062068785503)
      ·
        refine ⟨16883320103739093103178255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11255546735826062068785503 16883320103739093103178255)
        ·
          refine ⟨25324980155608639654767383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16883320103739093103178255 25324980155608639654767383)
          ·
            refine ⟨37987470233412959482151075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25324980155608639654767383 37987470233412959482151075)
            ·
              refine ⟨56981205350119439223226613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37987470233412959482151075 56981205350119439223226613)
              ·
                refine ⟨5341988001573697427177495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56981205350119439223226613 5341988001573697427177495)
                ·
                  refine ⟨8012982002360546140766243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5341988001573697427177495 8012982002360546140766243)
                  ·
                    refine ⟨12019473003540819211149365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8012982002360546140766243 12019473003540819211149365)
                    ·
                      refine ⟨1126825594081951801045253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12019473003540819211149365 1126825594081951801045253)
                      ·
                        rfl

theorem cell23_2194485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2194485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194485 prefixEnd_2194485 := by exact prefixLift 2194485
  have htrace : WordTrace (prefixWord ++ tailWord_2194485) baseStart_2194485 baseEnd_2194485 := by
    simpa [prefixWord, tailWord_2194485, baseEnd_2194485] using wordTrace_append hprefix tailTrace_2194485
  have hstable : (prefixWord ++ tailWord_2194485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194485).length < 2 ^ (prefixWord ++ tailWord_2194485).sum := by decide
  have hdescent : baseEnd_2194485 < baseStart_2194485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194492 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 4, 4]
def baseStart_2194492 : Nat := 118140960795 + 2194492 * 2 ^ 59
def prefixEnd_2194492 : Nat := 4983230072969 + 3 ^ 40 * 2194492 * 2
def baseEnd_2194492 : Nat := 375609729482177757885907

theorem tailTrace_2194492 : CollatzResearch.WordTrace tailWord_2194492 prefixEnd_2194492 375609729482177757885907 := by
  unfold tailWord_2194492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40019849382868874120100865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53359799177158498826801153 40019849382868874120100865)
  ·
    refine ⟨30014887037151655590075649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40019849382868874120100865 30014887037151655590075649)
    ·
      refine ⟨22511165277863741692556737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30014887037151655590075649 22511165277863741692556737)
      ·
        refine ⟨16883373958397806269417553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22511165277863741692556737 16883373958397806269417553)
        ·
          refine ⟨12662530468798354702063165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16883373958397806269417553 12662530468798354702063165)
          ·
            refine ⟨4748448925799383013273687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12662530468798354702063165 4748448925799383013273687)
            ·
              refine ⟨7122673388699074519910531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4748448925799383013273687 7122673388699074519910531)
              ·
                refine ⟨10684010083048611779865797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7122673388699074519910531 10684010083048611779865797)
                ·
                  refine ⟨2003251890571614708724837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10684010083048611779865797 2003251890571614708724837)
                  ·
                    refine ⟨375609729482177757885907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003251890571614708724837 375609729482177757885907)
                    ·
                      rfl

theorem cell23_2194492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_2194492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194492 prefixEnd_2194492 := by exact prefixLift 2194492
  have htrace : WordTrace (prefixWord ++ tailWord_2194492) baseStart_2194492 baseEnd_2194492 := by
    simpa [prefixWord, tailWord_2194492, baseEnd_2194492] using wordTrace_append hprefix tailTrace_2194492
  have hstable : (prefixWord ++ tailWord_2194492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194492).length < 2 ^ (prefixWord ++ tailWord_2194492).sum := by decide
  have hdescent : baseEnd_2194492 < baseStart_2194492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194499 : List Nat := [1, 1, 1, 3, 1, 2, 6, 1, 3, 2, 2]
def baseStart_2194499 : Nat := 118140960795 + 2194499 * 2 ^ 59
def prefixEnd_2194499 : Nat := 4983230072969 + 3 ^ 40 * 2194499 * 2
def baseEnd_2194499 : Nat := 1126832782811114746270189

theorem tailTrace_2194499 : CollatzResearch.WordTrace tailWord_2194499 prefixEnd_2194499 1126832782811114746270189 := by
  unfold tailWord_2194499
  simp only [CollatzResearch.WordTrace]
  refine ⟨80039954076712388435706551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53359969384474925623804367 80039954076712388435706551)
  ·
    refine ⟨120059931115068582653559827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80039954076712388435706551 120059931115068582653559827)
    ·
      refine ⟨180089896672602873980339741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120059931115068582653559827 180089896672602873980339741)
      ·
        refine ⟨67533711252226077742627403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180089896672602873980339741 67533711252226077742627403)
        ·
          refine ⟨101300566878339116613941105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67533711252226077742627403 101300566878339116613941105)
          ·
            refine ⟨75975425158754337460455829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101300566878339116613941105 75975425158754337460455829)
            ·
              refine ⟨3561348054316609568458867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75975425158754337460455829 3561348054316609568458867)
              ·
                refine ⟨5342022081474914352688301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561348054316609568458867 5342022081474914352688301)
                ·
                  refine ⟨2003258280553092882258113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5342022081474914352688301 2003258280553092882258113)
                  ·
                    refine ⟨1502443710414819661693585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003258280553092882258113 1502443710414819661693585)
                    ·
                      refine ⟨1126832782811114746270189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502443710414819661693585 1126832782811114746270189)
                      ·
                        rfl

theorem cell23_2194499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 1, 3, 2, 2].length) (baseStart_2194499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194499 prefixEnd_2194499 := by exact prefixLift 2194499
  have htrace : WordTrace (prefixWord ++ tailWord_2194499) baseStart_2194499 baseEnd_2194499 := by
    simpa [prefixWord, tailWord_2194499, baseEnd_2194499] using wordTrace_append hprefix tailTrace_2194499
  have hstable : (prefixWord ++ tailWord_2194499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194499).length < 2 ^ (prefixWord ++ tailWord_2194499).sum := by decide
  have hdescent : baseEnd_2194499 < baseStart_2194499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194509 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2194509 : Nat := 118140960795 + 2194509 * 2 ^ 59
def prefixEnd_2194509 : Nat := 4983230072969 + 3 ^ 40 * 2194509 * 2
def baseEnd_2194509 : Nat := 375612639205886569048381

theorem tailTrace_2194509 : CollatzResearch.WordTrace tailWord_2194509 prefixEnd_2194509 375612639205886569048381 := by
  unfold tailWord_2194509
  simp only [CollatzResearch.WordTrace]
  refine ⟨80040318806676160143570581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53360212537784106762380387 80040318806676160143570581)
  ·
    refine ⟨3751889944062945006729871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 80040318806676160143570581 3751889944062945006729871)
    ·
      refine ⟨5627834916094417510094807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3751889944062945006729871 5627834916094417510094807)
      ·
        refine ⟨8441752374141626265142211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5627834916094417510094807 8441752374141626265142211)
        ·
          refine ⟨12662628561212439397713317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8441752374141626265142211 12662628561212439397713317)
          ·
            refine ⟨2374242855227332387071247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12662628561212439397713317 2374242855227332387071247)
            ·
              refine ⟨3561364282840998580606871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374242855227332387071247 3561364282840998580606871)
              ·
                refine ⟨5342046424261497870910307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561364282840998580606871 5342046424261497870910307)
                ·
                  refine ⟨8013069636392246806365461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5342046424261497870910307 8013069636392246806365461)
                  ·
                    refine ⟨375612639205886569048381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8013069636392246806365461 375612639205886569048381)
                    ·
                      rfl

theorem cell23_2194509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2194509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194509 prefixEnd_2194509 := by exact prefixLift 2194509
  have htrace : WordTrace (prefixWord ++ tailWord_2194509) baseStart_2194509 baseEnd_2194509 := by
    simpa [prefixWord, tailWord_2194509, baseEnd_2194509] using wordTrace_append hprefix tailTrace_2194509
  have hstable : (prefixWord ++ tailWord_2194509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194509).length < 2 ^ (prefixWord ++ tailWord_2194509).sum := by decide
  have hdescent : baseEnd_2194509 < baseStart_2194509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194526 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_2194526 : Nat := 118140960795 + 2194526 * 2 ^ 59
def prefixEnd_2194526 : Nat := 4983230072969 + 3 ^ 40 * 2194526 * 2
def baseEnd_2194526 : Nat := 375615548929595380210855

theorem tailTrace_2194526 : CollatzResearch.WordTrace tailWord_2194526 prefixEnd_2194526 375615548929595380210855 := by
  unfold tailWord_2194526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005117355951821505867429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53360625898409714697959621 10005117355951821505867429)
  ·
    refine ⟨1875959504240966532350143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10005117355951821505867429 1875959504240966532350143)
    ·
      refine ⟨2813939256361449798525215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1875959504240966532350143 2813939256361449798525215)
      ·
        refine ⟨4220908884542174697787823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2813939256361449798525215 4220908884542174697787823)
        ·
          refine ⟨6331363326813262046681735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4220908884542174697787823 6331363326813262046681735)
          ·
            refine ⟨9497044990219893070022603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6331363326813262046681735 9497044990219893070022603)
            ·
              refine ⟨14245567485329839605033905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9497044990219893070022603 14245567485329839605033905)
              ·
                refine ⟨10684175613997379703775429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14245567485329839605033905 10684175613997379703775429)
                ·
                  refine ⟨2003282927624508694457893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10684175613997379703775429 2003282927624508694457893)
                  ·
                    refine ⟨375615548929595380210855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003282927624508694457893 375615548929595380210855)
                    ·
                      rfl

theorem cell23_2194526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_2194526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194526 prefixEnd_2194526 := by exact prefixLift 2194526
  have htrace : WordTrace (prefixWord ++ tailWord_2194526) baseStart_2194526 baseEnd_2194526 := by
    simpa [prefixWord, tailWord_2194526, baseEnd_2194526] using wordTrace_append hprefix tailTrace_2194526
  have hstable : (prefixWord ++ tailWord_2194526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194526).length < 2 ^ (prefixWord ++ tailWord_2194526).sum := by decide
  have hdescent : baseEnd_2194526 < baseStart_2194526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194550 : List Nat := [5, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2]
def baseStart_2194550 : Nat := 118140960795 + 2194550 * 2 ^ 59
def prefixEnd_2194550 : Nat := 4983230072969 + 3 ^ 40 * 2194550 * 2
def baseEnd_2194550 : Nat := 1126858970324494046732455

theorem tailTrace_2194550 : CollatzResearch.WordTrace tailWord_2194550 prefixEnd_2194550 1126858970324494046732455 := by
  unfold tailWord_2194550
  simp only [CollatzResearch.WordTrace]
  refine ⟨5002613387470476509113319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53361209466351749430542069 5002613387470476509113319)
  ·
    refine ⟨7503920081205714763669979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5002613387470476509113319 7503920081205714763669979)
    ·
      refine ⟨11255880121808572145504969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7503920081205714763669979 11255880121808572145504969)
      ·
        refine ⟨8441910091356429109128727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11255880121808572145504969 8441910091356429109128727)
        ·
          refine ⟨12662865137034643663693091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8441910091356429109128727 12662865137034643663693091)
          ·
            refine ⟨18994297705551965495539637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12662865137034643663693091 18994297705551965495539637)
            ·
              refine ⟨1780715409895496765206841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18994297705551965495539637 1780715409895496765206841)
              ·
                refine ⟨1335536557421622573905131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780715409895496765206841 1335536557421622573905131)
                ·
                  refine ⟨2003304836132433860857697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335536557421622573905131 2003304836132433860857697)
                  ·
                    refine ⟨1502478627099325395643273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003304836132433860857697 1502478627099325395643273)
                    ·
                      refine ⟨1126858970324494046732455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502478627099325395643273 1126858970324494046732455)
                      ·
                        rfl

theorem cell23_2194550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_2194550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194550 prefixEnd_2194550 := by exact prefixLift 2194550
  have htrace : WordTrace (prefixWord ++ tailWord_2194550) baseStart_2194550 baseEnd_2194550 := by
    simpa [prefixWord, tailWord_2194550, baseEnd_2194550] using wordTrace_append hprefix tailTrace_2194550
  have hstable : (prefixWord ++ tailWord_2194550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194550).length < 2 ^ (prefixWord ++ tailWord_2194550).sum := by decide
  have hdescent : baseEnd_2194550 < baseStart_2194550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194572 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 5, 4, 2]
def baseStart_2194572 : Nat := 118140960795 + 2194572 * 2 ^ 59
def prefixEnd_2194572 : Nat := 4983230072969 + 3 ^ 40 * 2194572 * 2
def baseEnd_2194572 : Nat := 1126870266898892960657353

theorem tailTrace_2194572 : CollatzResearch.WordTrace tailWord_2194572 prefixEnd_2194572 1126870266898892960657353 := by
  unfold tailWord_2194572
  simp only [CollatzResearch.WordTrace]
  refine ⟨40021308302723960951556985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53361744403631947935409313 40021308302723960951556985)
  ·
    refine ⟨30015981227042970713667739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40021308302723960951556985 30015981227042970713667739)
    ·
      refine ⟨45023971840564456070501609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30015981227042970713667739 45023971840564456070501609)
      ·
        refine ⟨33767978880423342052876207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45023971840564456070501609 33767978880423342052876207)
        ·
          refine ⟨50651968320635013079314311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33767978880423342052876207 50651968320635013079314311)
          ·
            refine ⟨75977952480952519618971467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50651968320635013079314311 75977952480952519618971467)
            ·
              refine ⟨113966928721428779428457201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75977952480952519618971467 113966928721428779428457201)
              ·
                refine ⟨85475196541071584571342901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113966928721428779428457201 85475196541071584571342901)
                ·
                  refine ⟨8013299675725461053563397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85475196541071584571342901 8013299675725461053563397)
                  ·
                    refine ⟨1502493689198523947543137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8013299675725461053563397 1502493689198523947543137)
                    ·
                      refine ⟨1126870266898892960657353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502493689198523947543137 1126870266898892960657353)
                      ·
                        rfl

theorem cell23_2194572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_2194572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194572 prefixEnd_2194572 := by exact prefixLift 2194572
  have htrace : WordTrace (prefixWord ++ tailWord_2194572) baseStart_2194572 baseEnd_2194572 := by
    simpa [prefixWord, tailWord_2194572, baseEnd_2194572] using wordTrace_append hprefix tailTrace_2194572
  have hstable : (prefixWord ++ tailWord_2194572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194572).length < 2 ^ (prefixWord ++ tailWord_2194572).sum := by decide
  have hdescent : baseEnd_2194572 < baseStart_2194572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194585 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 4]
def baseStart_2194585 : Nat := 118140960795 + 2194585 * 2 ^ 59
def prefixEnd_2194585 : Nat := 4983230072969 + 3 ^ 40 * 2194585 * 2
def baseEnd_2194585 : Nat := 1126876942147401409794793

theorem tailTrace_2194585 : CollatzResearch.WordTrace tailWord_2194585 prefixEnd_2194585 1126876942147401409794793 := by
  unfold tailWord_2194585
  simp only [CollatzResearch.WordTrace]
  refine ⟨80043090754400825123337209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53362060502933883415558139 80043090754400825123337209)
  ·
    refine ⟨60032318065800618842502907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80043090754400825123337209 60032318065800618842502907)
    ·
      refine ⟨90048477098700928263754361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60032318065800618842502907 90048477098700928263754361)
      ·
        refine ⟨67536357824025696197815771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90048477098700928263754361 67536357824025696197815771)
        ·
          refine ⟨101304536736038544296723657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67536357824025696197815771 101304536736038544296723657)
          ·
            refine ⟨75978402552028908222542743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101304536736038544296723657 75978402552028908222542743)
            ·
              refine ⟨113967603828043362333814115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75978402552028908222542743 113967603828043362333814115)
              ·
                refine ⟨170951405742065043500721173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113967603828043362333814115 170951405742065043500721173)
                ·
                  refine ⟨8013347144159298914096305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170951405742065043500721173 8013347144159298914096305)
                  ·
                    refine ⟨6010010358119474185572229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8013347144159298914096305 6010010358119474185572229)
                    ·
                      refine ⟨1126876942147401409794793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6010010358119474185572229 1126876942147401409794793)
                      ·
                        rfl

theorem cell23_2194585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_2194585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194585 prefixEnd_2194585 := by exact prefixLift 2194585
  have htrace : WordTrace (prefixWord ++ tailWord_2194585) baseStart_2194585 baseEnd_2194585 := by
    simpa [prefixWord, tailWord_2194585, baseEnd_2194585] using wordTrace_append hprefix tailTrace_2194585
  have hstable : (prefixWord ++ tailWord_2194585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194585).length < 2 ^ (prefixWord ++ tailWord_2194585).sum := by decide
  have hdescent : baseEnd_2194585 < baseStart_2194585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194589 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_2194589 : Nat := 118140960795 + 2194589 * 2 ^ 59
def prefixEnd_2194589 : Nat := 4983230072969 + 3 ^ 40 * 2194589 * 2
def baseEnd_2194589 : Nat := 1126878996070019394144775

theorem tailTrace_2194589 : CollatzResearch.WordTrace tailWord_2194589 prefixEnd_2194589 1126878996070019394144775 := by
  unfold tailWord_2194589
  simp only [CollatzResearch.WordTrace]
  refine ⟨80043236646386333806482821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53362157764257555870988547 80043236646386333806482821)
  ·
    refine ⟨15008106871197437588715529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80043236646386333806482821 15008106871197437588715529)
    ·
      refine ⟨11256080153398078191536647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15008106871197437588715529 11256080153398078191536647)
      ·
        refine ⟨16884120230097117287304971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11256080153398078191536647 16884120230097117287304971)
        ·
          refine ⟨25326180345145675930957457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16884120230097117287304971 25326180345145675930957457)
          ·
            refine ⟨18994635258859256948218093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25326180345145675930957457 18994635258859256948218093)
            ·
              refine ⟨7122988222072221355581785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18994635258859256948218093 7122988222072221355581785)
              ·
                refine ⟨5342241166554166016686339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7122988222072221355581785 5342241166554166016686339)
                ·
                  refine ⟨8013361749831249025029509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5342241166554166016686339 8013361749831249025029509)
                  ·
                    refine ⟨1502505328093359192193033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8013361749831249025029509 1502505328093359192193033)
                    ·
                      refine ⟨1126878996070019394144775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502505328093359192193033 1126878996070019394144775)
                      ·
                        rfl

theorem cell23_2194589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_2194589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194589 prefixEnd_2194589 := by exact prefixLift 2194589
  have htrace : WordTrace (prefixWord ++ tailWord_2194589) baseStart_2194589 baseEnd_2194589 := by
    simpa [prefixWord, tailWord_2194589, baseEnd_2194589] using wordTrace_append hprefix tailTrace_2194589
  have hstable : (prefixWord ++ tailWord_2194589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194589).length < 2 ^ (prefixWord ++ tailWord_2194589).sum := by decide
  have hdescent : baseEnd_2194589 < baseStart_2194589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194635 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5]
def baseStart_2194635 : Nat := 118140960795 + 2194635 * 2 ^ 59
def prefixEnd_2194635 : Nat := 4983230072969 + 3 ^ 40 * 2194635 * 2
def baseEnd_2194635 : Nat := 1126902616180126214169563

theorem tailTrace_2194635 : CollatzResearch.WordTrace tailWord_2194635 prefixEnd_2194635 1126902616180126214169563 := by
  unfold tailWord_2194635
  simp only [CollatzResearch.WordTrace]
  refine ⟨80044914404219683662657359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53363276269479789108438239 80044914404219683662657359)
  ·
    refine ⟨120067371606329525493986039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80044914404219683662657359 120067371606329525493986039)
    ·
      refine ⟨180101057409494288240979059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120067371606329525493986039 180101057409494288240979059)
      ·
        refine ⟨270151586114241432361468589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180101057409494288240979059 270151586114241432361468589)
        ·
          refine ⟨101306844792840537135550721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270151586114241432361468589 101306844792840537135550721)
          ·
            refine ⟨75980133594630402851663041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101306844792840537135550721 75980133594630402851663041)
            ·
              refine ⟨56985100195972802138747281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75980133594630402851663041 56985100195972802138747281)
              ·
                refine ⟨42738825146979601604060461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56985100195972802138747281 42738825146979601604060461)
                ·
                  refine ⟨16027059430117350601522673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42738825146979601604060461 16027059430117350601522673)
                  ·
                    refine ⟨12020294572588012951142005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16027059430117350601522673 12020294572588012951142005)
                    ·
                      refine ⟨1126902616180126214169563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12020294572588012951142005 1126902616180126214169563)
                      ·
                        rfl

theorem cell23_2194635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 5].length) (baseStart_2194635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194635 prefixEnd_2194635 := by exact prefixLift 2194635
  have htrace : WordTrace (prefixWord ++ tailWord_2194635) baseStart_2194635 baseEnd_2194635 := by
    simpa [prefixWord, tailWord_2194635, baseEnd_2194635] using wordTrace_append hprefix tailTrace_2194635
  have hstable : (prefixWord ++ tailWord_2194635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194635).length < 2 ^ (prefixWord ++ tailWord_2194635).sum := by decide
  have hdescent : baseEnd_2194635 < baseStart_2194635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194642 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_2194642 : Nat := 118140960795 + 2194642 * 2 ^ 59
def prefixEnd_2194642 : Nat := 4983230072969 + 3 ^ 40 * 2194642 * 2
def baseEnd_2194642 : Nat := 375635403514902562260677

theorem tailTrace_2194642 : CollatzResearch.WordTrace tailWord_2194642 prefixEnd_2194642 375635403514902562260677 := by
  unfold tailWord_2194642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20011292428798580964540545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53363446476796215905441453 20011292428798580964540545)
  ·
    refine ⟨15008469321598935723405409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20011292428798580964540545 15008469321598935723405409)
    ·
      refine ⟨11256351991199201792554057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15008469321598935723405409 11256351991199201792554057)
      ·
        refine ⟨8442263993399401344415543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11256351991199201792554057 8442263993399401344415543)
        ·
          refine ⟨12663395990099102016623315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8442263993399401344415543 12663395990099102016623315)
          ·
            refine ⟨18995093985148653024934973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12663395990099102016623315 18995093985148653024934973)
            ·
              refine ⟨7123160244430744884350615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18995093985148653024934973 7123160244430744884350615)
              ·
                refine ⟨10684740366646117326525923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7123160244430744884350615 10684740366646117326525923)
                ·
                  refine ⟨16027110549969175989788885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10684740366646117326525923 16027110549969175989788885)
                  ·
                    refine ⟨375635403514902562260677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16027110549969175989788885 375635403514902562260677)
                    ·
                      rfl

theorem cell23_2194642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_2194642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194642 prefixEnd_2194642 := by exact prefixLift 2194642
  have htrace : WordTrace (prefixWord ++ tailWord_2194642) baseStart_2194642 baseEnd_2194642 := by
    simpa [prefixWord, tailWord_2194642, baseEnd_2194642] using wordTrace_append hprefix tailTrace_2194642
  have hstable : (prefixWord ++ tailWord_2194642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194642).length < 2 ^ (prefixWord ++ tailWord_2194642).sum := by decide
  have hdescent : baseEnd_2194642 < baseStart_2194642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194682 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3]
def baseStart_2194682 : Nat := 118140960795 + 2194682 * 2 ^ 59
def prefixEnd_2194682 : Nat := 4983230072969 + 3 ^ 40 * 2194682 * 2
def baseEnd_2194682 : Nat := 1126926749770887530281847

theorem tailTrace_2194682 : CollatzResearch.WordTrace tailWord_2194682 prefixEnd_2194682 1126926749770887530281847 := by
  unfold tailWord_2194682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20011657158762352672404575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53364419090032940459745533 20011657158762352672404575)
  ·
    refine ⟨30017485738143529008606863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20011657158762352672404575 30017485738143529008606863)
    ·
      refine ⟨45026228607215293512910295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30017485738143529008606863 45026228607215293512910295)
      ·
        refine ⟨67539342910822940269365443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45026228607215293512910295 67539342910822940269365443)
        ·
          refine ⟨101309014366234410404048165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67539342910822940269365443 101309014366234410404048165)
          ·
            refine ⟨18995440193668951950759031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101309014366234410404048165 18995440193668951950759031)
            ·
              refine ⟨28493160290503427926138547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18995440193668951950759031 28493160290503427926138547)
              ·
                refine ⟨42739740435755141889207821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28493160290503427926138547 42739740435755141889207821)
                ·
                  refine ⟨16027402663408178208452933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42739740435755141889207821 16027402663408178208452933)
                  ·
                    refine ⟨3005137999389033414084925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16027402663408178208452933 3005137999389033414084925)
                    ·
                      refine ⟨1126926749770887530281847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005137999389033414084925 1126926749770887530281847)
                      ·
                        rfl

theorem cell23_2194682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3].length) (baseStart_2194682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194682 prefixEnd_2194682 := by exact prefixLift 2194682
  have htrace : WordTrace (prefixWord ++ tailWord_2194682) baseStart_2194682 baseEnd_2194682 := by
    simpa [prefixWord, tailWord_2194682, baseEnd_2194682] using wordTrace_append hprefix tailTrace_2194682
  have hstable : (prefixWord ++ tailWord_2194682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194682).length < 2 ^ (prefixWord ++ tailWord_2194682).sum := by decide
  have hdescent : baseEnd_2194682 < baseStart_2194682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194689 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 3, 4]
def baseStart_2194689 : Nat := 118140960795 + 2194689 * 2 ^ 59
def prefixEnd_2194689 : Nat := 4983230072969 + 3 ^ 40 * 2194689 * 2
def baseEnd_2194689 : Nat := 375643448045156334298105

theorem tailTrace_2194689 : CollatzResearch.WordTrace tailWord_2194689 prefixEnd_2194689 375643448045156334298105 := by
  unfold tailWord_2194689
  simp only [CollatzResearch.WordTrace]
  refine ⟨80046883946024050885123121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53364589297349367256748747 80046883946024050885123121)
  ·
    refine ⟨60035162959518038163842341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80046883946024050885123121 60035162959518038163842341)
    ·
      refine ⟨11256593054909632155720439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60035162959518038163842341 11256593054909632155720439)
      ·
        refine ⟨16884889582364448233580659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11256593054909632155720439 16884889582364448233580659)
        ·
          refine ⟨25327334373546672350370989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16884889582364448233580659 25327334373546672350370989)
          ·
            refine ⟨9497750390080002131389121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25327334373546672350370989 9497750390080002131389121)
            ·
              refine ⟨7123312792560001598541841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9497750390080002131389121 7123312792560001598541841)
              ·
                refine ⟨5342484594420001198906381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7123312792560001598541841 5342484594420001198906381)
                ·
                  refine ⟨2003431722907500449589893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5342484594420001198906381 2003431722907500449589893)
                  ·
                    refine ⟨375643448045156334298105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003431722907500449589893 375643448045156334298105)
                    ·
                      rfl

theorem cell23_2194689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_2194689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194689 prefixEnd_2194689 := by exact prefixLift 2194689
  have htrace : WordTrace (prefixWord ++ tailWord_2194689) baseStart_2194689 baseEnd_2194689 := by
    simpa [prefixWord, tailWord_2194689, baseEnd_2194689] using wordTrace_append hprefix tailTrace_2194689
  have hstable : (prefixWord ++ tailWord_2194689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194689).length < 2 ^ (prefixWord ++ tailWord_2194689).sum := by decide
  have hdescent : baseEnd_2194689 < baseStart_2194689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194702 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 8]
def baseStart_2194702 : Nat := 118140960795 + 2194702 * 2 ^ 59
def prefixEnd_2194702 : Nat := 4983230072969 + 3 ^ 40 * 2194702 * 2
def baseEnd_2194702 : Nat := 125215224375997494670195

theorem tailTrace_2194702 : CollatzResearch.WordTrace tailWord_2194702 prefixEnd_2194702 125215224375997494670195 := by
  unfold tailWord_2194702
  simp only [CollatzResearch.WordTrace]
  refine ⟨10005919761872119263168295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53364905396651302736897573 10005919761872119263168295)
  ·
    refine ⟨15008879642808178894752443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10005919761872119263168295 15008879642808178894752443)
    ·
      refine ⟨22513319464212268342128665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15008879642808178894752443 22513319464212268342128665)
      ·
        refine ⟨16884989598159201256596499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22513319464212268342128665 16884989598159201256596499)
        ·
          refine ⟨25327484397238801884894749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16884989598159201256596499 25327484397238801884894749)
          ·
            refine ⟨9497806648964550706835531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25327484397238801884894749 9497806648964550706835531)
            ·
              refine ⟨14246709973446826060253297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9497806648964550706835531 14246709973446826060253297)
              ·
                refine ⟨10685032480085119545189973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14246709973446826060253297 10685032480085119545189973)
                ·
                  refine ⟨125215224375997494670195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10685032480085119545189973 125215224375997494670195)
                  ·
                    rfl

theorem cell23_2194702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 8].length) (baseStart_2194702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194702 prefixEnd_2194702 := by exact prefixLift 2194702
  have htrace : WordTrace (prefixWord ++ tailWord_2194702) baseStart_2194702 baseEnd_2194702 := by
    simpa [prefixWord, tailWord_2194702, baseEnd_2194702] using wordTrace_append hprefix tailTrace_2194702
  have hstable : (prefixWord ++ tailWord_2194702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194702).length < 2 ^ (prefixWord ++ tailWord_2194702).sum := by decide
  have hdescent : baseEnd_2194702 < baseStart_2194702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194723 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 1, 4]
def baseStart_2194723 : Nat := 118140960795 + 2194723 * 2 ^ 59
def prefixEnd_2194723 : Nat := 4983230072969 + 3 ^ 40 * 2194723 * 2
def baseEnd_2194723 : Nat := 375649267492573956623053

theorem tailTrace_2194723 : CollatzResearch.WordTrace tailWord_2194723 prefixEnd_2194723 375649267492573956623053 := by
  unfold tailWord_2194723
  simp only [CollatzResearch.WordTrace]
  refine ⟨80048124027900874691860823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53365416018600583127907215 80048124027900874691860823)
  ·
    refine ⟨120072186041851312037791235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80048124027900874691860823 120072186041851312037791235)
    ·
      refine ⟨180108279062776968056686853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120072186041851312037791235 180108279062776968056686853)
      ·
        refine ⟨33770302324270681510628785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180108279062776968056686853 33770302324270681510628785)
        ·
          refine ⟨25327726743203011132971589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33770302324270681510628785 25327726743203011132971589)
          ·
            refine ⟨4748948764350564587432173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25327726743203011132971589 4748948764350564587432173)
            ·
              refine ⟨1780855786631461720287065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4748948764350564587432173 1780855786631461720287065)
              ·
                refine ⟨1335641839973596290215299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1780855786631461720287065 1335641839973596290215299)
                ·
                  refine ⟨2003462759960394435322949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335641839973596290215299 2003462759960394435322949)
                  ·
                    refine ⟨375649267492573956623053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003462759960394435322949 375649267492573956623053)
                    ·
                      rfl

theorem cell23_2194723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 4].length) (baseStart_2194723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194723 prefixEnd_2194723 := by exact prefixLift 2194723
  have htrace : WordTrace (prefixWord ++ tailWord_2194723) baseStart_2194723 baseEnd_2194723 := by
    simpa [prefixWord, tailWord_2194723, baseEnd_2194723] using wordTrace_append hprefix tailTrace_2194723
  have hstable : (prefixWord ++ tailWord_2194723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194723).length < 2 ^ (prefixWord ++ tailWord_2194723).sum := by decide
  have hdescent : baseEnd_2194723 < baseStart_2194723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194732 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 3, 5]
def baseStart_2194732 : Nat := 118140960795 + 2194732 * 2 ^ 59
def prefixEnd_2194732 : Nat := 4983230072969 + 3 ^ 40 * 2194732 * 2
def baseEnd_2194732 : Nat := 375650807934537444885539

theorem tailTrace_2194732 : CollatzResearch.WordTrace tailWord_2194732 prefixEnd_2194732 375650807934537444885539 := by
  unfold tailWord_2194732
  simp only [CollatzResearch.WordTrace]
  refine ⟨40024226142434134614469225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53365634856578846152625633 40024226142434134614469225)
  ·
    refine ⟨30018169606825600960851919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40024226142434134614469225 30018169606825600960851919)
    ·
      refine ⟨45027254410238401441277879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30018169606825600960851919 45027254410238401441277879)
      ·
        refine ⟨67540881615357602161916819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45027254410238401441277879 67540881615357602161916819)
        ·
          refine ⟨101311322423036403242875229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67540881615357602161916819 101311322423036403242875229)
          ·
            refine ⟨37991745908638651216078211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101311322423036403242875229 37991745908638651216078211)
            ·
              refine ⟨56987618862957976824117317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37991745908638651216078211 56987618862957976824117317)
              ·
                refine ⟨10685178536804620654521997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56987618862957976824117317 10685178536804620654521997)
                ·
                  refine ⟨4006941951301732745445749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10685178536804620654521997 4006941951301732745445749)
                  ·
                    refine ⟨375650807934537444885539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4006941951301732745445749 375650807934537444885539)
                    ·
                      rfl

theorem cell23_2194732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_2194732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194732 prefixEnd_2194732 := by exact prefixLift 2194732
  have htrace : WordTrace (prefixWord ++ tailWord_2194732) baseStart_2194732 baseEnd_2194732 := by
    simpa [prefixWord, tailWord_2194732, baseEnd_2194732] using wordTrace_append hprefix tailTrace_2194732
  have hstable : (prefixWord ++ tailWord_2194732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194732).length < 2 ^ (prefixWord ++ tailWord_2194732).sum := by decide
  have hdescent : baseEnd_2194732 < baseStart_2194732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194766 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_2194766 : Nat := 118140960795 + 2194766 * 2 ^ 59
def prefixEnd_2194766 : Nat := 4983230072969 + 3 ^ 40 * 2194766 * 2
def baseEnd_2194766 : Nat := 375656627381955067210487

theorem tailTrace_2194766 : CollatzResearch.WordTrace tailWord_2194766 prefixEnd_2194766 375656627381955067210487 := by
  unfold tailWord_2194766
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006211545843136629459519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53366461577830062023784101 10006211545843136629459519)
  ·
    refine ⟨15009317318764704944189279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10006211545843136629459519 15009317318764704944189279)
    ·
      refine ⟨22513975978147057416283919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15009317318764704944189279 22513975978147057416283919)
      ·
        refine ⟨33770963967220586124425879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22513975978147057416283919 33770963967220586124425879)
        ·
          refine ⟨50656445950830879186638819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33770963967220586124425879 50656445950830879186638819)
          ·
            refine ⟨75984668926246318779958229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50656445950830879186638819 75984668926246318779958229)
            ·
              refine ⟨1780890677958898096405271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75984668926246318779958229 1780890677958898096405271)
              ·
                refine ⟨2671336016938347144607907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780890677958898096405271 2671336016938347144607907)
                ·
                  refine ⟨4007004025407520716911861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671336016938347144607907 4007004025407520716911861)
                  ·
                    refine ⟨375656627381955067210487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4007004025407520716911861 375656627381955067210487)
                    ·
                      rfl

theorem cell23_2194766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_2194766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194766 prefixEnd_2194766 := by exact prefixLift 2194766
  have htrace : WordTrace (prefixWord ++ tailWord_2194766) baseStart_2194766 baseEnd_2194766 := by
    simpa [prefixWord, tailWord_2194766, baseEnd_2194766] using wordTrace_append hprefix tailTrace_2194766
  have hstable : (prefixWord ++ tailWord_2194766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194766).length < 2 ^ (prefixWord ++ tailWord_2194766).sum := by decide
  have hdescent : baseEnd_2194766 < baseStart_2194766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194774 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_2194774 : Nat := 118140960795 + 2194774 * 2 ^ 59
def prefixEnd_2194774 : Nat := 4983230072969 + 3 ^ 40 * 2194774 * 2
def baseEnd_2194774 : Nat := 375657996663700390110475

theorem tailTrace_2194774 : CollatzResearch.WordTrace tailWord_2194774 prefixEnd_2194774 375657996663700390110475 := by
  unfold tailWord_2194774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003124009419756900122961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53366656100477406934644917 5003124009419756900122961)
  ·
    refine ⟨3752343007064817675092221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5003124009419756900122961 3752343007064817675092221)
    ·
      refine ⟨1407128627649306628159583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3752343007064817675092221 1407128627649306628159583)
      ·
        refine ⟨2110692941473959942239375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407128627649306628159583 2110692941473959942239375)
        ·
          refine ⟨3166039412210939913359063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110692941473959942239375 3166039412210939913359063)
          ·
            refine ⟨4749059118316409870038595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166039412210939913359063 4749059118316409870038595)
            ·
              refine ⟨7123588677474614805057893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749059118316409870038595 7123588677474614805057893)
              ·
                refine ⟨1335672877026490275948355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7123588677474614805057893 1335672877026490275948355)
                ·
                  refine ⟨2003509315539735413922533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335672877026490275948355 2003509315539735413922533)
                  ·
                    refine ⟨375657996663700390110475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003509315539735413922533 375657996663700390110475)
                    ·
                      rfl

theorem cell23_2194774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_2194774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194774 prefixEnd_2194774 := by exact prefixLift 2194774
  have htrace : WordTrace (prefixWord ++ tailWord_2194774) baseStart_2194774 baseEnd_2194774 := by
    simpa [prefixWord, tailWord_2194774, baseEnd_2194774] using wordTrace_append hprefix tailTrace_2194774
  have hstable : (prefixWord ++ tailWord_2194774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194774).length < 2 ^ (prefixWord ++ tailWord_2194774).sum := by decide
  have hdescent : baseEnd_2194774 < baseStart_2194774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194789 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_2194789 : Nat := 118140960795 + 2194789 * 2 ^ 59
def prefixEnd_2194789 : Nat := 4983230072969 + 3 ^ 40 * 2194789 * 2
def baseEnd_2194789 : Nat := 1126981692200918611643855

theorem tailTrace_2194789 : CollatzResearch.WordTrace tailWord_2194789 prefixEnd_2194789 1126981692200918611643855 := by
  unfold tailWord_2194789
  simp only [CollatzResearch.WordTrace]
  refine ⟨80050531245661767963763421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53367020830441178642508947 80050531245661767963763421)
  ·
    refine ⟨30018949217123162986411283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80050531245661767963763421 30018949217123162986411283)
    ·
      refine ⟨45028423825684744479616925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30018949217123162986411283 45028423825684744479616925)
      ·
        refine ⟨16885658934631779179856347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45028423825684744479616925 16885658934631779179856347)
        ·
          refine ⟨25328488401947668769784521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16885658934631779179856347 25328488401947668769784521)
          ·
            refine ⟨18996366301460751577338391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25328488401947668769784521 18996366301460751577338391)
            ·
              refine ⟨28494549452191127366007587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18996366301460751577338391 28494549452191127366007587)
              ·
                refine ⟨42741824178286691049011381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28494549452191127366007587 42741824178286691049011381)
                ·
                  refine ⟨4007046016714377285844817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42741824178286691049011381 4007046016714377285844817)
                  ·
                    refine ⟨3005284512535782964383613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007046016714377285844817 3005284512535782964383613)
                    ·
                      refine ⟨1126981692200918611643855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005284512535782964383613 1126981692200918611643855)
                      ·
                        rfl

theorem cell23_2194789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_2194789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194789 prefixEnd_2194789 := by exact prefixLift 2194789
  have htrace : WordTrace (prefixWord ++ tailWord_2194789) baseStart_2194789 baseEnd_2194789 := by
    simpa [prefixWord, tailWord_2194789, baseEnd_2194789] using wordTrace_append hprefix tailTrace_2194789
  have hstable : (prefixWord ++ tailWord_2194789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194789).length < 2 ^ (prefixWord ++ tailWord_2194789).sum := by decide
  have hdescent : baseEnd_2194789 < baseStart_2194789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194796 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_2194796 : Nat := 118140960795 + 2194796 * 2 ^ 59
def prefixEnd_2194796 : Nat := 4983230072969 + 3 ^ 40 * 2194796 * 2
def baseEnd_2194796 : Nat := 375661762188500028085441

theorem tailTrace_2194796 : CollatzResearch.WordTrace tailWord_2194796 prefixEnd_2194796 375661762188500028085441 := by
  unfold tailWord_2194796
  simp only [CollatzResearch.WordTrace]
  refine ⟨40025393278318204079634121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53367191037757605439512161 40025393278318204079634121)
  ·
    refine ⟨30019044958738653059725591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40025393278318204079634121 30019044958738653059725591)
    ·
      refine ⟨45028567438107979589588387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30019044958738653059725591 45028567438107979589588387)
      ·
        refine ⟨67542851157161969384382581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45028567438107979589588387 67542851157161969384382581)
        ·
          refine ⟨6332142295983934629785867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67542851157161969384382581 6332142295983934629785867)
          ·
            refine ⟨9498213443975901944678801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6332142295983934629785867 9498213443975901944678801)
            ·
              refine ⟨7123660082981926458509101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9498213443975901944678801 7123660082981926458509101)
              ·
                refine ⟨2671372531118222421940913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7123660082981926458509101 2671372531118222421940913)
                ·
                  refine ⟨2003529398338666816455685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671372531118222421940913 2003529398338666816455685)
                  ·
                    refine ⟨375661762188500028085441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003529398338666816455685 375661762188500028085441)
                    ·
                      rfl

theorem cell23_2194796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_2194796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194796 prefixEnd_2194796 := by exact prefixLift 2194796
  have htrace : WordTrace (prefixWord ++ tailWord_2194796) baseStart_2194796 baseEnd_2194796 := by
    simpa [prefixWord, tailWord_2194796, baseEnd_2194796] using wordTrace_append hprefix tailTrace_2194796
  have hstable : (prefixWord ++ tailWord_2194796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194796).length < 2 ^ (prefixWord ++ tailWord_2194796).sum := by decide
  have hdescent : baseEnd_2194796 < baseStart_2194796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194799 : List Nat := [1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 4]
def baseStart_2194799 : Nat := 118140960795 + 2194799 * 2 ^ 59
def prefixEnd_2194799 : Nat := 4983230072969 + 3 ^ 40 * 2194799 * 2
def baseEnd_2194799 : Nat := 1126986827007463572518809

theorem tailTrace_2194799 : CollatzResearch.WordTrace tailWord_2194799 prefixEnd_2194799 1126986827007463572518809 := by
  unfold tailWord_2194799
  simp only [CollatzResearch.WordTrace]
  refine ⟨80050895975625539671627451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53367263983750359781084967 80050895975625539671627451)
  ·
    refine ⟨120076343963438309507441177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80050895975625539671627451 120076343963438309507441177)
    ·
      refine ⟨90057257972578732130580883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120076343963438309507441177 90057257972578732130580883)
      ·
        refine ⟨135085886958868098195871325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90057257972578732130580883 135085886958868098195871325)
        ·
          refine ⟨50657207609575536823451747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135085886958868098195871325 50657207609575536823451747)
          ·
            refine ⟨75985811414363305235177621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50657207609575536823451747 75985811414363305235177621)
            ·
              refine ⟨3561834910048279932898951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75985811414363305235177621 3561834910048279932898951)
              ·
                refine ⟨5342752365072419899348427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3561834910048279932898951 5342752365072419899348427)
                ·
                  refine ⟨8014128547608629849022641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5342752365072419899348427 8014128547608629849022641)
                  ·
                    refine ⟨6010596410706472386766981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8014128547608629849022641 6010596410706472386766981)
                    ·
                      refine ⟨1126986827007463572518809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6010596410706472386766981 1126986827007463572518809)
                      ·
                        rfl

theorem cell23_2194799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 2, 4].length) (baseStart_2194799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194799 prefixEnd_2194799 := by exact prefixLift 2194799
  have htrace : WordTrace (prefixWord ++ tailWord_2194799) baseStart_2194799 baseEnd_2194799 := by
    simpa [prefixWord, tailWord_2194799, baseEnd_2194799] using wordTrace_append hprefix tailTrace_2194799
  have hstable : (prefixWord ++ tailWord_2194799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194799).length < 2 ^ (prefixWord ++ tailWord_2194799).sum := by decide
  have hdescent : baseEnd_2194799 < baseStart_2194799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194814 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2194814 : Nat := 118140960795 + 2194814 * 2 ^ 59
def prefixEnd_2194814 : Nat := 4983230072969 + 3 ^ 40 * 2194814 * 2
def baseEnd_2194814 : Nat := 1126994529217281013831241

theorem tailTrace_2194814 : CollatzResearch.WordTrace tailWord_2194814 prefixEnd_2194814 1126994529217281013831241 := by
  unfold tailWord_2194814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006430383821399654177937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53367628713714131488948997 10006430383821399654177937)
  ·
    refine ⟨7504822787866049740633453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10006430383821399654177937 7504822787866049740633453)
    ·
      refine ⟨2814308545449768652737545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7504822787866049740633453 2814308545449768652737545)
      ·
        refine ⟨2110731409087326489553159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2814308545449768652737545 2110731409087326489553159)
        ·
          refine ⟨3166097113630989734329739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2110731409087326489553159 3166097113630989734329739)
          ·
            refine ⟨4749145670446484601494609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166097113630989734329739 4749145670446484601494609)
            ·
              refine ⟨3561859252834863451120957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4749145670446484601494609 3561859252834863451120957)
              ·
                refine ⟨1335697219813073794170359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3561859252834863451120957 1335697219813073794170359)
                ·
                  refine ⟨2003545829719610691255539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335697219813073794170359 2003545829719610691255539)
                  ·
                    refine ⟨3005318744579416036883309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2003545829719610691255539 3005318744579416036883309)
                    ·
                      refine ⟨1126994529217281013831241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005318744579416036883309 1126994529217281013831241)
                      ·
                        rfl

theorem cell23_2194814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2194814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194814 prefixEnd_2194814 := by exact prefixLift 2194814
  have htrace : WordTrace (prefixWord ++ tailWord_2194814) baseStart_2194814 baseEnd_2194814 := by
    simpa [prefixWord, tailWord_2194814, baseEnd_2194814] using wordTrace_append hprefix tailTrace_2194814
  have hstable : (prefixWord ++ tailWord_2194814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194814).length < 2 ^ (prefixWord ++ tailWord_2194814).sum := by decide
  have hdescent : baseEnd_2194814 < baseStart_2194814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194820 : List Nat := [2, 3, 2, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_2194820 : Nat := 118140960795 + 2194820 * 2 ^ 59
def prefixEnd_2194820 : Nat := 4983230072969 + 3 ^ 40 * 2194820 * 2
def baseEnd_2194820 : Nat := 1126997610101207990356213

theorem tailTrace_2194820 : CollatzResearch.WordTrace tailWord_2194820 prefixEnd_2194820 1126997610101207990356213 := by
  unfold tailWord_2194820
  simp only [CollatzResearch.WordTrace]
  refine ⟨40025830954274730129070957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53367774605699640172094609 40025830954274730129070957)
  ·
    refine ⟨15009686607853023798401609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40025830954274730129070957 15009686607853023798401609)
    ·
      refine ⟨11257264955889767848801207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15009686607853023798401609 11257264955889767848801207)
      ·
        refine ⟨16885897433834651773201811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11257264955889767848801207 16885897433834651773201811)
        ·
          refine ⟨25328846150751977659802717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16885897433834651773201811 25328846150751977659802717)
          ·
            refine ⟨9498317306531991622426019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25328846150751977659802717 9498317306531991622426019)
            ·
              refine ⟨14247475959797987433639029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9498317306531991622426019 14247475959797987433639029)
              ·
                refine ⟨1335700871231061321903659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14247475959797987433639029 1335700871231061321903659)
                ·
                  refine ⟨2003551306846591982855489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335700871231061321903659 2003551306846591982855489)
                  ·
                    refine ⟨1502663480134943987141617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003551306846591982855489 1502663480134943987141617)
                    ·
                      refine ⟨1126997610101207990356213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502663480134943987141617 1126997610101207990356213)
                      ·
                        rfl

theorem cell23_2194820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_2194820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194820 prefixEnd_2194820 := by exact prefixLift 2194820
  have htrace : WordTrace (prefixWord ++ tailWord_2194820) baseStart_2194820 baseEnd_2194820 := by
    simpa [prefixWord, tailWord_2194820, baseEnd_2194820] using wordTrace_append hprefix tailTrace_2194820
  have hstable : (prefixWord ++ tailWord_2194820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194820).length < 2 ^ (prefixWord ++ tailWord_2194820).sum := by decide
  have hdescent : baseEnd_2194820 < baseStart_2194820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194823 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 1, 2, 3]
def baseStart_2194823 : Nat := 118140960795 + 2194823 * 2 ^ 59
def prefixEnd_2194823 : Nat := 4983230072969 + 3 ^ 40 * 2194823 * 2
def baseEnd_2194823 : Nat := 1126999150543171478618699

theorem tailTrace_2194823 : CollatzResearch.WordTrace tailWord_2194823 prefixEnd_2194823 1126999150543171478618699 := by
  unfold tailWord_2194823
  simp only [CollatzResearch.WordTrace]
  refine ⟨80051771327538591770501123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53367847551692394513667415 80051771327538591770501123)
  ·
    refine ⟨120077656991307887655751685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80051771327538591770501123 120077656991307887655751685)
    ·
      refine ⟨22514560685870228935453441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120077656991307887655751685 22514560685870228935453441)
      ·
        refine ⟨16885920514402671701590081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22514560685870228935453441 16885920514402671701590081)
        ·
          refine ⟨12664440385802003776192561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16885920514402671701590081 12664440385802003776192561)
          ·
            refine ⟨9498330289351502832144421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12664440385802003776192561 9498330289351502832144421)
            ·
              refine ⟨1780936929253406781027079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9498330289351502832144421 1780936929253406781027079)
              ·
                refine ⟨2671405393880110171540619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1780936929253406781027079 2671405393880110171540619)
                ·
                  refine ⟨4007108090820165257310929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671405393880110171540619 4007108090820165257310929)
                  ·
                    refine ⟨3005331068115123942983197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007108090820165257310929 3005331068115123942983197)
                    ·
                      refine ⟨1126999150543171478618699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005331068115123942983197 1126999150543171478618699)
                      ·
                        rfl

theorem cell23_2194823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_2194823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194823 prefixEnd_2194823 := by exact prefixLift 2194823
  have htrace : WordTrace (prefixWord ++ tailWord_2194823) baseStart_2194823 baseEnd_2194823 := by
    simpa [prefixWord, tailWord_2194823, baseEnd_2194823] using wordTrace_append hprefix tailTrace_2194823
  have hstable : (prefixWord ++ tailWord_2194823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194823).length < 2 ^ (prefixWord ++ tailWord_2194823).sum := by decide
  have hdescent : baseEnd_2194823 < baseStart_2194823 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194830 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_2194830 : Nat := 118140960795 + 2194830 * 2 ^ 59
def prefixEnd_2194830 : Nat := 4983230072969 + 3 ^ 40 * 2194830 * 2
def baseEnd_2194830 : Nat := 375667581635917650410389

theorem tailTrace_2194830 : CollatzResearch.WordTrace tailWord_2194830 prefixEnd_2194830 375667581635917650410389 := by
  unfold tailWord_2194830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10006503329814153995750743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53368017759008821310670629 10006503329814153995750743)
  ·
    refine ⟨15009754994721230993626115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10006503329814153995750743 15009754994721230993626115)
    ·
      refine ⟨22514632492081846490439173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15009754994721230993626115 22514632492081846490439173)
      ·
        refine ⟨4221493592265346216957345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22514632492081846490439173 4221493592265346216957345)
        ·
          refine ⟨3166120194199009662718009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4221493592265346216957345 3166120194199009662718009)
          ·
            refine ⟨2374590145649257247038507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166120194199009662718009 2374590145649257247038507)
            ·
              refine ⟨3561885218473885870557761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2374590145649257247038507 3561885218473885870557761)
              ·
                refine ⟨2671413913855414402918321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3561885218473885870557761 2671413913855414402918321)
                ·
                  refine ⟨2003560435391560802188741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671413913855414402918321 2003560435391560802188741)
                  ·
                    refine ⟨375667581635917650410389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003560435391560802188741 375667581635917650410389)
                    ·
                      rfl

theorem cell23_2194830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_2194830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194830 prefixEnd_2194830 := by exact prefixLift 2194830
  have htrace : WordTrace (prefixWord ++ tailWord_2194830) baseStart_2194830 baseEnd_2194830 := by
    simpa [prefixWord, tailWord_2194830, baseEnd_2194830] using wordTrace_append hprefix tailTrace_2194830
  have hstable : (prefixWord ++ tailWord_2194830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194830).length < 2 ^ (prefixWord ++ tailWord_2194830).sum := by decide
  have hdescent : baseEnd_2194830 < baseStart_2194830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2194949 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_2194949 : Nat := 118140960795 + 2194949 * 2 ^ 59
def prefixEnd_2194949 : Nat := 4983230072969 + 3 ^ 40 * 2194949 * 2
def baseEnd_2194949 : Nat := 1127063849105637985643119

theorem tailTrace_2194949 : CollatzResearch.WordTrace tailWord_2194949 prefixEnd_2194949 1127063849105637985643119 := by
  unfold tailWord_2194949
  simp only [CollatzResearch.WordTrace]
  refine ⟨80056366925082115289587901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53370911283388076859725267 80056366925082115289587901)
  ·
    refine ⟨30021137596905793233595463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80056366925082115289587901 30021137596905793233595463)
    ·
      refine ⟨45031706395358689850393195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30021137596905793233595463 45031706395358689850393195)
      ·
        refine ⟨67547559593038034775589793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45031706395358689850393195 67547559593038034775589793)
        ·
          refine ⟨50660669694778526081692345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67547559593038034775589793 50660669694778526081692345)
          ·
            refine ⟨37995502271083894561269259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50660669694778526081692345 37995502271083894561269259)
            ·
              refine ⟨56993253406625841841903889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37995502271083894561269259 56993253406625841841903889)
              ·
                refine ⟨42744940054969381381427917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56993253406625841841903889 42744940054969381381427917)
                ·
                  refine ⟨16029352520613518018035469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42744940054969381381427917 16029352520613518018035469)
                  ·
                    refine ⟨6011007195230069256763301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16029352520613518018035469 6011007195230069256763301)
                    ·
                      refine ⟨1127063849105637985643119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6011007195230069256763301 1127063849105637985643119)
                      ·
                        rfl

theorem cell23_2194949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_2194949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2194949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2194949 prefixEnd_2194949 := by exact prefixLift 2194949
  have htrace : WordTrace (prefixWord ++ tailWord_2194949) baseStart_2194949 baseEnd_2194949 := by
    simpa [prefixWord, tailWord_2194949, baseEnd_2194949] using wordTrace_append hprefix tailTrace_2194949
  have hstable : (prefixWord ++ tailWord_2194949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2194949).length < 2 ^ (prefixWord ++ tailWord_2194949).sum := by decide
  have hdescent : baseEnd_2194949 < baseStart_2194949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2194949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195043 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 1, 5, 2]
def baseStart_2195043 : Nat := 118140960795 + 2195043 * 2 ^ 59
def prefixEnd_2195043 : Nat := 4983230072969 + 3 ^ 40 * 2195043 * 2
def baseEnd_2195043 : Nat := 1127112116287160617867687

theorem tailTrace_2195043 : CollatzResearch.WordTrace tailWord_2195043 prefixEnd_2195043 1127112116287160617867687 := by
  unfold tailWord_2195043
  simp only [CollatzResearch.WordTrace]
  refine ⟨80059795386741569343509783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53373196924494379562339855 80059795386741569343509783)
  ·
    refine ⟨120089693080112354015264675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80059795386741569343509783 120089693080112354015264675)
    ·
      refine ⟨180134539620168531022897013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120089693080112354015264675 180134539620168531022897013)
      ·
        refine ⟨16887613089390799783396595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180134539620168531022897013 16887613089390799783396595)
        ·
          refine ⟨25331419634086199675094893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16887613089390799783396595 25331419634086199675094893)
          ·
            refine ⟨9499282362782324878160585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25331419634086199675094893 9499282362782324878160585)
            ·
              refine ⟨7124461772086743658620439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9499282362782324878160585 7124461772086743658620439)
              ·
                refine ⟨10686692658130115487930659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7124461772086743658620439 10686692658130115487930659)
                ·
                  refine ⟨16030038987195173231895989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10686692658130115487930659 16030038987195173231895989)
                  ·
                    refine ⟨1502816155049547490490249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16030038987195173231895989 1502816155049547490490249)
                    ·
                      refine ⟨1127112116287160617867687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502816155049547490490249 1127112116287160617867687)
                      ·
                        rfl

theorem cell23_2195043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_2195043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195043 prefixEnd_2195043 := by exact prefixLift 2195043
  have htrace : WordTrace (prefixWord ++ tailWord_2195043) baseStart_2195043 baseEnd_2195043 := by
    simpa [prefixWord, tailWord_2195043, baseEnd_2195043] using wordTrace_append hprefix tailTrace_2195043
  have hstable : (prefixWord ++ tailWord_2195043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195043).length < 2 ^ (prefixWord ++ tailWord_2195043).sum := by decide
  have hdescent : baseEnd_2195043 < baseStart_2195043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195067 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 1, 1, 3]
def baseStart_2195067 : Nat := 118140960795 + 2195067 * 2 ^ 59
def prefixEnd_2195067 : Nat := 4983230072969 + 3 ^ 40 * 2195067 * 2
def baseEnd_2195067 : Nat := 1127124439822868523967577

theorem tailTrace_2195067 : CollatzResearch.WordTrace tailWord_2195067 prefixEnd_2195067 1127124439822868523967577 := by
  unfold tailWord_2195067
  simp only [CollatzResearch.WordTrace]
  refine ⟨80060670738654621442383455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53373780492436414294922303 80060670738654621442383455)
  ·
    refine ⟨120091006107981932163575183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80060670738654621442383455 120091006107981932163575183)
    ·
      refine ⟨180136509161972898245362775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120091006107981932163575183 180136509161972898245362775)
      ·
        refine ⟨270204763742959347368044163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180136509161972898245362775 270204763742959347368044163)
        ·
          refine ⟨405307145614439021052066245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270204763742959347368044163 405307145614439021052066245)
          ·
            refine ⟨75995089802707316447262421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 405307145614439021052066245 75995089802707316447262421)
            ·
              refine ⟨1781134917250952729232713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 75995089802707316447262421 1781134917250952729232713)
              ·
                refine ⟨1335851187938214546924535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781134917250952729232713 1335851187938214546924535)
                ·
                  refine ⟨2003776781907321820386803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335851187938214546924535 2003776781907321820386803)
                  ·
                    refine ⟨3005665172860982730580205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2003776781907321820386803 3005665172860982730580205)
                    ·
                      refine ⟨1127124439822868523967577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005665172860982730580205 1127124439822868523967577)
                      ·
                        rfl

theorem cell23_2195067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 1, 3].length) (baseStart_2195067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195067 prefixEnd_2195067 := by exact prefixLift 2195067
  have htrace : WordTrace (prefixWord ++ tailWord_2195067) baseStart_2195067 baseEnd_2195067 := by
    simpa [prefixWord, tailWord_2195067, baseEnd_2195067] using wordTrace_append hprefix tailTrace_2195067
  have hstable : (prefixWord ++ tailWord_2195067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195067).length < 2 ^ (prefixWord ++ tailWord_2195067).sum := by decide
  have hdescent : baseEnd_2195067 < baseStart_2195067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195083 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 2, 4]
def baseStart_2195083 : Nat := 118140960795 + 2195083 * 2 ^ 59
def prefixEnd_2195083 : Nat := 4983230072969 + 3 ^ 40 * 2195083 * 2
def baseEnd_2195083 : Nat := 375710885171113487122501

theorem tailTrace_2195083 : CollatzResearch.WordTrace tailWord_2195083 prefixEnd_2195083 375710885171113487122501 := by
  unfold tailWord_2195083
  simp only [CollatzResearch.WordTrace]
  refine ⟨80061254306596656174965903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53374169537731104116643935 80061254306596656174965903)
  ·
    refine ⟨120091881459894984262448855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80061254306596656174965903 120091881459894984262448855)
    ·
      refine ⟨180137822189842476393673283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120091881459894984262448855 180137822189842476393673283)
      ·
        refine ⟨270206733284763714590509925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180137822189842476393673283 270206733284763714590509925)
        ·
          refine ⟨50663762490893196485720611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270206733284763714590509925 50663762490893196485720611)
          ·
            refine ⟨75995643736339794728580917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50663762490893196485720611 75995643736339794728580917)
            ·
              refine ⟨7124591600281855755804461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75995643736339794728580917 7124591600281855755804461)
              ·
                refine ⟨2671721850105695908426673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7124591600281855755804461 2671721850105695908426673)
                ·
                  refine ⟨2003791387579271931320005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2671721850105695908426673 2003791387579271931320005)
                  ·
                    refine ⟨375710885171113487122501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003791387579271931320005 375710885171113487122501)
                    ·
                      rfl

theorem cell23_2195083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 4].length) (baseStart_2195083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195083 prefixEnd_2195083 := by exact prefixLift 2195083
  have htrace : WordTrace (prefixWord ++ tailWord_2195083) baseStart_2195083 baseEnd_2195083 := by
    simpa [prefixWord, tailWord_2195083, baseEnd_2195083] using wordTrace_append hprefix tailTrace_2195083
  have hstable : (prefixWord ++ tailWord_2195083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195083).length < 2 ^ (prefixWord ++ tailWord_2195083).sum := by decide
  have hdescent : baseEnd_2195083 < baseStart_2195083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195090 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_2195090 : Nat := 118140960795 + 2195090 * 2 ^ 59
def prefixEnd_2195090 : Nat := 4983230072969 + 3 ^ 40 * 2195090 * 2
def baseEnd_2195090 : Nat := 1127136249877921933979971

theorem tailTrace_2195090 : CollatzResearch.WordTrace tailWord_2195090 prefixEnd_2195090 1127136249877921933979971 := by
  unfold tailWord_2195090
  simp only [CollatzResearch.WordTrace]
  refine ⟨20015377404392824092617681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53374339745047530913647149 20015377404392824092617681)
  ·
    refine ⟨15011533053294618069463261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20015377404392824092617681 15011533053294618069463261)
    ·
      refine ⟨5629324894985481776048723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15011533053294618069463261 5629324894985481776048723)
      ·
        refine ⟨8443987342478222664073085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5629324894985481776048723 8443987342478222664073085)
        ·
          refine ⟨3166495253429333499027407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8443987342478222664073085 3166495253429333499027407)
          ·
            refine ⟨4749742880144000248541111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166495253429333499027407 4749742880144000248541111)
            ·
              refine ⟨7124614320216000372811667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749742880144000248541111 7124614320216000372811667)
              ·
                refine ⟨10686921480324000559217501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7124614320216000372811667 10686921480324000559217501)
                ·
                  refine ⟨4007595555121500209706563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10686921480324000559217501 4007595555121500209706563)
                  ·
                    refine ⟨6011393332682250314559845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4007595555121500209706563 6011393332682250314559845)
                    ·
                      refine ⟨1127136249877921933979971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6011393332682250314559845 1127136249877921933979971)
                      ·
                        rfl

theorem cell23_2195090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_2195090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195090 prefixEnd_2195090 := by exact prefixLift 2195090
  have htrace : WordTrace (prefixWord ++ tailWord_2195090) baseStart_2195090 baseEnd_2195090 := by
    simpa [prefixWord, tailWord_2195090, baseEnd_2195090] using wordTrace_append hprefix tailTrace_2195090
  have hstable : (prefixWord ++ tailWord_2195090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195090).length < 2 ^ (prefixWord ++ tailWord_2195090).sum := by decide
  have hdescent : baseEnd_2195090 < baseStart_2195090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195096 : List Nat := [2, 1, 2, 4, 1, 2, 2, 9]
def baseStart_2195096 : Nat := 118140960795 + 2195096 * 2 ^ 59
def prefixEnd_2195096 : Nat := 4983230072969 + 3 ^ 40 * 2195096 * 2
def baseEnd_2195096 : Nat := 41745901139327737426109

theorem tailTrace_2195096 : CollatzResearch.WordTrace tailWord_2195096 prefixEnd_2195096 41745901139327737426109 := by
  unfold tailWord_2195096
  simp only [CollatzResearch.WordTrace]
  refine ⟨40030864227774779697594571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53374485637033039596792761 40030864227774779697594571)
  ·
    refine ⟨60046296341662169546391857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40030864227774779697594571 60046296341662169546391857)
    ·
      refine ⟨45034722256246627159793893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60046296341662169546391857 45034722256246627159793893)
      ·
        refine ⟨8444010423046242592461355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45034722256246627159793893 8444010423046242592461355)
        ·
          refine ⟨12666015634569363888692033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8444010423046242592461355 12666015634569363888692033)
          ·
            refine ⟨9499511725927022916519025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12666015634569363888692033 9499511725927022916519025)
            ·
              refine ⟨7124633794445267187389269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9499511725927022916519025 7124633794445267187389269)
              ·
                refine ⟨41745901139327737426109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7124633794445267187389269 41745901139327737426109)
                ·
                  rfl

theorem cell23_2195096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 9].length) (baseStart_2195096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195096 prefixEnd_2195096 := by exact prefixLift 2195096
  have htrace : WordTrace (prefixWord ++ tailWord_2195096) baseStart_2195096 baseEnd_2195096 := by
    simpa [prefixWord, tailWord_2195096, baseEnd_2195096] using wordTrace_append hprefix tailTrace_2195096
  have hstable : (prefixWord ++ tailWord_2195096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195096).length < 2 ^ (prefixWord ++ tailWord_2195096).sum := by decide
  have hdescent : baseEnd_2195096 < baseStart_2195096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195107 : List Nat := [1, 1, 1, 4, 1, 1, 4, 5, 1, 2, 2]
def baseStart_2195107 : Nat := 118140960795 + 2195107 * 2 ^ 59
def prefixEnd_2195107 : Nat := 4983230072969 + 3 ^ 40 * 2195107 * 2
def baseEnd_2195107 : Nat := 1127144979049048367467393

theorem tailTrace_2195107 : CollatzResearch.WordTrace tailWord_2195107 prefixEnd_2195107 1127144979049048367467393 := by
  unfold tailWord_2195107
  simp only [CollatzResearch.WordTrace]
  refine ⟨80062129658509708273839575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53374753105673138849226383 80062129658509708273839575)
  ·
    refine ⟨120093194487764562410759363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80062129658509708273839575 120093194487764562410759363)
    ·
      refine ⟨180139791731646843616139045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120093194487764562410759363 180139791731646843616139045)
      ·
        refine ⟨33776210949683783178026071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 180139791731646843616139045 33776210949683783178026071)
        ·
          refine ⟨50664316424525674767039107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33776210949683783178026071 50664316424525674767039107)
          ·
            refine ⟨75996474636788512150558661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50664316424525674767039107 75996474636788512150558661)
            ·
              refine ⟨14249338994397846028229749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75996474636788512150558661 14249338994397846028229749)
              ·
                refine ⟨1335875530724798065146539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14249338994397846028229749 1335875530724798065146539)
                ·
                  refine ⟨2003813296087197097719809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335875530724798065146539 2003813296087197097719809)
                  ·
                    refine ⟨1502859972065397823289857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2003813296087197097719809 1502859972065397823289857)
                    ·
                      refine ⟨1127144979049048367467393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502859972065397823289857 1127144979049048367467393)
                      ·
                        rfl

theorem cell23_2195107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 5, 1, 2, 2].length) (baseStart_2195107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195107 prefixEnd_2195107 := by exact prefixLift 2195107
  have htrace : WordTrace (prefixWord ++ tailWord_2195107) baseStart_2195107 baseEnd_2195107 := by
    simpa [prefixWord, tailWord_2195107, baseEnd_2195107] using wordTrace_append hprefix tailTrace_2195107
  have hstable : (prefixWord ++ tailWord_2195107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195107).length < 2 ^ (prefixWord ++ tailWord_2195107).sum := by decide
  have hdescent : baseEnd_2195107 < baseStart_2195107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195118 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_2195118 : Nat := 118140960795 + 2195118 * 2 ^ 59
def prefixEnd_2195118 : Nat := 4983230072969 + 3 ^ 40 * 2195118 * 2
def baseEnd_2195118 : Nat := 1127150627336247824429843

theorem tailTrace_2195118 : CollatzResearch.WordTrace tailWord_2195118 prefixEnd_2195118 1127150627336247824429843 := by
  unfold tailWord_2195118
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007816357683732144061251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53375020574313238101660005 10007816357683732144061251)
  ·
    refine ⟨15011724536525598216091877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10007816357683732144061251 15011724536525598216091877)
    ·
      refine ⟨2814698350598549665517227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15011724536525598216091877 2814698350598549665517227)
      ·
        refine ⟨4222047525897824498275841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814698350598549665517227 4222047525897824498275841)
        ·
          refine ⟨3166535644423368373706881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4222047525897824498275841 3166535644423368373706881)
          ·
            refine ⟨2374901733317526280280161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166535644423368373706881 2374901733317526280280161)
            ·
              refine ⟨1781176299988144710210121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374901733317526280280161 1781176299988144710210121)
              ·
                refine ⟨1335882224991108532657591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781176299988144710210121 1335882224991108532657591)
                ·
                  refine ⟨2003823337486662798986387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335882224991108532657591 2003823337486662798986387)
                  ·
                    refine ⟨3005735006229994198479581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2003823337486662798986387 3005735006229994198479581)
                    ·
                      refine ⟨1127150627336247824429843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005735006229994198479581 1127150627336247824429843)
                      ·
                        rfl

theorem cell23_2195118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_2195118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195118 prefixEnd_2195118 := by exact prefixLift 2195118
  have htrace : WordTrace (prefixWord ++ tailWord_2195118) baseStart_2195118 baseEnd_2195118 := by
    simpa [prefixWord, tailWord_2195118, baseEnd_2195118] using wordTrace_append hprefix tailTrace_2195118
  have hstable : (prefixWord ++ tailWord_2195118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195118).length < 2 ^ (prefixWord ++ tailWord_2195118).sum := by decide
  have hdescent : baseEnd_2195118 < baseStart_2195118 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195140 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2195140 : Nat := 118140960795 + 2195140 * 2 ^ 59
def prefixEnd_2195140 : Nat := 4983230072969 + 3 ^ 40 * 2195140 * 2
def baseEnd_2195140 : Nat := 1127161923910646738354741

theorem tailTrace_2195140 : CollatzResearch.WordTrace tailWord_2195140 prefixEnd_2195140 1127161923910646738354741 := by
  unfold tailWord_2195140
  simp only [CollatzResearch.WordTrace]
  refine ⟨40031666633695077454895437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53375555511593436606527249 40031666633695077454895437)
  ·
    refine ⟨15011874987635654045585789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40031666633695077454895437 15011874987635654045585789)
    ·
      refine ⟨5629453120363370267094671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15011874987635654045585789 5629453120363370267094671)
      ·
        refine ⟨8444179680545055400642007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5629453120363370267094671 8444179680545055400642007)
        ·
          refine ⟨12666269520817583100963011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8444179680545055400642007 12666269520817583100963011)
          ·
            refine ⟨18999404281226374651444517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12666269520817583100963011 18999404281226374651444517)
            ·
              refine ⟨3562388302729945247145847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18999404281226374651444517 3562388302729945247145847)
              ·
                refine ⟨5343582454094917870718771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562388302729945247145847 5343582454094917870718771)
                ·
                  refine ⟨8015373681142376806078157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5343582454094917870718771 8015373681142376806078157)
                  ·
                    refine ⟨3005765130428391302279309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8015373681142376806078157 3005765130428391302279309)
                    ·
                      refine ⟨1127161923910646738354741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005765130428391302279309 1127161923910646738354741)
                      ·
                        rfl

theorem cell23_2195140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2195140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195140 prefixEnd_2195140 := by exact prefixLift 2195140
  have htrace : WordTrace (prefixWord ++ tailWord_2195140) baseStart_2195140 baseEnd_2195140 := by
    simpa [prefixWord, tailWord_2195140, baseEnd_2195140] using wordTrace_append hprefix tailTrace_2195140
  have hstable : (prefixWord ++ tailWord_2195140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195140).length < 2 ^ (prefixWord ++ tailWord_2195140).sum := by decide
  have hdescent : baseEnd_2195140 < baseStart_2195140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195150 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2]
def baseStart_2195150 : Nat := 118140960795 + 2195150 * 2 ^ 59
def prefixEnd_2195150 : Nat := 4983230072969 + 3 ^ 40 * 2195150 * 2
def baseEnd_2195150 : Nat := 1127167058717191699229695

theorem tailTrace_2195150 : CollatzResearch.WordTrace tailWord_2195150 prefixEnd_2195150 1127167058717191699229695 := by
  unfold tailWord_2195150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10007962249669240827206863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53375798664902617745103269 10007962249669240827206863)
  ·
    refine ⟨15011943374503861240810295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10007962249669240827206863 15011943374503861240810295)
    ·
      refine ⟨22517915061755791861215443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15011943374503861240810295 22517915061755791861215443)
      ·
        refine ⟨33776872592633687791823165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22517915061755791861215443 33776872592633687791823165)
        ·
          refine ⟨12666327222237632921933687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33776872592633687791823165 12666327222237632921933687)
          ·
            refine ⟨18999490833356449382900531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12666327222237632921933687 18999490833356449382900531)
            ·
              refine ⟨28499236250034674074350797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18999490833356449382900531 28499236250034674074350797)
              ·
                refine ⟨10687213593763002777881549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28499236250034674074350797 10687213593763002777881549)
                ·
                  refine ⟨4007705097661126041705581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10687213593763002777881549 4007705097661126041705581)
                  ·
                    refine ⟨1502889411622922265639593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4007705097661126041705581 1502889411622922265639593)
                    ·
                      refine ⟨1127167058717191699229695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1502889411622922265639593 1127167058717191699229695)
                      ·
                        rfl

theorem cell23_2195150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2].length) (baseStart_2195150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195150 prefixEnd_2195150 := by exact prefixLift 2195150
  have htrace : WordTrace (prefixWord ++ tailWord_2195150) baseStart_2195150 baseEnd_2195150 := by
    simpa [prefixWord, tailWord_2195150, baseEnd_2195150] using wordTrace_append hprefix tailTrace_2195150
  have hstable : (prefixWord ++ tailWord_2195150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195150).length < 2 ^ (prefixWord ++ tailWord_2195150).sum := by decide
  have hdescent : baseEnd_2195150 < baseStart_2195150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195158 : List Nat := [5, 2, 1, 3, 2, 1, 2, 1, 1, 1, 4]
def baseStart_2195158 : Nat := 118140960795 + 2195158 * 2 ^ 59
def prefixEnd_2195158 : Nat := 4983230072969 + 3 ^ 40 * 2195158 * 2
def baseEnd_2195158 : Nat := 1127171166562427667929659

theorem tailTrace_2195158 : CollatzResearch.WordTrace tailWord_2195158 prefixEnd_2195158 1127171166562427667929659 := by
  unfold tailWord_2195158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003999361332808998996633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53375993187549962655964085 5003999361332808998996633)
  ·
    refine ⟨3752999520999606749247475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5003999361332808998996633 3752999520999606749247475)
    ·
      refine ⟨5629499281499410123871213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3752999520999606749247475 5629499281499410123871213)
      ·
        refine ⟨2111062230562278796451705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5629499281499410123871213 2111062230562278796451705)
        ·
          refine ⟨1583296672921709097338779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2111062230562278796451705 1583296672921709097338779)
          ·
            refine ⟨2374945009382563646008169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583296672921709097338779 2374945009382563646008169)
            ·
              refine ⟨1781208757036922734506127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2374945009382563646008169 1781208757036922734506127)
              ·
                refine ⟨2671813135555384101759191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781208757036922734506127 2671813135555384101759191)
                ·
                  refine ⟨4007719703333076152638787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2671813135555384101759191 4007719703333076152638787)
                  ·
                    refine ⟨6011579554999614228958181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4007719703333076152638787 6011579554999614228958181)
                    ·
                      refine ⟨1127171166562427667929659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6011579554999614228958181 1127171166562427667929659)
                      ·
                        rfl

theorem cell23_2195158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_2195158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195158 prefixEnd_2195158 := by exact prefixLift 2195158
  have htrace : WordTrace (prefixWord ++ tailWord_2195158) baseStart_2195158 baseEnd_2195158 := by
    simpa [prefixWord, tailWord_2195158, baseEnd_2195158] using wordTrace_append hprefix tailTrace_2195158
  have hstable : (prefixWord ++ tailWord_2195158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195158).length < 2 ^ (prefixWord ++ tailWord_2195158).sum := by decide
  have hdescent : baseEnd_2195158 < baseStart_2195158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195233 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 4, 5]
def baseStart_2195233 : Nat := 118140960795 + 2195233 * 2 ^ 59
def prefixEnd_2195233 : Nat := 4983230072969 + 3 ^ 40 * 2195233 * 2
def baseEnd_2195233 : Nat := 375736559203838291497271

theorem tailTrace_2195233 : CollatzResearch.WordTrace tailWord_2195233 prefixEnd_2195233 375736559203838291497271 := by
  unfold tailWord_2195233
  simp only [CollatzResearch.WordTrace]
  refine ⟨80066725256053231792926353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53377816837368821195284235 80066725256053231792926353)
  ·
    refine ⟨60050043942039923844694765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80066725256053231792926353 60050043942039923844694765)
    ·
      refine ⟨22518766478264971441760537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60050043942039923844694765 22518766478264971441760537)
      ·
        refine ⟨16889074858698728581320403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22518766478264971441760537 16889074858698728581320403)
        ·
          refine ⟨25333612288048092871980605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16889074858698728581320403 25333612288048092871980605)
          ·
            refine ⟨9500104608018034826992727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25333612288048092871980605 9500104608018034826992727)
            ·
              refine ⟨14250156912027052240489091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9500104608018034826992727 14250156912027052240489091)
              ·
                refine ⟨21375235368040578360733637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14250156912027052240489091 21375235368040578360733637)
                ·
                  refine ⟨4007856631507608442637557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21375235368040578360733637 4007856631507608442637557)
                  ·
                    refine ⟨375736559203838291497271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4007856631507608442637557 375736559203838291497271)
                    ·
                      rfl

theorem cell23_2195233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 5].length) (baseStart_2195233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195233 prefixEnd_2195233 := by exact prefixLift 2195233
  have htrace : WordTrace (prefixWord ++ tailWord_2195233) baseStart_2195233 baseEnd_2195233 := by
    simpa [prefixWord, tailWord_2195233, baseEnd_2195233] using wordTrace_append hprefix tailTrace_2195233
  have hstable : (prefixWord ++ tailWord_2195233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195233).length < 2 ^ (prefixWord ++ tailWord_2195233).sum := by decide
  have hdescent : baseEnd_2195233 < baseStart_2195233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195237 : List Nat := [1, 3, 1, 2, 3, 3, 3, 2, 5]
def baseStart_2195237 : Nat := 118140960795 + 2195237 * 2 ^ 59
def prefixEnd_2195237 : Nat := 4983230072969 + 3 ^ 40 * 2195237 * 2
def baseEnd_2195237 : Nat := 125245747948236984315755

theorem tailTrace_2195237 : CollatzResearch.WordTrace tailWord_2195237 prefixEnd_2195237 125245747948236984315755 := by
  unfold tailWord_2195237
  simp only [CollatzResearch.WordTrace]
  refine ⟨80066871148038740476071965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53377914098692493650714643 80066871148038740476071965)
  ·
    refine ⟨30025076680514527678526987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80066871148038740476071965 30025076680514527678526987)
    ·
      refine ⟨45037615020771791517790481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30025076680514527678526987 45037615020771791517790481)
      ·
        refine ⟨33778211265578843638342861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45037615020771791517790481 33778211265578843638342861)
        ·
          refine ⟨12666829224592066364378573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33778211265578843638342861 12666829224592066364378573)
          ·
            refine ⟨4750060959222024886641965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12666829224592066364378573 4750060959222024886641965)
            ·
              refine ⟨1781272859708259332490737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4750060959222024886641965 1781272859708259332490737)
              ·
                refine ⟨1335954644781194499368053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781272859708259332490737 1335954644781194499368053)
                ·
                  refine ⟨125245747948236984315755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1335954644781194499368053 125245747948236984315755)
                  ·
                    rfl

theorem cell23_2195237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_2195237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195237 prefixEnd_2195237 := by exact prefixLift 2195237
  have htrace : WordTrace (prefixWord ++ tailWord_2195237) baseStart_2195237 baseEnd_2195237 := by
    simpa [prefixWord, tailWord_2195237, baseEnd_2195237] using wordTrace_append hprefix tailTrace_2195237
  have hstable : (prefixWord ++ tailWord_2195237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195237).length < 2 ^ (prefixWord ++ tailWord_2195237).sum := by decide
  have hdescent : baseEnd_2195237 < baseStart_2195237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195290 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3]
def baseStart_2195290 : Nat := 118140960795 + 2195290 * 2 ^ 59
def prefixEnd_2195290 : Nat := 4983230072969 + 3 ^ 40 * 2195290 * 2
def baseEnd_2195290 : Nat := 1127238946008821151479051

theorem tailTrace_2195290 : CollatzResearch.WordTrace tailWord_2195290 prefixEnd_2195290 1127238946008821151479051 := by
  unfold tailWord_2195290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20017201054211682631937831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53379202811231153685167549 20017201054211682631937831)
  ·
    refine ⟨30025801581317523947906747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20017201054211682631937831 30025801581317523947906747)
    ·
      refine ⟨45038702371976285921860121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30025801581317523947906747 45038702371976285921860121)
      ·
        refine ⟨33779026778982214441395091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45038702371976285921860121 33779026778982214441395091)
        ·
          refine ⟨50668540168473321662092637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33779026778982214441395091 50668540168473321662092637)
          ·
            refine ⟨19000702563177495623284739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50668540168473321662092637 19000702563177495623284739)
            ·
              refine ⟨28501053844766243434927109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19000702563177495623284739 28501053844766243434927109)
              ·
                refine ⟨5343947595893670644048833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28501053844766243434927109 5343947595893670644048833)
                ·
                  refine ⟨4007960696920252983036625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5343947595893670644048833 4007960696920252983036625)
                  ·
                    refine ⟨3005970522690189737277469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4007960696920252983036625 3005970522690189737277469)
                    ·
                      refine ⟨1127238946008821151479051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3005970522690189737277469 1127238946008821151479051)
                      ·
                        rfl

theorem cell23_2195290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 2, 3].length) (baseStart_2195290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195290 prefixEnd_2195290 := by exact prefixLift 2195290
  have htrace : WordTrace (prefixWord ++ tailWord_2195290) baseStart_2195290 baseEnd_2195290 := by
    simpa [prefixWord, tailWord_2195290, baseEnd_2195290] using wordTrace_append hprefix tailTrace_2195290
  have hstable : (prefixWord ++ tailWord_2195290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195290).length < 2 ^ (prefixWord ++ tailWord_2195290).sum := by decide
  have hdescent : baseEnd_2195290 < baseStart_2195290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195297 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2195297 : Nat := 118140960795 + 2195297 * 2 ^ 59
def prefixEnd_2195297 : Nat := 4983230072969 + 3 ^ 40 * 2195297 * 2
def baseEnd_2195297 : Nat := 375747513457800874697173

theorem tailTrace_2195297 : CollatzResearch.WordTrace tailWord_2195297 prefixEnd_2195297 375747513457800874697173 := by
  unfold tailWord_2195297
  simp only [CollatzResearch.WordTrace]
  refine ⟨80069059527821370723256145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53379373018547580482170763 80069059527821370723256145)
  ·
    refine ⟨60051794645866028042442109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80069059527821370723256145 60051794645866028042442109)
    ·
      refine ⟨22519422992199760515915791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60051794645866028042442109 22519422992199760515915791)
      ·
        refine ⟨33779134488299640773873687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22519422992199760515915791 33779134488299640773873687)
        ·
          refine ⟨50668701732449461160810531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33779134488299640773873687 50668701732449461160810531)
          ·
            refine ⟨76003052598674191741215797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50668701732449461160810531 76003052598674191741215797)
            ·
              refine ⟨7125286181125705475738981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76003052598674191741215797 7125286181125705475738981)
              ·
                refine ⟨1335991158961069776701059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7125286181125705475738981 1335991158961069776701059)
                ·
                  refine ⟨2003986738441604665051589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1335991158961069776701059 2003986738441604665051589)
                  ·
                    refine ⟨375747513457800874697173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2003986738441604665051589 375747513457800874697173)
                    ·
                      rfl

theorem cell23_2195297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2195297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195297 prefixEnd_2195297 := by exact prefixLift 2195297
  have htrace : WordTrace (prefixWord ++ tailWord_2195297) baseStart_2195297 baseEnd_2195297 := by
    simpa [prefixWord, tailWord_2195297, baseEnd_2195297] using wordTrace_append hprefix tailTrace_2195297
  have hstable : (prefixWord ++ tailWord_2195297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195297).length < 2 ^ (prefixWord ++ tailWord_2195297).sum := by decide
  have hdescent : baseEnd_2195297 < baseStart_2195297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195353 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 3, 6]
def baseStart_2195353 : Nat := 118140960795 + 2195353 * 2 ^ 59
def prefixEnd_2195353 : Nat := 4983230072969 + 3 ^ 40 * 2195353 * 2
def baseEnd_2195353 : Nat := 375757098430018134997087

theorem tailTrace_2195353 : CollatzResearch.WordTrace tailWord_2195353 prefixEnd_2195353 375757098430018134997087 := by
  unfold tailWord_2195353
  simp only [CollatzResearch.WordTrace]
  refine ⟨80071102015618492287294713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53380734677078994858196475 80071102015618492287294713)
  ·
    refine ⟨60053326511713869215471035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80071102015618492287294713 60053326511713869215471035)
    ·
      refine ⟨90079989767570803823206553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60053326511713869215471035 90079989767570803823206553)
      ·
        refine ⟨67559992325678102867404915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90079989767570803823206553 67559992325678102867404915)
        ·
          refine ⟨101339988488517154301107373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67559992325678102867404915 101339988488517154301107373)
          ·
            refine ⟨38002495683193932862915265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101339988488517154301107373 38002495683193932862915265)
            ·
              refine ⟨28501871762395449647186449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38002495683193932862915265 28501871762395449647186449)
              ·
                refine ⟨21376403821796587235389837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28501871762395449647186449 21376403821796587235389837)
                ·
                  refine ⟨8016151433173720213271189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21376403821796587235389837 8016151433173720213271189)
                  ·
                    refine ⟨375757098430018134997087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8016151433173720213271189 375757098430018134997087)
                    ·
                      rfl

theorem cell23_2195353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 6].length) (baseStart_2195353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195353 prefixEnd_2195353 := by exact prefixLift 2195353
  have htrace : WordTrace (prefixWord ++ tailWord_2195353) baseStart_2195353 baseEnd_2195353 := by
    simpa [prefixWord, tailWord_2195353, baseEnd_2195353] using wordTrace_append hprefix tailTrace_2195353
  have hstable : (prefixWord ++ tailWord_2195353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195353).length < 2 ^ (prefixWord ++ tailWord_2195353).sum := by decide
  have hdescent : baseEnd_2195353 < baseStart_2195353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195354 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3]
def baseStart_2195354 : Nat := 118140960795 + 2195354 * 2 ^ 59
def prefixEnd_2195354 : Nat := 4983230072969 + 3 ^ 40 * 2195354 * 2
def baseEnd_2195354 : Nat := 1127271808770708901078757

theorem tailTrace_2195354 : CollatzResearch.WordTrace tailWord_2195354 prefixEnd_2195354 1127271808770708901078757 := by
  unfold tailWord_2195354
  simp only [CollatzResearch.WordTrace]
  refine ⟨20017784622153717364520279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53380758992409912972054077 20017784622153717364520279)
  ·
    refine ⟨30026676933230576046780419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20017784622153717364520279 30026676933230576046780419)
    ·
      refine ⟨45040015399845864070170629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30026676933230576046780419 45040015399845864070170629)
      ·
        refine ⟨8445002887471099513156993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45040015399845864070170629 8445002887471099513156993)
        ·
          refine ⟨6333752165603324634867745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8445002887471099513156993 6333752165603324634867745)
          ·
            refine ⟨4750314124202493476150809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6333752165603324634867745 4750314124202493476150809)
            ·
              refine ⟨3562735593151870107113107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4750314124202493476150809 3562735593151870107113107)
              ·
                refine ⟨5344103389727805160669661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3562735593151870107113107 5344103389727805160669661)
                ·
                  refine ⟨2004038771147926935251123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5344103389727805160669661 2004038771147926935251123)
                  ·
                    refine ⟨3006058156721890402876685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2004038771147926935251123 3006058156721890402876685)
                    ·
                      refine ⟨1127271808770708901078757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006058156721890402876685 1127271808770708901078757)
                      ·
                        rfl

theorem cell23_2195354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_2195354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195354 prefixEnd_2195354 := by exact prefixLift 2195354
  have htrace : WordTrace (prefixWord ++ tailWord_2195354) baseStart_2195354 baseEnd_2195354 := by
    simpa [prefixWord, tailWord_2195354, baseEnd_2195354] using wordTrace_append hprefix tailTrace_2195354
  have hstable : (prefixWord ++ tailWord_2195354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195354).length < 2 ^ (prefixWord ++ tailWord_2195354).sum := by decide
  have hdescent : baseEnd_2195354 < baseStart_2195354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195377 : List Nat := [1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 4]
def baseStart_2195377 : Nat := 118140960795 + 2195377 * 2 ^ 59
def prefixEnd_2195377 : Nat := 4983230072969 + 3 ^ 40 * 2195377 * 2
def baseEnd_2195377 : Nat := 1127283618825762311091151

theorem tailTrace_2195377 : CollatzResearch.WordTrace tailWord_2195377 prefixEnd_2195377 1127283618825762311091151 := by
  unfold tailWord_2195377
  simp only [CollatzResearch.WordTrace]
  refine ⟨80071977367531544386168385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53381318245021029590778923 80071977367531544386168385)
  ·
    refine ⟨60053983025648658289626289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80071977367531544386168385 60053983025648658289626289)
    ·
      refine ⟨45040487269236493717219717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60053983025648658289626289 45040487269236493717219717)
      ·
        refine ⟨8445091362981842571978697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45040487269236493717219717 8445091362981842571978697)
        ·
          refine ⟨6333818522236381928984023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8445091362981842571978697 6333818522236381928984023)
          ·
            refine ⟨9500727783354572893476035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6333818522236381928984023 9500727783354572893476035)
            ·
              refine ⟨14251091675031859340214053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9500727783354572893476035 14251091675031859340214053)
              ·
                refine ⟨2672079689068473626290135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14251091675031859340214053 2672079689068473626290135)
                ·
                  refine ⟨4008119533602710439435203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672079689068473626290135 4008119533602710439435203)
                  ·
                    refine ⟨6012179300404065659152805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4008119533602710439435203 6012179300404065659152805)
                    ·
                      refine ⟨1127283618825762311091151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6012179300404065659152805 1127283618825762311091151)
                      ·
                        rfl

theorem cell23_2195377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_2195377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195377 prefixEnd_2195377 := by exact prefixLift 2195377
  have htrace : WordTrace (prefixWord ++ tailWord_2195377) baseStart_2195377 baseEnd_2195377 := by
    simpa [prefixWord, tailWord_2195377, baseEnd_2195377] using wordTrace_append hprefix tailTrace_2195377
  have hstable : (prefixWord ++ tailWord_2195377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195377).length < 2 ^ (prefixWord ++ tailWord_2195377).sum := by decide
  have hdescent : baseEnd_2195377 < baseStart_2195377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195400 : List Nat := [2, 1, 3, 1, 4, 3, 9]
def baseStart_2195400 : Nat := 118140960795 + 2195400 * 2 ^ 59
def prefixEnd_2195400 : Nat := 4983230072969 + 3 ^ 40 * 2195400 * 2
def baseEnd_2195400 : Nat := 13917227517047107667945

theorem tailTrace_2195400 : CollatzResearch.WordTrace tailWord_2195400 prefixEnd_2195400 13917227517047107667945 := by
  unfold tailWord_2195400
  simp only [CollatzResearch.WordTrace]
  refine ⟨40036408123224109657127827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53381877497632146209503769 40036408123224109657127827)
  ·
    refine ⟨60054612184836164485691741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40036408123224109657127827 60054612184836164485691741)
    ·
      refine ⟨22520479569313561682134403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60054612184836164485691741 22520479569313561682134403)
      ·
        refine ⟨33780719353970342523201605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22520479569313561682134403 33780719353970342523201605)
        ·
          refine ⟨6333884878869439223100301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33780719353970342523201605 6333884878869439223100301)
          ·
            refine ⟨2375206829576039708662613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6333884878869439223100301 2375206829576039708662613)
            ·
              refine ⟨13917227517047107667945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2375206829576039708662613 13917227517047107667945)
              ·
                rfl

theorem cell23_2195400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 9].length) (baseStart_2195400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195400 prefixEnd_2195400 := by exact prefixLift 2195400
  have htrace : WordTrace (prefixWord ++ tailWord_2195400) baseStart_2195400 baseEnd_2195400 := by
    simpa [prefixWord, tailWord_2195400, baseEnd_2195400] using wordTrace_append hprefix tailTrace_2195400
  have hstable : (prefixWord ++ tailWord_2195400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195400).length < 2 ^ (prefixWord ++ tailWord_2195400).sum := by decide
  have hdescent : baseEnd_2195400 < baseStart_2195400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195431 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2195431 : Nat := 118140960795 + 2195431 * 2 ^ 59
def prefixEnd_2195431 : Nat := 4983230072969 + 3 ^ 40 * 2195431 * 2
def baseEnd_2195431 : Nat := 1127311346781105099815903

theorem tailTrace_2195431 : CollatzResearch.WordTrace tailWord_2195431 prefixEnd_2195431 1127311346781105099815903 := by
  unfold tailWord_2195431
  simp only [CollatzResearch.WordTrace]
  refine ⟨80073946909335911608634147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53382631272890607739089431 80073946909335911608634147)
  ·
    refine ⟨120110920364003867412951221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80073946909335911608634147 120110920364003867412951221)
    ·
      refine ⟨11260398784125362569964177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120110920364003867412951221 11260398784125362569964177)
      ·
        refine ⟨8445299088094021927473133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11260398784125362569964177 8445299088094021927473133)
        ·
          refine ⟨3166987158035258222802425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8445299088094021927473133 3166987158035258222802425)
          ·
            refine ⟨2375240368526443667101819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166987158035258222802425 2375240368526443667101819)
            ·
              refine ⟨3562860552789665500652729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375240368526443667101819 3562860552789665500652729)
              ·
                refine ⟨2672145414592249125489547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3562860552789665500652729 2672145414592249125489547)
                ·
                  refine ⟨4008218121888373688234321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672145414592249125489547 4008218121888373688234321)
                  ·
                    refine ⟨3006163591416280266175741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4008218121888373688234321 3006163591416280266175741)
                    ·
                      refine ⟨1127311346781105099815903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006163591416280266175741 1127311346781105099815903)
                      ·
                        rfl

theorem cell23_2195431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2195431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195431 prefixEnd_2195431 := by exact prefixLift 2195431
  have htrace : WordTrace (prefixWord ++ tailWord_2195431) baseStart_2195431 baseEnd_2195431 := by
    simpa [prefixWord, tailWord_2195431, baseEnd_2195431] using wordTrace_append hprefix tailTrace_2195431
  have hstable : (prefixWord ++ tailWord_2195431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195431).length < 2 ^ (prefixWord ++ tailWord_2195431).sum := by decide
  have hdescent : baseEnd_2195431 < baseStart_2195431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195467 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 3, 4, 2]
def baseStart_2195467 : Nat := 118140960795 + 2195467 * 2 ^ 59
def prefixEnd_2195467 : Nat := 4983230072969 + 3 ^ 40 * 2195467 * 2
def baseEnd_2195467 : Nat := 1127329832084666958965737

theorem tailTrace_2195467 : CollatzResearch.WordTrace tailWord_2195467 prefixEnd_2195467 1127329832084666958965737 := by
  unfold tailWord_2195467
  simp only [CollatzResearch.WordTrace]
  refine ⟨80075259937205489756944655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53383506624803659837963103 80075259937205489756944655)
  ·
    refine ⟨120112889905808234635416983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80075259937205489756944655 120112889905808234635416983)
    ·
      refine ⟨180169334858712351953125475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120112889905808234635416983 180169334858712351953125475)
      ·
        refine ⟨270254002288068527929688213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180169334858712351953125475 270254002288068527929688213)
        ·
          refine ⟨12668156357253212246704135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 270254002288068527929688213 12668156357253212246704135)
          ·
            refine ⟨19002234535879818370056203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12668156357253212246704135 19002234535879818370056203)
            ·
              refine ⟨28503351803819727555084305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19002234535879818370056203 28503351803819727555084305)
              ·
                refine ⟨21377513852864795666313229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28503351803819727555084305 21377513852864795666313229)
                ·
                  refine ⟨8016567694824298374867461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21377513852864795666313229 8016567694824298374867461)
                  ·
                    refine ⟨1503106442779555945287649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8016567694824298374867461 1503106442779555945287649)
                    ·
                      refine ⟨1127329832084666958965737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503106442779555945287649 1127329832084666958965737)
                      ·
                        rfl

theorem cell23_2195467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 3, 4, 2].length) (baseStart_2195467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195467 prefixEnd_2195467 := by exact prefixLift 2195467
  have htrace : WordTrace (prefixWord ++ tailWord_2195467) baseStart_2195467 baseEnd_2195467 := by
    simpa [prefixWord, tailWord_2195467, baseEnd_2195467] using wordTrace_append hprefix tailTrace_2195467
  have hstable : (prefixWord ++ tailWord_2195467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195467).length < 2 ^ (prefixWord ++ tailWord_2195467).sum := by decide
  have hdescent : baseEnd_2195467 < baseStart_2195467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195477 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_2195477 : Nat := 118140960795 + 2195477 * 2 ^ 59
def prefixEnd_2195477 : Nat := 4983230072969 + 3 ^ 40 * 2195477 * 2
def baseEnd_2195477 : Nat := 375778322297070639946897

theorem tailTrace_2195477 : CollatzResearch.WordTrace tailWord_2195477 prefixEnd_2195477 375778322297070639946897 := by
  unfold tailWord_2195477
  simp only [CollatzResearch.WordTrace]
  refine ⟨80075624667169261464808685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53383749778112840976539123 80075624667169261464808685)
  ·
    refine ⟨30028359250188473049303257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80075624667169261464808685 30028359250188473049303257)
    ·
      refine ⟨22521269437641354786977443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30028359250188473049303257 22521269437641354786977443)
      ·
        refine ⟨33781904156462032180466165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22521269437641354786977443 33781904156462032180466165)
        ·
          refine ⟨3167053514668315516918703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33781904156462032180466165 3167053514668315516918703)
          ·
            refine ⟨4750580272002473275378055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167053514668315516918703 4750580272002473275378055)
            ·
              refine ⟨7125870408003709913067083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750580272002473275378055 7125870408003709913067083)
              ·
                refine ⟨10688805612005564869600625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7125870408003709913067083 10688805612005564869600625)
                ·
                  refine ⟨8016604209004173652200469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10688805612005564869600625 8016604209004173652200469)
                  ·
                    refine ⟨375778322297070639946897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8016604209004173652200469 375778322297070639946897)
                    ·
                      rfl

theorem cell23_2195477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_2195477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195477 prefixEnd_2195477 := by exact prefixLift 2195477
  have htrace : WordTrace (prefixWord ++ tailWord_2195477) baseStart_2195477 baseEnd_2195477 := by
    simpa [prefixWord, tailWord_2195477, baseEnd_2195477] using wordTrace_append hprefix tailTrace_2195477
  have hstable : (prefixWord ++ tailWord_2195477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195477).length < 2 ^ (prefixWord ++ tailWord_2195477).sum := by decide
  have hdescent : baseEnd_2195477 < baseStart_2195477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195484 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 1, 4, 2]
def baseStart_2195484 : Nat := 118140960795 + 2195484 * 2 ^ 59
def prefixEnd_2195484 : Nat := 4983230072969 + 3 ^ 40 * 2195484 * 2
def baseEnd_2195484 : Nat := 1127338561255793392453159

theorem tailTrace_2195484 : CollatzResearch.WordTrace tailWord_2195484 prefixEnd_2195484 1127338561255793392453159 := by
  unfold tailWord_2195484
  simp only [CollatzResearch.WordTrace]
  refine ⟨40037939989071950830156753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53383919985429267773542337 40037939989071950830156753)
  ·
    refine ⟨30028454991803963122617565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40037939989071950830156753 30028454991803963122617565)
    ·
      refine ⟨11260670621926486170981587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30028454991803963122617565 11260670621926486170981587)
      ·
        refine ⟨16891005932889729256472381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11260670621926486170981587 16891005932889729256472381)
        ·
          refine ⟨6334127224833648471177143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16891005932889729256472381 6334127224833648471177143)
          ·
            refine ⟨9501190837250472706765715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334127224833648471177143 9501190837250472706765715)
            ·
              refine ⟨14251786255875709060148573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501190837250472706765715 14251786255875709060148573)
              ·
                refine ⟨5344419845953390897555715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14251786255875709060148573 5344419845953390897555715)
                ·
                  refine ⟨8016629768930086346333573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5344419845953390897555715 8016629768930086346333573)
                  ·
                    refine ⟨1503118081674391189937545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8016629768930086346333573 1503118081674391189937545)
                    ·
                      refine ⟨1127338561255793392453159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503118081674391189937545 1127338561255793392453159)
                      ·
                        rfl

theorem cell23_2195484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_2195484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195484 prefixEnd_2195484 := by exact prefixLift 2195484
  have htrace : WordTrace (prefixWord ++ tailWord_2195484) baseStart_2195484 baseEnd_2195484 := by
    simpa [prefixWord, tailWord_2195484, baseEnd_2195484] using wordTrace_append hprefix tailTrace_2195484
  have hstable : (prefixWord ++ tailWord_2195484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195484).length < 2 ^ (prefixWord ++ tailWord_2195484).sum := by decide
  have hdescent : baseEnd_2195484 < baseStart_2195484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195507 : List Nat := [1, 1, 1, 2, 4, 1, 3, 5, 5]
def baseStart_2195507 : Nat := 118140960795 + 2195507 * 2 ^ 59
def prefixEnd_2195507 : Nat := 4983230072969 + 3 ^ 40 * 2195507 * 2
def baseEnd_2195507 : Nat := 125261152367871866940617

theorem tailTrace_2195507 : CollatzResearch.WordTrace tailWord_2195507 prefixEnd_2195507 125261152367871866940617 := by
  unfold tailWord_2195507
  simp only [CollatzResearch.WordTrace]
  refine ⟨80076718857060576588400775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53384479238040384392267183 80076718857060576588400775)
  ·
    refine ⟨120115078285590864882601163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80076718857060576588400775 120115078285590864882601163)
    ·
      refine ⟨180172617428386297323901745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120115078285590864882601163 180172617428386297323901745)
      ·
        refine ⟨135129463071289722992926309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180172617428386297323901745 135129463071289722992926309)
        ·
          refine ⟨25336774325866823061173683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135129463071289722992926309 25336774325866823061173683)
          ·
            refine ⟨38005161488800234591760525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25336774325866823061173683 38005161488800234591760525)
            ·
              refine ⟨14251935558300087971910197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38005161488800234591760525 14251935558300087971910197)
              ·
                refine ⟨1336118958590633247366581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14251935558300087971910197 1336118958590633247366581)
                ·
                  refine ⟨125261152367871866940617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336118958590633247366581 125261152367871866940617)
                  ·
                    rfl

theorem cell23_2195507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 5, 5].length) (baseStart_2195507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195507 prefixEnd_2195507 := by exact prefixLift 2195507
  have htrace : WordTrace (prefixWord ++ tailWord_2195507) baseStart_2195507 baseEnd_2195507 := by
    simpa [prefixWord, tailWord_2195507, baseEnd_2195507] using wordTrace_append hprefix tailTrace_2195507
  have hstable : (prefixWord ++ tailWord_2195507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195507).length < 2 ^ (prefixWord ++ tailWord_2195507).sum := by decide
  have hdescent : baseEnd_2195507 < baseStart_2195507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195517 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2195517 : Nat := 118140960795 + 2195517 * 2 ^ 59
def prefixEnd_2195517 : Nat := 4983230072969 + 3 ^ 40 * 2195517 * 2
def baseEnd_2195517 : Nat := 1127355506117391763340507

theorem tailTrace_2195517 : CollatzResearch.WordTrace tailWord_2195517 prefixEnd_2195517 1127355506117391763340507 := by
  unfold tailWord_2195517
  simp only [CollatzResearch.WordTrace]
  refine ⟨80077083587024348296264805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53384722391349565530843203 80077083587024348296264805)
  ·
    refine ⟨15014453172567065305549651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80077083587024348296264805 15014453172567065305549651)
    ·
      refine ⟨22521679758850597958324477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15014453172567065305549651 22521679758850597958324477)
      ·
        refine ⟨8445629909568974234371679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22521679758850597958324477 8445629909568974234371679)
        ·
          refine ⟨12668444864353461351557519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8445629909568974234371679 12668444864353461351557519)
          ·
            refine ⟨19002667296530192027336279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12668444864353461351557519 19002667296530192027336279)
            ·
              refine ⟨28504000944795288041004419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19002667296530192027336279 28504000944795288041004419)
              ·
                refine ⟨42756001417192932061506629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28504000944795288041004419 42756001417192932061506629)
                ·
                  refine ⟨8016750265723674761532493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42756001417192932061506629 8016750265723674761532493)
                  ·
                    refine ⟨3006281349646378035574685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8016750265723674761532493 3006281349646378035574685)
                    ·
                      refine ⟨1127355506117391763340507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006281349646378035574685 1127355506117391763340507)
                      ·
                        rfl

theorem cell23_2195517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2195517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195517 prefixEnd_2195517 := by exact prefixLift 2195517
  have htrace : WordTrace (prefixWord ++ tailWord_2195517) baseStart_2195517 baseEnd_2195517 := by
    simpa [prefixWord, tailWord_2195517, baseEnd_2195517] using wordTrace_append hprefix tailTrace_2195517
  have hstable : (prefixWord ++ tailWord_2195517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195517).length < 2 ^ (prefixWord ++ tailWord_2195517).sum := by decide
  have hdescent : baseEnd_2195517 < baseStart_2195517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195518 : List Nat := [4, 2, 1, 3, 2, 1, 1, 1, 4, 2, 2]
def baseStart_2195518 : Nat := 118140960795 + 2195518 * 2 ^ 59
def prefixEnd_2195518 : Nat := 4983230072969 + 3 ^ 40 * 2195518 * 2
def baseEnd_2195518 : Nat := 1127356019598046259428003

theorem tailTrace_2195518 : CollatzResearch.WordTrace tailWord_2195518 prefixEnd_2195518 1127356019598046259428003 := by
  unfold tailWord_2195518
  simp only [CollatzResearch.WordTrace]
  refine ⟨10009640007502590683381401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53384746706680483644700805 10009640007502590683381401)
  ·
    refine ⟨7507230005626943012536051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10009640007502590683381401 7507230005626943012536051)
    ·
      refine ⟨11260845008440414518804077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7507230005626943012536051 11260845008440414518804077)
      ·
        refine ⟨4222816878165155444551529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11260845008440414518804077 4222816878165155444551529)
        ·
          refine ⟨3167112658623866583413647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4222816878165155444551529 3167112658623866583413647)
          ·
            refine ⟨4750668987935799875120471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167112658623866583413647 4750668987935799875120471)
            ·
              refine ⟨7126003481903699812680707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4750668987935799875120471 7126003481903699812680707)
              ·
                refine ⟨10689005222855549719021061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126003481903699812680707 10689005222855549719021061)
                ·
                  refine ⟨2004188479285415572316449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10689005222855549719021061 2004188479285415572316449)
                  ·
                    refine ⟨1503141359464061679237337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2004188479285415572316449 1503141359464061679237337)
                    ·
                      refine ⟨1127356019598046259428003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503141359464061679237337 1127356019598046259428003)
                      ·
                        rfl

theorem cell23_2195518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_2195518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195518 prefixEnd_2195518 := by exact prefixLift 2195518
  have htrace : WordTrace (prefixWord ++ tailWord_2195518) baseStart_2195518 baseEnd_2195518 := by
    simpa [prefixWord, tailWord_2195518, baseEnd_2195518] using wordTrace_append hprefix tailTrace_2195518
  have hstable : (prefixWord ++ tailWord_2195518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195518).length < 2 ^ (prefixWord ++ tailWord_2195518).sum := by decide
  have hdescent : baseEnd_2195518 < baseStart_2195518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195530 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_2195530 : Nat := 118140960795 + 2195530 * 2 ^ 59
def prefixEnd_2195530 : Nat := 4983230072969 + 3 ^ 40 * 2195530 * 2
def baseEnd_2195530 : Nat := 1127362181365900212477947

theorem tailTrace_2195530 : CollatzResearch.WordTrace tailWord_2195530 prefixEnd_2195530 1127362181365900212477947 := by
  unfold tailWord_2195530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20019389433994312879122011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53385038490651501010992029 20019389433994312879122011)
  ·
    refine ⟨30029084150991469318683017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20019389433994312879122011 30029084150991469318683017)
    ·
      refine ⟨22521813113243601989012263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30029084150991469318683017 22521813113243601989012263)
      ·
        refine ⟨33782719669865402983518395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22521813113243601989012263 33782719669865402983518395)
        ·
          refine ⟨50674079504798104475277593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33782719669865402983518395 50674079504798104475277593)
          ·
            refine ⟨38005559628598578356458195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50674079504798104475277593 38005559628598578356458195)
            ·
              refine ⟨57008339442897867534687293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38005559628598578356458195 57008339442897867534687293)
              ·
                refine ⟨21378127291086700325507735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57008339442897867534687293 21378127291086700325507735)
                ·
                  refine ⟨32067190936630050488261603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21378127291086700325507735 32067190936630050488261603)
                  ·
                    refine ⟨48100786404945075732392405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32067190936630050488261603 48100786404945075732392405)
                    ·
                      refine ⟨1127362181365900212477947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48100786404945075732392405 1127362181365900212477947)
                      ·
                        rfl

theorem cell23_2195530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_2195530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195530 prefixEnd_2195530 := by exact prefixLift 2195530
  have htrace : WordTrace (prefixWord ++ tailWord_2195530) baseStart_2195530 baseEnd_2195530 := by
    simpa [prefixWord, tailWord_2195530, baseEnd_2195530] using wordTrace_append hprefix tailTrace_2195530
  have hstable : (prefixWord ++ tailWord_2195530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195530).length < 2 ^ (prefixWord ++ tailWord_2195530).sum := by decide
  have hdescent : baseEnd_2195530 < baseStart_2195530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195557 : List Nat := [1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2195557 : Nat := 118140960795 + 2195557 * 2 ^ 59
def prefixEnd_2195557 : Nat := 4983230072969 + 3 ^ 40 * 2195557 * 2
def baseEnd_2195557 : Nat := 1127376045343571606840323

theorem tailTrace_2195557 : CollatzResearch.WordTrace tailWord_2195557 prefixEnd_2195557 1127376045343571606840323 := by
  unfold tailWord_2195557
  simp only [CollatzResearch.WordTrace]
  refine ⟨80078542506879435127720925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53385695004586290085147283 80078542506879435127720925)
  ·
    refine ⟨30029453440079788172895347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80078542506879435127720925 30029453440079788172895347)
    ·
      refine ⟨45044180160119682259343021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30029453440079788172895347 45044180160119682259343021)
      ·
        refine ⟨16891567560044880847253633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45044180160119682259343021 16891567560044880847253633)
        ·
          refine ⟨12668675670033660635440225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16891567560044880847253633 12668675670033660635440225)
          ·
            refine ⟨9501506752525245476580169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12668675670033660635440225 9501506752525245476580169)
            ·
              refine ⟨7126130064393934107435127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9501506752525245476580169 7126130064393934107435127)
              ·
                refine ⟨10689195096590901161152691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126130064393934107435127 10689195096590901161152691)
                ·
                  refine ⟨16033792644886351741729037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10689195096590901161152691 16033792644886351741729037)
                  ·
                    refine ⟨6012672241832381903148389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16033792644886351741729037 6012672241832381903148389)
                    ·
                      refine ⟨1127376045343571606840323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6012672241832381903148389 1127376045343571606840323)
                      ·
                        rfl

theorem cell23_2195557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2195557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195557 prefixEnd_2195557 := by exact prefixLift 2195557
  have htrace : WordTrace (prefixWord ++ tailWord_2195557) baseStart_2195557 baseEnd_2195557 := by
    simpa [prefixWord, tailWord_2195557, baseEnd_2195557] using wordTrace_append hprefix tailTrace_2195557
  have hstable : (prefixWord ++ tailWord_2195557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195557).length < 2 ^ (prefixWord ++ tailWord_2195557).sum := by decide
  have hdescent : baseEnd_2195557 < baseStart_2195557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195574 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4]
def baseStart_2195574 : Nat := 118140960795 + 2195574 * 2 ^ 59
def prefixEnd_2195574 : Nat := 4983230072969 + 3 ^ 40 * 2195574 * 2
def baseEnd_2195574 : Nat := 1127384774514698040327745

theorem tailTrace_2195574 : CollatzResearch.WordTrace tailWord_2195574 prefixEnd_2195574 1127384774514698040327745 := by
  unfold tailWord_2195574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004947659238615439443111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53386108365211898020726517 5004947659238615439443111)
  ·
    refine ⟨7507421488857923159164667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004947659238615439443111 7507421488857923159164667)
    ·
      refine ⟨11261132233286884738747001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7507421488857923159164667 11261132233286884738747001)
      ·
        refine ⟨8445849174965163554060251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11261132233286884738747001 8445849174965163554060251)
        ·
          refine ⟨12668773762447745331090377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8445849174965163554060251 12668773762447745331090377)
          ·
            refine ⟨9501580321835808998317783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12668773762447745331090377 9501580321835808998317783)
            ·
              refine ⟨14252370482753713497476675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9501580321835808998317783 14252370482753713497476675)
              ·
                refine ⟨21378555724130570246215013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14252370482753713497476675 21378555724130570246215013)
                ·
                  refine ⟨4008479198274481921165315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21378555724130570246215013 4008479198274481921165315)
                  ·
                    refine ⟨6012718797411722881747973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4008479198274481921165315 6012718797411722881747973)
                    ·
                      refine ⟨1127384774514698040327745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6012718797411722881747973 1127384774514698040327745)
                      ·
                        rfl

theorem cell23_2195574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_2195574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195574 prefixEnd_2195574 := by exact prefixLift 2195574
  have htrace : WordTrace (prefixWord ++ tailWord_2195574) baseStart_2195574 baseEnd_2195574 := by
    simpa [prefixWord, tailWord_2195574, baseEnd_2195574] using wordTrace_append hprefix tailTrace_2195574
  have hstable : (prefixWord ++ tailWord_2195574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195574).length < 2 ^ (prefixWord ++ tailWord_2195574).sum := by decide
  have hdescent : baseEnd_2195574 < baseStart_2195574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195681 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 5, 2, 2]
def baseStart_2195681 : Nat := 118140960795 + 2195681 * 2 ^ 59
def prefixEnd_2195681 : Nat := 4983230072969 + 3 ^ 40 * 2195681 * 2
def baseEnd_2195681 : Nat := 1127439716944729121689753

theorem tailTrace_2195681 : CollatzResearch.WordTrace tailWord_2195681 prefixEnd_2195681 1127439716944729121689753 := by
  unfold tailWord_2195681
  simp only [CollatzResearch.WordTrace]
  refine ⟨80083065158430204305234897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53388710105620136203489931 80083065158430204305234897)
  ·
    refine ⟨60062298868822653228926173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80083065158430204305234897 60062298868822653228926173)
    ·
      refine ⟨22523362075808494960847315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60062298868822653228926173 22523362075808494960847315)
      ·
        refine ⟨33785043113712742441270973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22523362075808494960847315 33785043113712742441270973)
        ·
          refine ⟨12669391167642278415476615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33785043113712742441270973 12669391167642278415476615)
          ·
            refine ⟨19004086751463417623214923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12669391167642278415476615 19004086751463417623214923)
            ·
              refine ⟨28506130127195126434822385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19004086751463417623214923 28506130127195126434822385)
              ·
                refine ⟨21379597595396344826116789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28506130127195126434822385 21379597595396344826116789)
                ·
                  refine ⟨2004337274568407327448449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21379597595396344826116789 2004337274568407327448449)
                  ·
                    refine ⟨1503252955926305495586337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2004337274568407327448449 1503252955926305495586337)
                    ·
                      refine ⟨1127439716944729121689753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503252955926305495586337 1127439716944729121689753)
                      ·
                        rfl

theorem cell23_2195681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_2195681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195681 prefixEnd_2195681 := by exact prefixLift 2195681
  have htrace : WordTrace (prefixWord ++ tailWord_2195681) baseStart_2195681 baseEnd_2195681 := by
    simpa [prefixWord, tailWord_2195681, baseEnd_2195681] using wordTrace_append hprefix tailTrace_2195681
  have hstable : (prefixWord ++ tailWord_2195681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195681).length < 2 ^ (prefixWord ++ tailWord_2195681).sum := by decide
  have hdescent : baseEnd_2195681 < baseStart_2195681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195682 : List Nat := [3, 3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_2195682 : Nat := 118140960795 + 2195682 * 2 ^ 59
def prefixEnd_2195682 : Nat := 4983230072969 + 3 ^ 40 * 2195682 * 2
def baseEnd_2195682 : Nat := 125271136713931513086361

theorem tailTrace_2195682 : CollatzResearch.WordTrace tailWord_2195682 prefixEnd_2195682 125271136713931513086361 := by
  unfold tailWord_2195682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20020775407856645369005325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53388734420951054317347533 20020775407856645369005325)
  ·
    refine ⟨7507790777946242013376997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20020775407856645369005325 7507790777946242013376997)
    ·
      refine ⟨1407710770864920377508187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7507790777946242013376997 1407710770864920377508187)
      ·
        refine ⟨2111566156297380566262281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407710770864920377508187 2111566156297380566262281)
        ·
          refine ⟨1583674617223035424696711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2111566156297380566262281 1583674617223035424696711)
          ·
            refine ⟨2375511925834553137045067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1583674617223035424696711 2375511925834553137045067)
            ·
              refine ⟨3563267888751829705567601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375511925834553137045067 3563267888751829705567601)
              ·
                refine ⟨2672450916563872279175701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3563267888751829705567601 2672450916563872279175701)
                ·
                  refine ⟨125271136713931513086361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2672450916563872279175701 125271136713931513086361)
                  ·
                    rfl

theorem cell23_2195682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_2195682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195682 prefixEnd_2195682 := by exact prefixLift 2195682
  have htrace : WordTrace (prefixWord ++ tailWord_2195682) baseStart_2195682 baseEnd_2195682 := by
    simpa [prefixWord, tailWord_2195682, baseEnd_2195682] using wordTrace_append hprefix tailTrace_2195682
  have hstable : (prefixWord ++ tailWord_2195682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195682).length < 2 ^ (prefixWord ++ tailWord_2195682).sum := by decide
  have hdescent : baseEnd_2195682 < baseStart_2195682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195698 : List Nat := [3, 2, 1, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2195698 : Nat := 118140960795 + 2195698 * 2 ^ 59
def prefixEnd_2195698 : Nat := 4983230072969 + 3 ^ 40 * 2195698 * 2
def baseEnd_2195698 : Nat := 1127448446115855555177175

theorem tailTrace_2195698 : CollatzResearch.WordTrace tailWord_2195698 prefixEnd_2195698 1127448446115855555177175 := by
  unfold tailWord_2195698
  simp only [CollatzResearch.WordTrace]
  refine ⟨20020921299842154052150937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53389123466245744139069165 20020921299842154052150937)
  ·
    refine ⟨15015690974881615539113203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20020921299842154052150937 15015690974881615539113203)
    ·
      refine ⟨22523536462322423308669805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15015690974881615539113203 22523536462322423308669805)
      ·
        refine ⟨8446326173370908740751177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22523536462322423308669805 8446326173370908740751177)
        ·
          refine ⟨6334744630028181555563383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8446326173370908740751177 6334744630028181555563383)
          ·
            refine ⟨9502116945042272333345075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6334744630028181555563383 9502116945042272333345075)
            ·
              refine ⟨14253175417563408500017613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9502116945042272333345075 14253175417563408500017613)
              ·
                refine ⟨5344940781586278187506605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14253175417563408500017613 5344940781586278187506605)
                ·
                  refine ⟨2004352793094854320314977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5344940781586278187506605 2004352793094854320314977)
                  ·
                    refine ⟨1503264594821140740236233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2004352793094854320314977 1503264594821140740236233)
                    ·
                      refine ⟨1127448446115855555177175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503264594821140740236233 1127448446115855555177175)
                      ·
                        rfl

theorem cell23_2195698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2195698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195698 prefixEnd_2195698 := by exact prefixLift 2195698
  have htrace : WordTrace (prefixWord ++ tailWord_2195698) baseStart_2195698 baseEnd_2195698 := by
    simpa [prefixWord, tailWord_2195698, baseEnd_2195698] using wordTrace_append hprefix tailTrace_2195698
  have hstable : (prefixWord ++ tailWord_2195698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195698).length < 2 ^ (prefixWord ++ tailWord_2195698).sum := by decide
  have hdescent : baseEnd_2195698 < baseStart_2195698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195708 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_2195708 : Nat := 118140960795 + 2195708 * 2 ^ 59
def prefixEnd_2195708 : Nat := 4983230072969 + 3 ^ 40 * 2195708 * 2
def baseEnd_2195708 : Nat := 375817860307466838684043

theorem tailTrace_2195708 : CollatzResearch.WordTrace tailWord_2195708 prefixEnd_2195708 375817860307466838684043 := by
  unfold tailWord_2195708
  simp only [CollatzResearch.WordTrace]
  refine ⟨40042024964666193958233889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53389366619554925277645185 40042024964666193958233889)
  ·
    refine ⟨30031518723499645468675417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40042024964666193958233889 30031518723499645468675417)
    ·
      refine ⟨22523639042624734101506563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30031518723499645468675417 22523639042624734101506563)
      ·
        refine ⟨33785458563937101152259845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22523639042624734101506563 33785458563937101152259845)
        ·
          refine ⟨6334773480738206466048721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33785458563937101152259845 6334773480738206466048721)
          ·
            refine ⟨4751080110553654849536541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6334773480738206466048721 4751080110553654849536541)
            ·
              refine ⟨1781655041457620568576203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4751080110553654849536541 1781655041457620568576203)
              ·
                refine ⟨2672482562186430852864305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781655041457620568576203 2672482562186430852864305)
                ·
                  refine ⟨2004361921639823139648229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2672482562186430852864305 2004361921639823139648229)
                  ·
                    refine ⟨375817860307466838684043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2004361921639823139648229 375817860307466838684043)
                    ·
                      rfl

theorem cell23_2195708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_2195708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195708 prefixEnd_2195708 := by exact prefixLift 2195708
  have htrace : WordTrace (prefixWord ++ tailWord_2195708) baseStart_2195708 baseEnd_2195708 := by
    simpa [prefixWord, tailWord_2195708, baseEnd_2195708] using wordTrace_append hprefix tailTrace_2195708
  have hstable : (prefixWord ++ tailWord_2195708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195708).length < 2 ^ (prefixWord ++ tailWord_2195708).sum := by decide
  have hdescent : baseEnd_2195708 < baseStart_2195708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195767 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 6]
def baseStart_2195767 : Nat := 118140960795 + 2195767 * 2 ^ 59
def prefixEnd_2195767 : Nat := 4983230072969 + 3 ^ 40 * 2195767 * 2
def baseEnd_2195767 : Nat := 1127483876281015785214357

theorem tailTrace_2195767 : CollatzResearch.WordTrace tailWord_2195767 prefixEnd_2195767 1127483876281015785214357 := by
  unfold tailWord_2195767
  simp only [CollatzResearch.WordTrace]
  refine ⟨80086201836118640992865555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53390801224079093995243703 80086201836118640992865555)
  ·
    refine ⟨120129302754177961489298333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80086201836118640992865555 120129302754177961489298333)
    ·
      refine ⟨45048488532816735558486875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120129302754177961489298333 45048488532816735558486875)
      ·
        refine ⟨67572732799225103337730313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45048488532816735558486875 67572732799225103337730313)
        ·
          refine ⟨50679549599418827503297735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67572732799225103337730313 50679549599418827503297735)
          ·
            refine ⟨76019324399128241254946603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50679549599418827503297735 76019324399128241254946603)
            ·
              refine ⟨114028986598692361882419905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76019324399128241254946603 114028986598692361882419905)
              ·
                refine ⟨85521739949019271411814929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114028986598692361882419905 85521739949019271411814929)
                ·
                  refine ⟨64141304961764453558861197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85521739949019271411814929 64141304961764453558861197)
                  ·
                    refine ⟨24052989360661670084572949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64141304961764453558861197 24052989360661670084572949)
                    ·
                      refine ⟨1127483876281015785214357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24052989360661670084572949 1127483876281015785214357)
                      ·
                        rfl

theorem cell23_2195767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_2195767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195767 prefixEnd_2195767 := by exact prefixLift 2195767
  have htrace : WordTrace (prefixWord ++ tailWord_2195767) baseStart_2195767 baseEnd_2195767 := by
    simpa [prefixWord, tailWord_2195767, baseEnd_2195767] using wordTrace_append hprefix tailTrace_2195767
  have hstable : (prefixWord ++ tailWord_2195767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195767).length < 2 ^ (prefixWord ++ tailWord_2195767).sum := by decide
  have hdescent : baseEnd_2195767 < baseStart_2195767 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195787 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7]
def baseStart_2195787 : Nat := 118140960795 + 2195787 * 2 ^ 59
def prefixEnd_2195787 : Nat := 4983230072969 + 3 ^ 40 * 2195787 * 2
def baseEnd_2195787 : Nat := 1127494145894105706964265

theorem tailTrace_2195787 : CollatzResearch.WordTrace tailWord_2195787 prefixEnd_2195787 1127494145894105706964265 := by
  unfold tailWord_2195787
  simp only [CollatzResearch.WordTrace]
  refine ⟨80086931296046184408593615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53391287530697456272395743 80086931296046184408593615)
  ·
    refine ⟨120130396944069276612890423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80086931296046184408593615 120130396944069276612890423)
    ·
      refine ⟨180195595416103914919335635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120130396944069276612890423 180195595416103914919335635)
      ·
        refine ⟨270293393124155872379003453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180195595416103914919335635 270293393124155872379003453)
        ·
          refine ⟨101360022421558452142126295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270293393124155872379003453 101360022421558452142126295)
          ·
            refine ⟨152040033632337678213189443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101360022421558452142126295 152040033632337678213189443)
            ·
              refine ⟨228060050448506517319784165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152040033632337678213189443 228060050448506517319784165)
              ·
                refine ⟨42761259459094971997459531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 228060050448506517319784165 42761259459094971997459531)
                ·
                  refine ⟨64141889188642457996189297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42761259459094971997459531 64141889188642457996189297)
                  ·
                    refine ⟨48106416891481843497141973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64141889188642457996189297 48106416891481843497141973)
                    ·
                      refine ⟨1127494145894105706964265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48106416891481843497141973 1127494145894105706964265)
                      ·
                        rfl

theorem cell23_2195787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_2195787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195787 prefixEnd_2195787 := by exact prefixLift 2195787
  have htrace : WordTrace (prefixWord ++ tailWord_2195787) baseStart_2195787 baseEnd_2195787 := by
    simpa [prefixWord, tailWord_2195787, baseEnd_2195787] using wordTrace_append hprefix tailTrace_2195787
  have hstable : (prefixWord ++ tailWord_2195787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195787).length < 2 ^ (prefixWord ++ tailWord_2195787).sum := by decide
  have hdescent : baseEnd_2195787 < baseStart_2195787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195811 : List Nat := [1, 1, 1, 5, 2, 1, 3, 4, 5]
def baseStart_2195811 : Nat := 118140960795 + 2195811 * 2 ^ 59
def prefixEnd_2195811 : Nat := 4983230072969 + 3 ^ 40 * 2195811 * 2
def baseEnd_2195811 : Nat := 125278496603312623673795

theorem tailTrace_2195811 : CollatzResearch.WordTrace tailWord_2195811 prefixEnd_2195811 125278496603312623673795 := by
  unfold tailWord_2195811
  simp only [CollatzResearch.WordTrace]
  refine ⟨80087806647959236507467287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53391871098639491004978191 80087806647959236507467287)
  ·
    refine ⟨120131709971938854761200931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80087806647959236507467287 120131709971938854761200931)
    ·
      refine ⟨180197564957908282141801397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120131709971938854761200931 180197564957908282141801397)
      ·
        refine ⟨16893521714803901450793881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180197564957908282141801397 16893521714803901450793881)
        ·
          refine ⟨12670141286102926088095411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16893521714803901450793881 12670141286102926088095411)
          ·
            refine ⟨19005211929154389132143117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12670141286102926088095411 19005211929154389132143117)
            ·
              refine ⟨7126954473432895924553669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19005211929154389132143117 7126954473432895924553669)
              ·
                refine ⟨1336303963768667985853813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7126954473432895924553669 1336303963768667985853813)
                ·
                  refine ⟨125278496603312623673795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336303963768667985853813 125278496603312623673795)
                  ·
                    rfl

theorem cell23_2195811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 5].length) (baseStart_2195811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195811 prefixEnd_2195811 := by exact prefixLift 2195811
  have htrace : WordTrace (prefixWord ++ tailWord_2195811) baseStart_2195811 baseEnd_2195811 := by
    simpa [prefixWord, tailWord_2195811, baseEnd_2195811] using wordTrace_append hprefix tailTrace_2195811
  have hstable : (prefixWord ++ tailWord_2195811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195811).length < 2 ^ (prefixWord ++ tailWord_2195811).sum := by decide
  have hdescent : baseEnd_2195811 < baseStart_2195811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195821 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2195821 : Nat := 118140960795 + 2195821 * 2 ^ 59
def prefixEnd_2195821 : Nat := 4983230072969 + 3 ^ 40 * 2195821 * 2
def baseEnd_2195821 : Nat := 1127511604236358573939109

theorem tailTrace_2195821 : CollatzResearch.WordTrace tailWord_2195821 prefixEnd_2195821 1127511604236358573939109 := by
  unfold tailWord_2195821
  simp only [CollatzResearch.WordTrace]
  refine ⟨80088171377923008215331317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53392114251948672143554211 80088171377923008215331317)
  ·
    refine ⟨7508266066680282020187311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80088171377923008215331317 7508266066680282020187311)
    ·
      refine ⟨11262399100020423030280967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7508266066680282020187311 11262399100020423030280967)
      ·
        refine ⟨16893598650030634545421451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11262399100020423030280967 16893598650030634545421451)
        ·
          refine ⟨25340397975045951818132177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16893598650030634545421451 25340397975045951818132177)
          ·
            refine ⟨19005298481284463863599133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25340397975045951818132177 19005298481284463863599133)
            ·
              refine ⟨7126986930481673948849675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19005298481284463863599133 7126986930481673948849675)
              ·
                refine ⟨10690480395722510923274513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7126986930481673948849675 10690480395722510923274513)
                ·
                  refine ⟨8017860296791883192455885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10690480395722510923274513 8017860296791883192455885)
                  ·
                    refine ⟨3006697611296956197170957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8017860296791883192455885 3006697611296956197170957)
                    ·
                      refine ⟨1127511604236358573939109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006697611296956197170957 1127511604236358573939109)
                      ·
                        rfl

theorem cell23_2195821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2195821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195821 prefixEnd_2195821 := by exact prefixLift 2195821
  have htrace : WordTrace (prefixWord ++ tailWord_2195821) baseStart_2195821 baseEnd_2195821 := by
    simpa [prefixWord, tailWord_2195821, baseEnd_2195821] using wordTrace_append hprefix tailTrace_2195821
  have hstable : (prefixWord ++ tailWord_2195821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195821).length < 2 ^ (prefixWord ++ tailWord_2195821).sum := by decide
  have hdescent : baseEnd_2195821 < baseStart_2195821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195841 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 1, 7]
def baseStart_2195841 : Nat := 118140960795 + 2195841 * 2 ^ 59
def prefixEnd_2195841 : Nat := 4983230072969 + 3 ^ 40 * 2195841 * 2
def baseEnd_2195841 : Nat := 375840624616482831896339

theorem tailTrace_2195841 : CollatzResearch.WordTrace tailWord_2195841 prefixEnd_2195841 375840624616482831896339 := by
  unfold tailWord_2195841
  simp only [CollatzResearch.WordTrace]
  refine ⟨80088900837850551631059377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53392600558567034420706251 80088900837850551631059377)
  ·
    refine ⟨60066675628387913723294533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80088900837850551631059377 60066675628387913723294533)
    ·
      refine ⟨11262501680322733823117725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60066675628387913723294533 11262501680322733823117725)
      ·
        refine ⟨4223438130121025183669147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11262501680322733823117725 4223438130121025183669147)
        ·
          refine ⟨6335157195181537775503721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4223438130121025183669147 6335157195181537775503721)
          ·
            refine ⟨4751367896386153331627791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6335157195181537775503721 4751367896386153331627791)
            ·
              refine ⟨7127051844579229997441687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4751367896386153331627791 7127051844579229997441687)
              ·
                refine ⟨10690577766868844996162531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7127051844579229997441687 10690577766868844996162531)
                ·
                  refine ⟨16035866650303267494243797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10690577766868844996162531 16035866650303267494243797)
                  ·
                    refine ⟨375840624616482831896339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16035866650303267494243797 375840624616482831896339)
                    ·
                      rfl

theorem cell23_2195841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_2195841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195841 prefixEnd_2195841 := by exact prefixLift 2195841
  have htrace : WordTrace (prefixWord ++ tailWord_2195841) baseStart_2195841 baseEnd_2195841 := by
    simpa [prefixWord, tailWord_2195841, baseEnd_2195841] using wordTrace_append hprefix tailTrace_2195841
  have hstable : (prefixWord ++ tailWord_2195841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195841).length < 2 ^ (prefixWord ++ tailWord_2195841).sum := by decide
  have hdescent : baseEnd_2195841 < baseStart_2195841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195862 : List Nat := [5, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_2195862 : Nat := 118140960795 + 2195862 * 2 ^ 59
def prefixEnd_2195862 : Nat := 4983230072969 + 3 ^ 40 * 2195862 * 2
def baseEnd_2195862 : Nat := 125281406327021434836269

theorem tailTrace_2195862 : CollatzResearch.WordTrace tailWord_2195862 prefixEnd_2195862 125281406327021434836269 := by
  unfold tailWord_2195862
  simp only [CollatzResearch.WordTrace]
  refine ⟨5005604173173404513598365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53393111180516314811715893 5005604173173404513598365)
  ·
    refine ⟨1877101564940026692599387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5005604173173404513598365 1877101564940026692599387)
    ·
      refine ⟨2815652347410040038899081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877101564940026692599387 2815652347410040038899081)
      ·
        refine ⟨2111739260557530029174311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2815652347410040038899081 2111739260557530029174311)
        ·
          refine ⟨3167608890836295043761467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111739260557530029174311 3167608890836295043761467)
          ·
            refine ⟨4751413336254442565642201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167608890836295043761467 4751413336254442565642201)
            ·
              refine ⟨3563560002190831924231651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751413336254442565642201 3563560002190831924231651)
              ·
                refine ⟨5345340003286247886347477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563560002190831924231651 5345340003286247886347477)
                ·
                  refine ⟨125281406327021434836269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5345340003286247886347477 125281406327021434836269)
                  ·
                    rfl

theorem cell23_2195862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_2195862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195862 prefixEnd_2195862 := by exact prefixLift 2195862
  have htrace : WordTrace (prefixWord ++ tailWord_2195862) baseStart_2195862 baseEnd_2195862 := by
    simpa [prefixWord, tailWord_2195862, baseEnd_2195862] using wordTrace_append hprefix tailTrace_2195862
  have hstable : (prefixWord ++ tailWord_2195862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195862).length < 2 ^ (prefixWord ++ tailWord_2195862).sum := by decide
  have hdescent : baseEnd_2195862 < baseStart_2195862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195922 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_2195922 : Nat := 118140960795 + 2195922 * 2 ^ 59
def prefixEnd_2195922 : Nat := 4983230072969 + 3 ^ 40 * 2195922 * 2
def baseEnd_2195922 : Nat := 375854488594154226258715

theorem tailTrace_2195922 : CollatzResearch.WordTrace tailWord_2195922 prefixEnd_2195922 375854488594154226258715 := by
  unfold tailWord_2195922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20022963787639275616189505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53394570100371401643172013 20022963787639275616189505)
  ·
    refine ⟨15017222840729456712142129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20022963787639275616189505 15017222840729456712142129)
    ·
      refine ⟨11262917130547092534106597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15017222840729456712142129 11262917130547092534106597)
      ·
        refine ⟨2111796961977579850144987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11262917130547092534106597 2111796961977579850144987)
        ·
          refine ⟨3167695442966369775217481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111796961977579850144987 3167695442966369775217481)
          ·
            refine ⟨2375771582224777331413111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3167695442966369775217481 2375771582224777331413111)
            ·
              refine ⟨3563657373337165997119667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2375771582224777331413111 3563657373337165997119667)
              ·
                refine ⟨5345486060005748995679501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3563657373337165997119667 5345486060005748995679501)
                ·
                  refine ⟨2004557272502155873379813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5345486060005748995679501 2004557272502155873379813)
                  ·
                    refine ⟨375854488594154226258715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2004557272502155873379813 375854488594154226258715)
                    ·
                      rfl

theorem cell23_2195922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_2195922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195922 prefixEnd_2195922 := by exact prefixLift 2195922
  have htrace : WordTrace (prefixWord ++ tailWord_2195922) baseStart_2195922 baseEnd_2195922 := by
    simpa [prefixWord, tailWord_2195922, baseEnd_2195922] using wordTrace_append hprefix tailTrace_2195922
  have hstable : (prefixWord ++ tailWord_2195922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195922).length < 2 ^ (prefixWord ++ tailWord_2195922).sum := by decide
  have hdescent : baseEnd_2195922 < baseStart_2195922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195961 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 6, 4]
def baseStart_2195961 : Nat := 118140960795 + 2195961 * 2 ^ 59
def prefixEnd_2195961 : Nat := 4983230072969 + 3 ^ 40 * 2195961 * 2
def baseEnd_2195961 : Nat := 375861163842662675396155

theorem tailTrace_2195961 : CollatzResearch.WordTrace tailWord_2195961 prefixEnd_2195961 375861163842662675396155 := by
  unfold tailWord_2195961
  simp only [CollatzResearch.WordTrace]
  refine ⟨80093277597415812125427737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53395518398277208083618491 80093277597415812125427737)
  ·
    refine ⟨60069958198061859094070803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80093277597415812125427737 60069958198061859094070803)
    ·
      refine ⟨90104937297092788641106205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60069958198061859094070803 90104937297092788641106205)
      ·
        refine ⟨33789351486409795740414827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90104937297092788641106205 33789351486409795740414827)
        ·
          refine ⟨50684027229614693610622241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33789351486409795740414827 50684027229614693610622241)
          ·
            refine ⟨38013020422211020207966681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50684027229614693610622241 38013020422211020207966681)
            ·
              refine ⟨28509765316658265155975011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38013020422211020207966681 28509765316658265155975011)
              ·
                refine ⟨42764647974987397733962517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28509765316658265155975011 42764647974987397733962517)
                ·
                  refine ⟨2004592873827534268779493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42764647974987397733962517 2004592873827534268779493)
                  ·
                    refine ⟨375861163842662675396155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2004592873827534268779493 375861163842662675396155)
                    ·
                      rfl

theorem cell23_2195961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 4].length) (baseStart_2195961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195961 prefixEnd_2195961 := by exact prefixLift 2195961
  have htrace : WordTrace (prefixWord ++ tailWord_2195961) baseStart_2195961 baseEnd_2195961 := by
    simpa [prefixWord, tailWord_2195961, baseEnd_2195961] using wordTrace_append hprefix tailTrace_2195961
  have hstable : (prefixWord ++ tailWord_2195961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195961).length < 2 ^ (prefixWord ++ tailWord_2195961).sum := by decide
  have hdescent : baseEnd_2195961 < baseStart_2195961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2195979 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 1, 1, 3]
def baseStart_2195979 : Nat := 118140960795 + 2195979 * 2 ^ 59
def prefixEnd_2195979 : Nat := 4983230072969 + 3 ^ 40 * 2195979 * 2
def baseEnd_2195979 : Nat := 1127592734179768955763383

theorem tailTrace_2195979 : CollatzResearch.WordTrace tailWord_2195979 prefixEnd_2195979 1127592734179768955763383 := by
  unfold tailWord_2195979
  simp only [CollatzResearch.WordTrace]
  refine ⟨80093934111350601199582991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53395956074233734133055327 80093934111350601199582991)
  ·
    refine ⟨120140901167025901799374487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80093934111350601199582991 120140901167025901799374487)
    ·
      refine ⟨180211351750538852699061731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120140901167025901799374487 180211351750538852699061731)
      ·
        refine ⟨270317027625808279048592597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180211351750538852699061731 270317027625808279048592597)
        ·
          refine ⟨6335555334979881540201389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 270317027625808279048592597 6335555334979881540201389)
          ·
            refine ⟨2375833250617455577575521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6335555334979881540201389 2375833250617455577575521)
            ·
              refine ⟨1781874937963091683181641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375833250617455577575521 1781874937963091683181641)
              ·
                refine ⟨1336406203472318762386231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1781874937963091683181641 1336406203472318762386231)
                ·
                  refine ⟨2004609305208478143579347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336406203472318762386231 2004609305208478143579347)
                  ·
                    refine ⟨3006913957812717215369021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2004609305208478143579347 3006913957812717215369021)
                    ·
                      refine ⟨1127592734179768955763383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006913957812717215369021 1127592734179768955763383)
                      ·
                        rfl

theorem cell23_2195979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 1, 3].length) (baseStart_2195979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2195979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2195979 prefixEnd_2195979 := by exact prefixLift 2195979
  have htrace : WordTrace (prefixWord ++ tailWord_2195979) baseStart_2195979 baseEnd_2195979 := by
    simpa [prefixWord, tailWord_2195979, baseEnd_2195979] using wordTrace_append hprefix tailTrace_2195979
  have hstable : (prefixWord ++ tailWord_2195979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2195979).length < 2 ^ (prefixWord ++ tailWord_2195979).sum := by decide
  have hdescent : baseEnd_2195979 < baseStart_2195979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2195979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196013 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2196013 : Nat := 118140960795 + 2196013 * 2 ^ 59
def prefixEnd_2196013 : Nat := 4983230072969 + 3 ^ 40 * 2196013 * 2
def baseEnd_2196013 : Nat := 1127610192522021822738227

theorem tailTrace_2196013 : CollatzResearch.WordTrace tailWord_2196013 prefixEnd_2196013 1127610192522021822738227 := by
  unfold tailWord_2196013
  simp only [CollatzResearch.WordTrace]
  refine ⟨80095174193227425006320693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53396782795484950004213795 80095174193227425006320693)
  ·
    refine ⟨7508922580615071094342565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80095174193227425006320693 7508922580615071094342565)
    ·
      refine ⟨1407922983865325830189231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7508922580615071094342565 1407922983865325830189231)
      ·
        refine ⟨2111884475797988745283847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407922983865325830189231 2111884475797988745283847)
        ·
          refine ⟨3167826713696983117925771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111884475797988745283847 3167826713696983117925771)
          ·
            refine ⟨4751740070545474676888657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3167826713696983117925771 4751740070545474676888657)
            ·
              refine ⟨3563805052909106007666493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4751740070545474676888657 3563805052909106007666493)
              ·
                refine ⟨1336426894840914752874935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3563805052909106007666493 1336426894840914752874935)
                ·
                  refine ⟨2004640342261372129312403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336426894840914752874935 2004640342261372129312403)
                  ·
                    refine ⟨3006960513392058193968605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2004640342261372129312403 3006960513392058193968605)
                    ·
                      refine ⟨1127610192522021822738227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006960513392058193968605 1127610192522021822738227)
                      ·
                        rfl

theorem cell23_2196013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2196013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196013 prefixEnd_2196013 := by exact prefixLift 2196013
  have htrace : WordTrace (prefixWord ++ tailWord_2196013) baseStart_2196013 baseEnd_2196013 := by
    simpa [prefixWord, tailWord_2196013, baseEnd_2196013] using wordTrace_append hprefix tailTrace_2196013
  have hstable : (prefixWord ++ tailWord_2196013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196013).length < 2 ^ (prefixWord ++ tailWord_2196013).sum := by decide
  have hdescent : baseEnd_2196013 < baseStart_2196013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196018 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2196018 : Nat := 118140960795 + 2196018 * 2 ^ 59
def prefixEnd_2196018 : Nat := 4983230072969 + 3 ^ 40 * 2196018 * 2
def baseEnd_2196018 : Nat := 1127612759925294303175703

theorem tailTrace_2196018 : CollatzResearch.WordTrace tailWord_2196018 prefixEnd_2196018 1127612759925294303175703 := by
  unfold tailWord_2196018
  simp only [CollatzResearch.WordTrace]
  refine ⟨20023839139552327715063177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53396904372139540573501805 20023839139552327715063177)
  ·
    refine ⟨15017879354664245786297383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20023839139552327715063177 15017879354664245786297383)
    ·
      refine ⟨22526819031996368679446075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15017879354664245786297383 22526819031996368679446075)
      ·
        refine ⟨33790228547994553019169113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22526819031996368679446075 33790228547994553019169113)
        ·
          refine ⟨25342671410995914764376835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33790228547994553019169113 25342671410995914764376835)
          ·
            refine ⟨38014007116493872146565253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25342671410995914764376835 38014007116493872146565253)
            ·
              refine ⟨7127626334342601027480985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38014007116493872146565253 7127626334342601027480985)
              ·
                refine ⟨5345719750756950770610739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7127626334342601027480985 5345719750756950770610739)
                ·
                  refine ⟨8018579626135426155916109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5345719750756950770610739 8018579626135426155916109)
                  ·
                    refine ⟨3006967359800784808468541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8018579626135426155916109 3006967359800784808468541)
                    ·
                      refine ⟨1127612759925294303175703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006967359800784808468541 1127612759925294303175703)
                      ·
                        rfl

theorem cell23_2196018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2196018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196018 prefixEnd_2196018 := by exact prefixLift 2196018
  have htrace : WordTrace (prefixWord ++ tailWord_2196018) baseStart_2196018 baseEnd_2196018 := by
    simpa [prefixWord, tailWord_2196018, baseEnd_2196018] using wordTrace_append hprefix tailTrace_2196018
  have hstable : (prefixWord ++ tailWord_2196018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196018).length < 2 ^ (prefixWord ++ tailWord_2196018).sum := by decide
  have hdescent : baseEnd_2196018 < baseStart_2196018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196022 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_2196022 : Nat := 118140960795 + 2196022 * 2 ^ 59
def prefixEnd_2196022 : Nat := 4983230072969 + 3 ^ 40 * 2196022 * 2
def baseEnd_2196022 : Nat := 1127614813847912287525685

theorem tailTrace_2196022 : CollatzResearch.WordTrace tailWord_2196022 prefixEnd_2196022 1127614813847912287525685 := by
  unfold tailWord_2196022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5005968903137176221462395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53397001633463213028932213 5005968903137176221462395)
  ·
    refine ⟨7508953354705764332193593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5005968903137176221462395 7508953354705764332193593)
    ·
      refine ⟨5631715016029323249145195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7508953354705764332193593 5631715016029323249145195)
      ·
        refine ⟨8447572524043984873717793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5631715016029323249145195 8447572524043984873717793)
        ·
          refine ⟨6335679393032988655288345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8447572524043984873717793 6335679393032988655288345)
          ·
            refine ⟨4751759544774741491466259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6335679393032988655288345 4751759544774741491466259)
            ·
              refine ⟨7127639317162112237199389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4751759544774741491466259 7127639317162112237199389)
              ·
                refine ⟨2672864743935792088949771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7127639317162112237199389 2672864743935792088949771)
                ·
                  refine ⟨4009297115903688133424657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2672864743935792088949771 4009297115903688133424657)
                  ·
                    refine ⟨3006972836927766100068493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009297115903688133424657 3006972836927766100068493)
                    ·
                      refine ⟨1127614813847912287525685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3006972836927766100068493 1127614813847912287525685)
                      ·
                        rfl

theorem cell23_2196022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_2196022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196022 prefixEnd_2196022 := by exact prefixLift 2196022
  have htrace : WordTrace (prefixWord ++ tailWord_2196022) baseStart_2196022 baseEnd_2196022 := by
    simpa [prefixWord, tailWord_2196022, baseEnd_2196022] using wordTrace_append hprefix tailTrace_2196022
  have hstable : (prefixWord ++ tailWord_2196022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196022).length < 2 ^ (prefixWord ++ tailWord_2196022).sum := by decide
  have hdescent : baseEnd_2196022 < baseStart_2196022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196078 : List Nat := [4, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2196078 : Nat := 118140960795 + 2196078 * 2 ^ 59
def prefixEnd_2196078 : Nat := 4983230072969 + 3 ^ 40 * 2196078 * 2
def baseEnd_2196078 : Nat := 1127643568764564068425427

theorem tailTrace_2196078 : CollatzResearch.WordTrace tailWord_2196078 prefixEnd_2196078 1127643568764564068425427 := by
  unfold tailWord_2196078
  simp only [CollatzResearch.WordTrace]
  refine ⟨10012193117248992638429611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53398363291994627404957925 10012193117248992638429611)
  ·
    refine ⟨15018289675873488957644417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10012193117248992638429611 15018289675873488957644417)
    ·
      refine ⟨11263717256905116718233313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15018289675873488957644417 11263717256905116718233313)
      ·
        refine ⟨8447787942678837538674985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11263717256905116718233313 8447787942678837538674985)
        ·
          refine ⟨6335840957009128154006239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8447787942678837538674985 6335840957009128154006239)
          ·
            refine ⟨9503761435513692231009359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6335840957009128154006239 9503761435513692231009359)
            ·
              refine ⟨14255642153270538346514039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9503761435513692231009359 14255642153270538346514039)
              ·
                refine ⟨21383463229905807519771059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14255642153270538346514039 21383463229905807519771059)
                ·
                  refine ⟨32075194844858711279656589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21383463229905807519771059 32075194844858711279656589)
                  ·
                    refine ⟨12028198066822016729871221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32075194844858711279656589 12028198066822016729871221)
                    ·
                      refine ⟨1127643568764564068425427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12028198066822016729871221 1127643568764564068425427)
                      ·
                        rfl

theorem cell23_2196078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2196078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196078 prefixEnd_2196078 := by exact prefixLift 2196078
  have htrace : WordTrace (prefixWord ++ tailWord_2196078) baseStart_2196078 baseEnd_2196078 := by
    simpa [prefixWord, tailWord_2196078, baseEnd_2196078] using wordTrace_append hprefix tailTrace_2196078
  have hstable : (prefixWord ++ tailWord_2196078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196078).length < 2 ^ (prefixWord ++ tailWord_2196078).sum := by decide
  have hdescent : baseEnd_2196078 < baseStart_2196078 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196121 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 7]
def baseStart_2196121 : Nat := 118140960795 + 2196121 * 2 ^ 59
def prefixEnd_2196121 : Nat := 4983230072969 + 3 ^ 40 * 2196121 * 2
def baseEnd_2196121 : Nat := 1127665648432707400187729

theorem tailTrace_2196121 : CollatzResearch.WordTrace tailWord_2196121 prefixEnd_2196121 1127665648432707400187729 := by
  unfold tailWord_2196121
  simp only [CollatzResearch.WordTrace]
  refine ⟨80099113276836159451252217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53399408851224106300834811 80099113276836159451252217)
  ·
    refine ⟨60074334957627119588439163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80099113276836159451252217 60074334957627119588439163)
    ·
      refine ⟨90111502436440679382658745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60074334957627119588439163 90111502436440679382658745)
      ·
        refine ⟨67583626827330509536994059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90111502436440679382658745 67583626827330509536994059)
        ·
          refine ⟨101375440240995764305491089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67583626827330509536994059 101375440240995764305491089)
          ·
            refine ⟨76031580180746823229118317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101375440240995764305491089 76031580180746823229118317)
            ·
              refine ⟨28511842567780058710919369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76031580180746823229118317 28511842567780058710919369)
              ·
                refine ⟨21383881925835044033189527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28511842567780058710919369 21383881925835044033189527)
                ·
                  refine ⟨32075822888752566049784291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21383881925835044033189527 32075822888752566049784291)
                  ·
                    refine ⟨48113734333128849074676437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32075822888752566049784291 48113734333128849074676437)
                    ·
                      refine ⟨1127665648432707400187729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 48113734333128849074676437 1127665648432707400187729)
                      ·
                        rfl

theorem cell23_2196121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_2196121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196121 prefixEnd_2196121 := by exact prefixLift 2196121
  have htrace : WordTrace (prefixWord ++ tailWord_2196121) baseStart_2196121 baseEnd_2196121 := by
    simpa [prefixWord, tailWord_2196121, baseEnd_2196121] using wordTrace_append hprefix tailTrace_2196121
  have hstable : (prefixWord ++ tailWord_2196121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196121).length < 2 ^ (prefixWord ++ tailWord_2196121).sum := by decide
  have hdescent : baseEnd_2196121 < baseStart_2196121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196149 : List Nat := [1, 3, 3, 3, 1, 3, 2, 2, 5]
def baseStart_2196149 : Nat := 118140960795 + 2196149 * 2 ^ 59
def prefixEnd_2196149 : Nat := 4983230072969 + 3 ^ 40 * 2196149 * 2
def baseEnd_2196149 : Nat := 125297780654559254515289

theorem tailTrace_2196149 : CollatzResearch.WordTrace tailWord_2196149 prefixEnd_2196149 125297780654559254515289 := by
  unfold tailWord_2196149
  simp only [CollatzResearch.WordTrace]
  refine ⟨80100134520734720233271501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53400089680489813488847667 80100134520734720233271501)
  ·
    refine ⟨30037550445275520087476813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80100134520734720233271501 30037550445275520087476813)
    ·
      refine ⟨11264081416978320032803805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30037550445275520087476813 11264081416978320032803805)
      ·
        refine ⟨4224030531366870012301427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11264081416978320032803805 4224030531366870012301427)
        ·
          refine ⟨6336045797050305018452141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4224030531366870012301427 6336045797050305018452141)
          ·
            refine ⟨2376017173893864381919553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6336045797050305018452141 2376017173893864381919553)
            ·
              refine ⟨1782012880420398286439665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2376017173893864381919553 1782012880420398286439665)
              ·
                refine ⟨1336509660315298714829749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782012880420398286439665 1336509660315298714829749)
                ·
                  refine ⟨125297780654559254515289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336509660315298714829749 125297780654559254515289)
                  ·
                    rfl

theorem cell23_2196149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_2196149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196149 prefixEnd_2196149 := by exact prefixLift 2196149
  have htrace : WordTrace (prefixWord ++ tailWord_2196149) baseStart_2196149 baseEnd_2196149 := by
    simpa [prefixWord, tailWord_2196149, baseEnd_2196149] using wordTrace_append hprefix tailTrace_2196149
  have hstable : (prefixWord ++ tailWord_2196149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196149).length < 2 ^ (prefixWord ++ tailWord_2196149).sum := by decide
  have hdescent : baseEnd_2196149 < baseStart_2196149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196171 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 12]
def baseStart_2196171 : Nat := 118140960795 + 2196171 * 2 ^ 59
def prefixEnd_2196171 : Nat := 4983230072969 + 3 ^ 40 * 2196171 * 2
def baseEnd_2196171 : Nat := 125299035829492467173611

theorem tailTrace_2196171 : CollatzResearch.WordTrace tailWord_2196171 prefixEnd_2196171 125299035829492467173611 := by
  unfold tailWord_2196171
  simp only [CollatzResearch.WordTrace]
  refine ⟨80100936926655017990572367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53400624617770011993714911 80100936926655017990572367)
  ·
    refine ⟨120151405389982526985858551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80100936926655017990572367 120151405389982526985858551)
    ·
      refine ⟨180227108084973790478787827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120151405389982526985858551 180227108084973790478787827)
      ·
        refine ⟨270340662127460685718181741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180227108084973790478787827 270340662127460685718181741)
        ·
          refine ⟨101377748297797757144318153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270340662127460685718181741 101377748297797757144318153)
          ·
            refine ⟨76033311223348317858238615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101377748297797757144318153 76033311223348317858238615)
            ·
              refine ⟨114049966835022476787357923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76033311223348317858238615 114049966835022476787357923)
              ·
                refine ⟨171074950252533715181036885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114049966835022476787357923 171074950252533715181036885)
                ·
                  refine ⟨125299035829492467173611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 171074950252533715181036885 125299035829492467173611)
                  ·
                    rfl

theorem cell23_2196171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 12].length) (baseStart_2196171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196171 prefixEnd_2196171 := by exact prefixLift 2196171
  have htrace : WordTrace (prefixWord ++ tailWord_2196171) baseStart_2196171 baseEnd_2196171 := by
    simpa [prefixWord, tailWord_2196171, baseEnd_2196171] using wordTrace_append hprefix tailTrace_2196171
  have hstable : (prefixWord ++ tailWord_2196171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196171).length < 2 ^ (prefixWord ++ tailWord_2196171).sum := by decide
  have hdescent : baseEnd_2196171 < baseStart_2196171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196218 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_2196218 : Nat := 118140960795 + 2196218 * 2 ^ 59
def prefixEnd_2196218 : Nat := 4983230072969 + 3 ^ 40 * 2196218 * 2
def baseEnd_2196218 : Nat := 375905152018731173558261

theorem tailTrace_2196218 : CollatzResearch.WordTrace tailWord_2196218 prefixEnd_2196218 375905152018731173558261 := by
  unfold tailWord_2196218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20025662789371186254383327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53401767438323163345022205 20025662789371186254383327)
  ·
    refine ⟨30038494184056779381574991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20025662789371186254383327 30038494184056779381574991)
    ·
      refine ⟨45057741276085169072362487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30038494184056779381574991 45057741276085169072362487)
      ·
        refine ⟨67586611914127753608543731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45057741276085169072362487 67586611914127753608543731)
        ·
          refine ⟨101379917871191630412815597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67586611914127753608543731 101379917871191630412815597)
          ·
            refine ⟨38017469201696861404805849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101379917871191630412815597 38017469201696861404805849)
            ·
              refine ⟨28513101901272646053604387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38017469201696861404805849 28513101901272646053604387)
              ·
                refine ⟨42769652851908969080406581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28513101901272646053604387 42769652851908969080406581)
                ·
                  refine ⟨4009654954866465851288117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42769652851908969080406581 4009654954866465851288117)
                  ·
                    refine ⟨375905152018731173558261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4009654954866465851288117 375905152018731173558261)
                    ·
                      rfl

theorem cell23_2196218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_2196218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196218 prefixEnd_2196218 := by exact prefixLift 2196218
  have htrace : WordTrace (prefixWord ++ tailWord_2196218) baseStart_2196218 baseEnd_2196218 := by
    simpa [prefixWord, tailWord_2196218, baseEnd_2196218] using wordTrace_append hprefix tailTrace_2196218
  have hstable : (prefixWord ++ tailWord_2196218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196218).length < 2 ^ (prefixWord ++ tailWord_2196218).sum := by decide
  have hdescent : baseEnd_2196218 < baseStart_2196218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196232 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 3, 1, 3]
def baseStart_2196232 : Nat := 118140960795 + 2196232 * 2 ^ 59
def prefixEnd_2196232 : Nat := 4983230072969 + 3 ^ 40 * 2196232 * 2
def baseEnd_2196232 : Nat := 1127722644785356465899719

theorem tailTrace_2196232 : CollatzResearch.WordTrace tailWord_2196232 prefixEnd_2196232 1127722644785356465899719 := by
  unfold tailWord_2196232
  simp only [CollatzResearch.WordTrace]
  refine ⟨40051580889717012704271475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53402107852956016939028633 40051580889717012704271475)
  ·
    refine ⟨60077371334575519056407213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40051580889717012704271475 60077371334575519056407213)
    ·
      refine ⟨22529014250465819646152705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60077371334575519056407213 22529014250465819646152705)
      ·
        refine ⟨16896760687849364734614529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22529014250465819646152705 16896760687849364734614529)
        ·
          refine ⟨12672570515887023550960897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16896760687849364734614529 12672570515887023550960897)
          ·
            refine ⟨9504427886915267663220673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12672570515887023550960897 9504427886915267663220673)
            ·
              refine ⟨7128320915186450747415505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9504427886915267663220673 7128320915186450747415505)
              ·
                refine ⟨5346240686389838060561629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7128320915186450747415505 5346240686389838060561629)
                ·
                  refine ⟨2004840257396189272710611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5346240686389838060561629 2004840257396189272710611)
                  ·
                    refine ⟨3007260386094283909065917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2004840257396189272710611 3007260386094283909065917)
                    ·
                      refine ⟨1127722644785356465899719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3007260386094283909065917 1127722644785356465899719)
                      ·
                        rfl

theorem cell23_2196232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_2196232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196232 prefixEnd_2196232 := by exact prefixLift 2196232
  have htrace : WordTrace (prefixWord ++ tailWord_2196232) baseStart_2196232 baseEnd_2196232 := by
    simpa [prefixWord, tailWord_2196232, baseEnd_2196232] using wordTrace_append hprefix tailTrace_2196232
  have hstable : (prefixWord ++ tailWord_2196232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196232).length < 2 ^ (prefixWord ++ tailWord_2196232).sum := by decide
  have hdescent : baseEnd_2196232 < baseStart_2196232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196248 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_2196248 : Nat := 118140960795 + 2196248 * 2 ^ 59
def prefixEnd_2196248 : Nat := 4983230072969 + 3 ^ 40 * 2196248 * 2
def baseEnd_2196248 : Nat := 375910286825276134433215

theorem tailTrace_2196248 : CollatzResearch.WordTrace tailWord_2196248 prefixEnd_2196248 375910286825276134433215 := by
  unfold tailWord_2196248
  simp only [CollatzResearch.WordTrace]
  refine ⟨40051872673688030070562699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53402496898250706760750265 40051872673688030070562699)
  ·
    refine ⟨60077809010532045105844049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40051872673688030070562699 60077809010532045105844049)
    ·
      refine ⟨45058356757899033829383037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60077809010532045105844049 45058356757899033829383037)
      ·
        refine ⟨16896883784212137686018639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45058356757899033829383037 16896883784212137686018639)
        ·
          refine ⟨25345325676318206529027959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16896883784212137686018639 25345325676318206529027959)
          ·
            refine ⟨38017988514477309793541939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25345325676318206529027959 38017988514477309793541939)
            ·
              refine ⟨57026982771715964690312909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38017988514477309793541939 57026982771715964690312909)
              ·
                refine ⟨21385118539393486758867341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57026982771715964690312909 21385118539393486758867341)
                ·
                  refine ⟨8019419452272557534575253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21385118539393486758867341 8019419452272557534575253)
                  ·
                    refine ⟨375910286825276134433215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8019419452272557534575253 375910286825276134433215)
                    ·
                      rfl

theorem cell23_2196248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_2196248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196248 prefixEnd_2196248 := by exact prefixLift 2196248
  have htrace : WordTrace (prefixWord ++ tailWord_2196248) baseStart_2196248 baseEnd_2196248 := by
    simpa [prefixWord, tailWord_2196248, baseEnd_2196248] using wordTrace_append hprefix tailTrace_2196248
  have hstable : (prefixWord ++ tailWord_2196248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196248).length < 2 ^ (prefixWord ++ tailWord_2196248).sum := by decide
  have hdescent : baseEnd_2196248 < baseStart_2196248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196268 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_2196268 : Nat := 118140960795 + 2196268 * 2 ^ 59
def prefixEnd_2196268 : Nat := 4983230072969 + 3 ^ 40 * 2196268 * 2
def baseEnd_2196268 : Nat := 1127741130088918325049553

theorem tailTrace_2196268 : CollatzResearch.WordTrace tailWord_2196268 prefixEnd_2196268 1127741130088918325049553 := by
  unfold tailWord_2196268
  simp only [CollatzResearch.WordTrace]
  refine ⟨40052237403651801778426729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53402983204869069037902305 40052237403651801778426729)
  ·
    refine ⟨30039178052738851333820047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40052237403651801778426729 30039178052738851333820047)
    ·
      refine ⟨45058767079108277000730071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30039178052738851333820047 45058767079108277000730071)
      ·
        refine ⟨67588150618662415501095107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45058767079108277000730071 67588150618662415501095107)
        ·
          refine ⟨101382225927993623251642661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67588150618662415501095107 101382225927993623251642661)
          ·
            refine ⟨19009167361498804359682999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101382225927993623251642661 19009167361498804359682999)
            ·
              refine ⟨28513751042248206539524499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19009167361498804359682999 28513751042248206539524499)
              ·
                refine ⟨42770626563372309809286749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28513751042248206539524499 42770626563372309809286749)
                ·
                  refine ⟨16038984961264616178482531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42770626563372309809286749 16038984961264616178482531)
                  ·
                    refine ⟨24058477441896924267723797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16038984961264616178482531 24058477441896924267723797)
                    ·
                      refine ⟨1127741130088918325049553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24058477441896924267723797 1127741130088918325049553)
                      ·
                        rfl

theorem cell23_2196268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_2196268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196268 prefixEnd_2196268 := by exact prefixLift 2196268
  have htrace : WordTrace (prefixWord ++ tailWord_2196268) baseStart_2196268 baseEnd_2196268 := by
    simpa [prefixWord, tailWord_2196268, baseEnd_2196268] using wordTrace_append hprefix tailTrace_2196268
  have hstable : (prefixWord ++ tailWord_2196268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196268).length < 2 ^ (prefixWord ++ tailWord_2196268).sum := by decide
  have hdescent : baseEnd_2196268 < baseStart_2196268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196275 : List Nat := [1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5]
def baseStart_2196275 : Nat := 118140960795 + 2196275 * 2 ^ 59
def prefixEnd_2196275 : Nat := 4983230072969 + 3 ^ 40 * 2196275 * 2
def baseEnd_2196275 : Nat := 1127744724453499797662021

theorem tailTrace_2196275 : CollatzResearch.WordTrace tailWord_2196275 prefixEnd_2196275 1127744724453499797662021 := by
  unfold tailWord_2196275
  simp only [CollatzResearch.WordTrace]
  refine ⟨80104730118278243752358279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53403153412185495834905519 80104730118278243752358279)
  ·
    refine ⟨120157095177417365628537419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80104730118278243752358279 120157095177417365628537419)
    ·
      refine ⟨180235642766126048442806129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120157095177417365628537419 180235642766126048442806129)
      ·
        refine ⟨135176732074594536332104597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180235642766126048442806129 135176732074594536332104597)
        ·
          refine ⟨6336409315996618890567403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135176732074594536332104597 6336409315996618890567403)
          ·
            refine ⟨9504613973994928335851105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336409315996618890567403 9504613973994928335851105)
            ·
              refine ⟨7128460480496196251888329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9504613973994928335851105 7128460480496196251888329)
              ·
                refine ⟨5346345360372147188916247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7128460480496196251888329 5346345360372147188916247)
                ·
                  refine ⟨8019518040558220783374371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5346345360372147188916247 8019518040558220783374371)
                  ·
                    refine ⟨12029277060837331175061557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8019518040558220783374371 12029277060837331175061557)
                    ·
                      refine ⟨1127744724453499797662021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12029277060837331175061557 1127744724453499797662021)
                      ·
                        rfl

theorem cell23_2196275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_2196275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196275 prefixEnd_2196275 := by exact prefixLift 2196275
  have htrace : WordTrace (prefixWord ++ tailWord_2196275) baseStart_2196275 baseEnd_2196275 := by
    simpa [prefixWord, tailWord_2196275, baseEnd_2196275] using wordTrace_append hprefix tailTrace_2196275
  have hstable : (prefixWord ++ tailWord_2196275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196275).length < 2 ^ (prefixWord ++ tailWord_2196275).sum := by decide
  have hdescent : baseEnd_2196275 < baseStart_2196275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196286 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 1, 5]
def baseStart_2196286 : Nat := 118140960795 + 2196286 * 2 ^ 59
def prefixEnd_2196286 : Nat := 4983230072969 + 3 ^ 40 * 2196286 * 2
def baseEnd_2196286 : Nat := 375916790913566418208157

theorem tailTrace_2196286 : CollatzResearch.WordTrace tailWord_2196286 prefixEnd_2196286 375916790913566418208157 := by
  unfold tailWord_2196286
  simp only [CollatzResearch.WordTrace]
  refine ⟨10013141415154799078876089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53403420880825595087339141 10013141415154799078876089)
  ·
    refine ⟨7509856061366099309157067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10013141415154799078876089 7509856061366099309157067)
    ·
      refine ⟨11264784092049148963735601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509856061366099309157067 11264784092049148963735601)
      ·
        refine ⟨8448588069036861722801701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11264784092049148963735601 8448588069036861722801701)
        ·
          refine ⟨1584110262944411573025319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8448588069036861722801701 1584110262944411573025319)
          ·
            refine ⟨2376165394416617359537979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584110262944411573025319 2376165394416617359537979)
            ·
              refine ⟨3564248091624926039306969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376165394416617359537979 3564248091624926039306969)
              ·
                refine ⟨2673186068718694529480227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564248091624926039306969 2673186068718694529480227)
                ·
                  refine ⟨4009779103078041794220341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673186068718694529480227 4009779103078041794220341)
                  ·
                    refine ⟨375916790913566418208157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4009779103078041794220341 375916790913566418208157)
                    ·
                      rfl

theorem cell23_2196286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_2196286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196286 prefixEnd_2196286 := by exact prefixLift 2196286
  have htrace : WordTrace (prefixWord ++ tailWord_2196286) baseStart_2196286 baseEnd_2196286 := by
    simpa [prefixWord, tailWord_2196286, baseEnd_2196286] using wordTrace_append hprefix tailTrace_2196286
  have hstable : (prefixWord ++ tailWord_2196286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196286).length < 2 ^ (prefixWord ++ tailWord_2196286).sum := by decide
  have hdescent : baseEnd_2196286 < baseStart_2196286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196289 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_2196289 : Nat := 118140960795 + 2196289 * 2 ^ 59
def prefixEnd_2196289 : Nat := 4983230072969 + 3 ^ 40 * 2196289 * 2
def baseEnd_2196289 : Nat := 1127751913182662742886957

theorem tailTrace_2196289 : CollatzResearch.WordTrace tailWord_2196289 prefixEnd_2196289 1127751913182662742886957 := by
  unfold tailWord_2196289
  simp only [CollatzResearch.WordTrace]
  refine ⟨80105240740227524143367921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53403493826818349428911947 80105240740227524143367921)
  ·
    refine ⟨60078930555170643107525941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80105240740227524143367921 60078930555170643107525941)
    ·
      refine ⟨5632399739547247791330557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60078930555170643107525941 5632399739547247791330557)
      ·
        refine ⟨2112149902330217921748959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5632399739547247791330557 2112149902330217921748959)
        ·
          refine ⟨3168224853495326882623439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112149902330217921748959 3168224853495326882623439)
          ·
            refine ⟨4752337280242990323935159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168224853495326882623439 4752337280242990323935159)
            ·
              refine ⟨7128505920364485485902739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752337280242990323935159 7128505920364485485902739)
              ·
                refine ⟨10692758880546728228854109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7128505920364485485902739 10692758880546728228854109)
                ·
                  refine ⟨4009784580205023085820291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10692758880546728228854109 4009784580205023085820291)
                  ·
                    refine ⟨6014676870307534628730437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4009784580205023085820291 6014676870307534628730437)
                    ·
                      refine ⟨1127751913182662742886957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6014676870307534628730437 1127751913182662742886957)
                      ·
                        rfl

theorem cell23_2196289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_2196289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196289 prefixEnd_2196289 := by exact prefixLift 2196289
  have htrace : WordTrace (prefixWord ++ tailWord_2196289) baseStart_2196289 baseEnd_2196289 := by
    simpa [prefixWord, tailWord_2196289, baseEnd_2196289] using wordTrace_append hprefix tailTrace_2196289
  have hstable : (prefixWord ++ tailWord_2196289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196289).length < 2 ^ (prefixWord ++ tailWord_2196289).sum := by decide
  have hdescent : baseEnd_2196289 < baseStart_2196289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196306 : List Nat := [3, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_2196306 : Nat := 118140960795 + 2196306 * 2 ^ 59
def prefixEnd_2196306 : Nat := 4983230072969 + 3 ^ 40 * 2196306 * 2
def baseEnd_2196306 : Nat := 1127760642353789176374379

theorem tailTrace_2196306 : CollatzResearch.WordTrace tailWord_2196306 prefixEnd_2196306 1127760642353789176374379 := by
  unfold tailWord_2196306
  simp only [CollatzResearch.WordTrace]
  refine ⟨20026465195291484011684193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53403907187443957364491181 20026465195291484011684193)
  ·
    refine ⟨15019848896468613008763145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20026465195291484011684193 15019848896468613008763145)
    ·
      refine ⟨11264886672351459756572359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15019848896468613008763145 11264886672351459756572359)
      ·
        refine ⟨16897330008527189634858539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11264886672351459756572359 16897330008527189634858539)
        ·
          refine ⟨25345995012790784452287809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16897330008527189634858539 25345995012790784452287809)
          ·
            refine ⟨19009496259593088339215857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25345995012790784452287809 19009496259593088339215857)
            ·
              refine ⟨14257122194694816254411893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19009496259593088339215857 14257122194694816254411893)
              ·
                refine ⟨1336605205752639023851115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14257122194694816254411893 1336605205752639023851115)
                ·
                  refine ⟨2004907808628958535776673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336605205752639023851115 2004907808628958535776673)
                  ·
                    refine ⟨1503680856471718901832505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2004907808628958535776673 1503680856471718901832505)
                    ·
                      refine ⟨1127760642353789176374379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503680856471718901832505 1127760642353789176374379)
                      ·
                        rfl

theorem cell23_2196306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_2196306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196306 prefixEnd_2196306 := by exact prefixLift 2196306
  have htrace : WordTrace (prefixWord ++ tailWord_2196306) baseStart_2196306 baseEnd_2196306 := by
    simpa [prefixWord, tailWord_2196306, baseEnd_2196306] using wordTrace_append hprefix tailTrace_2196306
  have hstable : (prefixWord ++ tailWord_2196306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196306).length < 2 ^ (prefixWord ++ tailWord_2196306).sum := by decide
  have hdescent : baseEnd_2196306 < baseStart_2196306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196309 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 1, 2, 3]
def baseStart_2196309 : Nat := 118140960795 + 2196309 * 2 ^ 59
def prefixEnd_2196309 : Nat := 4983230072969 + 3 ^ 40 * 2196309 * 2
def baseEnd_2196309 : Nat := 1127762182795752664636865

theorem tailTrace_2196309 : CollatzResearch.WordTrace tailWord_2196309 prefixEnd_2196309 1127762182795752664636865 := by
  unfold tailWord_2196309
  simp only [CollatzResearch.WordTrace]
  refine ⟨80105970200155067559095981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53403980133436711706063987 80105970200155067559095981)
  ·
    refine ⟨30039738825058150334660993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80105970200155067559095981 30039738825058150334660993)
    ·
      refine ⟨22529804118793612750995745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30039738825058150334660993 22529804118793612750995745)
      ·
        refine ⟨16897353089095209563246809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22529804118793612750995745 16897353089095209563246809)
        ·
          refine ⟨12673014816821407172435107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16897353089095209563246809 12673014816821407172435107)
          ·
            refine ⟨19009522225232110758652661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12673014816821407172435107 19009522225232110758652661)
            ·
              refine ⟨1782142708615510383623687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19009522225232110758652661 1782142708615510383623687)
              ·
                refine ⟨2673214062923265575435531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782142708615510383623687 2673214062923265575435531)
                ·
                  refine ⟨4009821094384898363153297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673214062923265575435531 4009821094384898363153297)
                  ·
                    refine ⟨3007365820788673772364973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4009821094384898363153297 3007365820788673772364973)
                    ·
                      refine ⟨1127762182795752664636865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3007365820788673772364973 1127762182795752664636865)
                      ·
                        rfl

theorem cell23_2196309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_2196309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196309 prefixEnd_2196309 := by exact prefixLift 2196309
  have htrace : WordTrace (prefixWord ++ tailWord_2196309) baseStart_2196309 baseEnd_2196309 := by
    simpa [prefixWord, tailWord_2196309, baseEnd_2196309] using wordTrace_append hprefix tailTrace_2196309
  have hstable : (prefixWord ++ tailWord_2196309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196309).length < 2 ^ (prefixWord ++ tailWord_2196309).sum := by decide
  have hdescent : baseEnd_2196309 < baseStart_2196309 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196315 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 2]
def baseStart_2196315 : Nat := 118140960795 + 2196315 * 2 ^ 59
def prefixEnd_2196315 : Nat := 4983230072969 + 3 ^ 40 * 2196315 * 2
def baseEnd_2196315 : Nat := 1127765263679679641161837

theorem tailTrace_2196315 : CollatzResearch.WordTrace tailWord_2196315 prefixEnd_2196315 1127765263679679641161837 := by
  unfold tailWord_2196315
  simp only [CollatzResearch.WordTrace]
  refine ⟨80106189038133330583814399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53404126025422220389209599 80106189038133330583814399)
  ·
    refine ⟨120159283557199995875721599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80106189038133330583814399 120159283557199995875721599)
    ·
      refine ⟨180238925335799993813582399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120159283557199995875721599 180238925335799993813582399)
      ·
        refine ⟨270358388003699990720373599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180238925335799993813582399 270358388003699990720373599)
        ·
          refine ⟨405537582005549986080560399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270358388003699990720373599 405537582005549986080560399)
          ·
            refine ⟨608306373008324979120840599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405537582005549986080560399 608306373008324979120840599)
            ·
              refine ⟨912459559512487468681260899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 608306373008324979120840599 912459559512487468681260899)
              ·
                refine ⟨1368689339268731203021891349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 912459559512487468681260899 1368689339268731203021891349)
                ·
                  refine ⟨64157312778221775141651157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1368689339268731203021891349 64157312778221775141651157)
                  ·
                    refine ⟨1503687018239572854882449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 64157312778221775141651157 1503687018239572854882449)
                    ·
                      refine ⟨1127765263679679641161837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503687018239572854882449 1127765263679679641161837)
                      ·
                        rfl

theorem cell23_2196315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 7, 2].length) (baseStart_2196315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196315 prefixEnd_2196315 := by exact prefixLift 2196315
  have htrace : WordTrace (prefixWord ++ tailWord_2196315) baseStart_2196315 baseEnd_2196315 := by
    simpa [prefixWord, tailWord_2196315, baseEnd_2196315] using wordTrace_append hprefix tailTrace_2196315
  have hstable : (prefixWord ++ tailWord_2196315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196315).length < 2 ^ (prefixWord ++ tailWord_2196315).sum := by decide
  have hdescent : baseEnd_2196315 < baseStart_2196315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196323 : List Nat := [1, 1, 1, 5, 3, 1, 4, 2, 1, 2, 2]
def baseStart_2196323 : Nat := 118140960795 + 2196323 * 2 ^ 59
def prefixEnd_2196323 : Nat := 4983230072969 + 3 ^ 40 * 2196323 * 2
def baseEnd_2196323 : Nat := 1127769371524915609861801

theorem tailTrace_2196323 : CollatzResearch.WordTrace tailWord_2196323 prefixEnd_2196323 1127769371524915609861801 := by
  unfold tailWord_2196323
  simp only [CollatzResearch.WordTrace]
  refine ⟨80106480822104347950105623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53404320548069565300070415 80106480822104347950105623)
  ·
    refine ⟨120159721233156521925158435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80106480822104347950105623 120159721233156521925158435)
    ·
      refine ⟨180239581849734782887737653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120159721233156521925158435 180239581849734782887737653)
      ·
        refine ⟨16897460798412635895725405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180239581849734782887737653 16897460798412635895725405)
        ·
          refine ⟨6336547799404738460897027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16897460798412635895725405 6336547799404738460897027)
          ·
            refine ⟨9504821699107107691345541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6336547799404738460897027 9504821699107107691345541)
            ·
              refine ⟨1782154068582582692127289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9504821699107107691345541 1782154068582582692127289)
              ·
                refine ⟨1336615551436937019095467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782154068582582692127289 1336615551436937019095467)
                ·
                  refine ⟨2004923327155405528643201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336615551436937019095467 2004923327155405528643201)
                  ·
                    refine ⟨1503692495366554146482401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2004923327155405528643201 1503692495366554146482401)
                    ·
                      refine ⟨1127769371524915609861801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503692495366554146482401 1127769371524915609861801)
                      ·
                        rfl

theorem cell23_2196323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_2196323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196323 prefixEnd_2196323 := by exact prefixLift 2196323
  have htrace : WordTrace (prefixWord ++ tailWord_2196323) baseStart_2196323 baseEnd_2196323 := by
    simpa [prefixWord, tailWord_2196323, baseEnd_2196323] using wordTrace_append hprefix tailTrace_2196323
  have hstable : (prefixWord ++ tailWord_2196323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196323).length < 2 ^ (prefixWord ++ tailWord_2196323).sum := by decide
  have hdescent : baseEnd_2196323 < baseStart_2196323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196332 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 5, 3, 2]
def baseStart_2196332 : Nat := 118140960795 + 2196332 * 2 ^ 59
def prefixEnd_2196332 : Nat := 4983230072969 + 3 ^ 40 * 2196332 * 2
def baseEnd_2196332 : Nat := 1127773992850806074649259

theorem tailTrace_2196332 : CollatzResearch.WordTrace tailWord_2196332 prefixEnd_2196332 1127773992850806074649259 := by
  unfold tailWord_2196332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40053404539535871243591625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53404539386047828324788833 40053404539535871243591625)
  ·
    refine ⟨30040053404651903432693719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40053404539535871243591625 30040053404651903432693719)
    ·
      refine ⟨45060080106977855149040579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30040053404651903432693719 45060080106977855149040579)
      ·
        refine ⟨67590120160466782723560869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45060080106977855149040579 67590120160466782723560869)
        ·
          refine ⟨12673147530087521760667663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67590120160466782723560869 12673147530087521760667663)
          ·
            refine ⟨19009721295131282641001495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12673147530087521760667663 19009721295131282641001495)
            ·
              refine ⟨28514581942696923961502243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19009721295131282641001495 28514581942696923961502243)
              ·
                refine ⟨42771872914045385942253365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28514581942696923961502243 42771872914045385942253365)
                ·
                  refine ⟨4009863085691754932086253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42771872914045385942253365 4009863085691754932086253)
                  ·
                    refine ⟨1503698657134408099532345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4009863085691754932086253 1503698657134408099532345)
                    ·
                      refine ⟨1127773992850806074649259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503698657134408099532345 1127773992850806074649259)
                      ·
                        rfl

theorem cell23_2196332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_2196332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196332 prefixEnd_2196332 := by exact prefixLift 2196332
  have htrace : WordTrace (prefixWord ++ tailWord_2196332) baseStart_2196332 baseEnd_2196332 := by
    simpa [prefixWord, tailWord_2196332, baseEnd_2196332] using wordTrace_append hprefix tailTrace_2196332
  have hstable : (prefixWord ++ tailWord_2196332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196332).length < 2 ^ (prefixWord ++ tailWord_2196332).sum := by decide
  have hdescent : baseEnd_2196332 < baseStart_2196332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196375 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 4]
def baseStart_2196375 : Nat := 118140960795 + 2196375 * 2 ^ 59
def prefixEnd_2196375 : Nat := 4983230072969 + 3 ^ 40 * 2196375 * 2
def baseEnd_2196375 : Nat := 1127796072518949406411561

theorem tailTrace_2196375 : CollatzResearch.WordTrace tailWord_2196375 prefixEnd_2196375 1127796072518949406411561 := by
  unfold tailWord_2196375
  simp only [CollatzResearch.WordTrace]
  refine ⟨80108377417915960830998579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53405584945277307220665719 80108377417915960830998579)
  ·
    refine ⟨120162566126873941246497869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80108377417915960830998579 120162566126873941246497869)
    ·
      refine ⟨45060962297577727967436701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120162566126873941246497869 45060962297577727967436701)
      ·
        refine ⟨16897860861591647987788763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45060962297577727967436701 16897860861591647987788763)
        ·
          refine ⟨25346791292387471981683145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16897860861591647987788763 25346791292387471981683145)
          ·
            refine ⟨19010093469290603986262359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25346791292387471981683145 19010093469290603986262359)
            ·
              refine ⟨28515140203935905979393539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19010093469290603986262359 28515140203935905979393539)
              ·
                refine ⟨42772710305903858969090309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28515140203935905979393539 42772710305903858969090309)
                ·
                  refine ⟨8019883182356973556704433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42772710305903858969090309 8019883182356973556704433)
                  ·
                    refine ⟨6014912386767730167528325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8019883182356973556704433 6014912386767730167528325)
                    ·
                      refine ⟨1127796072518949406411561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6014912386767730167528325 1127796072518949406411561)
                      ·
                        rfl

theorem cell23_2196375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_2196375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196375 prefixEnd_2196375 := by exact prefixLift 2196375
  have htrace : WordTrace (prefixWord ++ tailWord_2196375) baseStart_2196375 baseEnd_2196375 := by
    simpa [prefixWord, tailWord_2196375, baseEnd_2196375] using wordTrace_append hprefix tailTrace_2196375
  have hstable : (prefixWord ++ tailWord_2196375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196375).length < 2 ^ (prefixWord ++ tailWord_2196375).sum := by decide
  have hdescent : baseEnd_2196375 < baseStart_2196375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196436 : List Nat := [2, 4, 1, 2, 1, 3, 3, 2, 5]
def baseStart_2196436 : Nat := 118140960795 + 2196436 * 2 ^ 59
def prefixEnd_2196436 : Nat := 4983230072969 + 3 ^ 40 * 2196436 * 2
def baseEnd_2196436 : Nat := 125314154982097074194309

theorem tailTrace_2196436 : CollatzResearch.WordTrace tailWord_2196436 prefixEnd_2196436 125314154982097074194309 := by
  unfold tailWord_2196436
  simp only [CollatzResearch.WordTrace]
  refine ⟨40055301135347484124484581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53407068180463312165979441 40055301135347484124484581)
  ·
    refine ⟨7510368962877653273340859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40055301135347484124484581 7510368962877653273340859)
    ·
      refine ⟨11265553444316479910011289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7510368962877653273340859 11265553444316479910011289)
      ·
        refine ⟨8449165083237359932508467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11265553444316479910011289 8449165083237359932508467)
        ·
          refine ⟨12673747624856039898762701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8449165083237359932508467 12673747624856039898762701)
          ·
            refine ⟨4752655359321014962036013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12673747624856039898762701 4752655359321014962036013)
            ·
              refine ⟨1782245759745380610763505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4752655359321014962036013 1782245759745380610763505)
              ·
                refine ⟨1336684319809035458072629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782245759745380610763505 1336684319809035458072629)
                ·
                  refine ⟨125314154982097074194309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1336684319809035458072629 125314154982097074194309)
                  ·
                    rfl

theorem cell23_2196436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_2196436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196436 prefixEnd_2196436 := by exact prefixLift 2196436
  have htrace : WordTrace (prefixWord ++ tailWord_2196436) baseStart_2196436 baseEnd_2196436 := by
    simpa [prefixWord, tailWord_2196436, baseEnd_2196436] using wordTrace_append hprefix tailTrace_2196436
  have hstable : (prefixWord ++ tailWord_2196436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196436).length < 2 ^ (prefixWord ++ tailWord_2196436).sum := by decide
  have hdescent : baseEnd_2196436 < baseStart_2196436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196442 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_2196442 : Nat := 118140960795 + 2196442 * 2 ^ 59
def prefixEnd_2196442 : Nat := 4983230072969 + 3 ^ 40 * 2196442 * 2
def baseEnd_2196442 : Nat := 1127830475722800644273753

theorem tailTrace_2196442 : CollatzResearch.WordTrace tailWord_2196442 prefixEnd_2196442 1127830475722800644273753 := by
  unfold tailWord_2196442
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027705277168307818421895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53407214072448820849125053 20027705277168307818421895)
  ·
    refine ⟨30041557915752461727632843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20027705277168307818421895 30041557915752461727632843)
    ·
      refine ⟨45062336873628692591449265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30041557915752461727632843 45062336873628692591449265)
      ·
        refine ⟨33796752655221519443586949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45062336873628692591449265 33796752655221519443586949)
        ·
          refine ⟨6336891122854034895672553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33796752655221519443586949 6336891122854034895672553)
          ·
            refine ⟨4752668342140526171754415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6336891122854034895672553 4752668342140526171754415)
            ·
              refine ⟨7129002513210789257631623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4752668342140526171754415 7129002513210789257631623)
              ·
                refine ⟨10693503769816183886447435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129002513210789257631623 10693503769816183886447435)
                ·
                  refine ⟨16040255654724275829671153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10693503769816183886447435 16040255654724275829671153)
                  ·
                    refine ⟨12030191741043206872253365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16040255654724275829671153 12030191741043206872253365)
                    ·
                      refine ⟨1127830475722800644273753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12030191741043206872253365 1127830475722800644273753)
                      ·
                        rfl

theorem cell23_2196442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_2196442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196442 prefixEnd_2196442 := by exact prefixLift 2196442
  have htrace : WordTrace (prefixWord ++ tailWord_2196442) baseStart_2196442 baseEnd_2196442 := by
    simpa [prefixWord, tailWord_2196442, baseEnd_2196442] using wordTrace_append hprefix tailTrace_2196442
  have hstable : (prefixWord ++ tailWord_2196442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196442).length < 2 ^ (prefixWord ++ tailWord_2196442).sum := by decide
  have hdescent : baseEnd_2196442 < baseStart_2196442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196466 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_2196466 : Nat := 118140960795 + 2196466 * 2 ^ 59
def prefixEnd_2196466 : Nat := 4983230072969 + 3 ^ 40 * 2196466 * 2
def baseEnd_2196466 : Nat := 375947599752836183457881

theorem tailTrace_2196466 : CollatzResearch.WordTrace tailWord_2196466 prefixEnd_2196466 375947599752836183457881 := by
  unfold tailWord_2196466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20027924115146570843140313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53407797640390855581707501 20027924115146570843140313)
  ·
    refine ⟨15020943086359928132355235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20027924115146570843140313 15020943086359928132355235)
    ·
      refine ⟨22531414629539892198532853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15020943086359928132355235 22531414629539892198532853)
      ·
        refine ⟨2112320121519364893612455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22531414629539892198532853 2112320121519364893612455)
        ·
          refine ⟨3168480182279047340418683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112320121519364893612455 3168480182279047340418683)
          ·
            refine ⟨4752720273418571010628025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168480182279047340418683 4752720273418571010628025)
            ·
              refine ⟨3564540205063928257971019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4752720273418571010628025 3564540205063928257971019)
              ·
                refine ⟨5346810307595892386956529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3564540205063928257971019 5346810307595892386956529)
                ·
                  refine ⟨4010107730696919290217397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5346810307595892386956529 4010107730696919290217397)
                  ·
                    refine ⟨375947599752836183457881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4010107730696919290217397 375947599752836183457881)
                    ·
                      rfl

theorem cell23_2196466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_2196466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196466 prefixEnd_2196466 := by exact prefixLift 2196466
  have htrace : WordTrace (prefixWord ++ tailWord_2196466) baseStart_2196466 baseEnd_2196466 := by
    simpa [prefixWord, tailWord_2196466, baseEnd_2196466] using wordTrace_append hprefix tailTrace_2196466
  have hstable : (prefixWord ++ tailWord_2196466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196466).length < 2 ^ (prefixWord ++ tailWord_2196466).sum := by decide
  have hdescent : baseEnd_2196466 < baseStart_2196466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196492 : List Nat := [2, 2, 1, 2, 3, 2, 1, 4, 6]
def baseStart_2196492 : Nat := 118140960795 + 2196492 * 2 ^ 59
def prefixEnd_2196492 : Nat := 4983230072969 + 3 ^ 40 * 2196492 * 2
def baseEnd_2196492 : Nat := 125317349972836160960947

theorem tailTrace_2196492 : CollatzResearch.WordTrace tailWord_2196492 prefixEnd_2196492 125317349972836160960947 := by
  unfold tailWord_2196492
  simp only [CollatzResearch.WordTrace]
  refine ⟨40056322379246044906503865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53408429838994726542005153 40056322379246044906503865)
  ·
    refine ⟨30042241784434533679877899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40056322379246044906503865 30042241784434533679877899)
    ·
      refine ⟨45063362676651800519816849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30042241784434533679877899 45063362676651800519816849)
      ·
        refine ⟨33797522007488850389862637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45063362676651800519816849 33797522007488850389862637)
        ·
          refine ⟨12674070752808318896198489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33797522007488850389862637 12674070752808318896198489)
          ·
            refine ⟨9505553064606239172148867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12674070752808318896198489 9505553064606239172148867)
            ·
              refine ⟨14258329596909358758223301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9505553064606239172148867 14258329596909358758223301)
              ·
                refine ⟨2673436799420504767166869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14258329596909358758223301 2673436799420504767166869)
                ·
                  refine ⟨125317349972836160960947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2673436799420504767166869 125317349972836160960947)
                  ·
                    rfl

theorem cell23_2196492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 6].length) (baseStart_2196492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196492 prefixEnd_2196492 := by exact prefixLift 2196492
  have htrace : WordTrace (prefixWord ++ tailWord_2196492) baseStart_2196492 baseEnd_2196492 := by
    simpa [prefixWord, tailWord_2196492, baseEnd_2196492] using wordTrace_append hprefix tailTrace_2196492
  have hstable : (prefixWord ++ tailWord_2196492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196492).length < 2 ^ (prefixWord ++ tailWord_2196492).sum := by decide
  have hdescent : baseEnd_2196492 < baseStart_2196492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196529 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 1, 5, 2]
def baseStart_2196529 : Nat := 118140960795 + 2196529 * 2 ^ 59
def prefixEnd_2196529 : Nat := 4983230072969 + 3 ^ 40 * 2196529 * 2
def baseEnd_2196529 : Nat := 1127875148539741803885853

theorem tailTrace_2196529 : CollatzResearch.WordTrace tailWord_2196529 prefixEnd_2196529 1127875148539741803885853 := by
  unfold tailWord_2196529
  simp only [CollatzResearch.WordTrace]
  refine ⟨80113994259358045132104641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53409329506238696754736427 80113994259358045132104641)
  ·
    refine ⟨60085495694518533849078481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80113994259358045132104641 60085495694518533849078481)
    ·
      refine ⟨45064121770888900386808861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60085495694518533849078481 45064121770888900386808861)
      ·
        refine ⟨16899045664083337645053323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45064121770888900386808861 16899045664083337645053323)
        ·
          refine ⟨25348568496125006467579985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16899045664083337645053323 25348568496125006467579985)
          ·
            refine ⟨19011426372093754850684989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25348568496125006467579985 19011426372093754850684989)
            ·
              refine ⟨7129284889535158069006871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19011426372093754850684989 7129284889535158069006871)
              ·
                refine ⟨10693927334302737103510307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129284889535158069006871 10693927334302737103510307)
                ·
                  refine ⟨16040891001454105655265461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10693927334302737103510307 16040891001454105655265461)
                  ·
                    refine ⟨1503833531386322405181137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16040891001454105655265461 1503833531386322405181137)
                    ·
                      refine ⟨1127875148539741803885853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503833531386322405181137 1127875148539741803885853)
                      ·
                        rfl

theorem cell23_2196529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 5, 2].length) (baseStart_2196529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196529 prefixEnd_2196529 := by exact prefixLift 2196529
  have htrace : WordTrace (prefixWord ++ tailWord_2196529) baseStart_2196529 baseEnd_2196529 := by
    simpa [prefixWord, tailWord_2196529, baseEnd_2196529] using wordTrace_append hprefix tailTrace_2196529
  have hstable : (prefixWord ++ tailWord_2196529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196529).length < 2 ^ (prefixWord ++ tailWord_2196529).sum := by decide
  have hdescent : baseEnd_2196529 < baseStart_2196529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196573 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2196573 : Nat := 118140960795 + 2196573 * 2 ^ 59
def prefixEnd_2196573 : Nat := 4983230072969 + 3 ^ 40 * 2196573 * 2
def baseEnd_2196573 : Nat := 375965913896179877245217

theorem tailTrace_2196573 : CollatzResearch.WordTrace tailWord_2196573 prefixEnd_2196573 375965913896179877245217 := by
  unfold tailWord_2196573
  simp only [CollatzResearch.WordTrace]
  refine ⟨80115599071198640646706373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53410399380799093764470915 80115599071198640646706373)
  ·
    refine ⟨15021674825849745121257445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80115599071198640646706373 15021674825849745121257445)
    ·
      refine ⟨2816564029846827210235771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15021674825849745121257445 2816564029846827210235771)
      ·
        refine ⟨4224846044770240815353657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2816564029846827210235771 4224846044770240815353657)
        ·
          refine ⟨3168634533577680611515243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4224846044770240815353657 3168634533577680611515243)
          ·
            refine ⟨4752951800366520917272865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168634533577680611515243 4752951800366520917272865)
            ·
              refine ⟨3564713850274890687954649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4752951800366520917272865 3564713850274890687954649)
              ·
                refine ⟨2673535387706168015965987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564713850274890687954649 2673535387706168015965987)
                ·
                  refine ⟨4010303081559252023948981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673535387706168015965987 4010303081559252023948981)
                  ·
                    refine ⟨375965913896179877245217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4010303081559252023948981 375965913896179877245217)
                    ·
                      rfl

theorem cell23_2196573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2196573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196573 prefixEnd_2196573 := by exact prefixLift 2196573
  have htrace : WordTrace (prefixWord ++ tailWord_2196573) baseStart_2196573 baseEnd_2196573 := by
    simpa [prefixWord, tailWord_2196573, baseEnd_2196573] using wordTrace_append hprefix tailTrace_2196573
  have hstable : (prefixWord ++ tailWord_2196573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196573).length < 2 ^ (prefixWord ++ tailWord_2196573).sum := by decide
  have hdescent : baseEnd_2196573 < baseStart_2196573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196576 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 3, 2, 2]
def baseStart_2196576 : Nat := 118140960795 + 2196576 * 2 ^ 59
def prefixEnd_2196576 : Nat := 4983230072969 + 3 ^ 40 * 2196576 * 2
def baseEnd_2196576 : Nat := 1127899282130503119998137

theorem tailTrace_2196576 : CollatzResearch.WordTrace tailWord_2196576 prefixEnd_2196576 1127899282130503119998137 := by
  unfold tailWord_2196576
  simp only [CollatzResearch.WordTrace]
  refine ⟨40057854245093886079532791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53410472326791848106043721 40057854245093886079532791)
  ·
    refine ⟨60086781367640829119299187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40057854245093886079532791 60086781367640829119299187)
    ·
      refine ⟨90130172051461243678948781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60086781367640829119299187 90130172051461243678948781)
      ·
        refine ⟨33798814519297966379605793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90130172051461243678948781 33798814519297966379605793)
        ·
          refine ⟨25349110889473474784704345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33798814519297966379605793 25349110889473474784704345)
          ·
            refine ⟨19011833167105106088528259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25349110889473474784704345 19011833167105106088528259)
            ·
              refine ⟨28517749750657659132792389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19011833167105106088528259 28517749750657659132792389)
              ·
                refine ⟨5347078078248311087398573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28517749750657659132792389 5347078078248311087398573)
                ·
                  refine ⟨2005154279343116657774465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5347078078248311087398573 2005154279343116657774465)
                  ·
                    refine ⟨1503865709507337493330849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2005154279343116657774465 1503865709507337493330849)
                    ·
                      refine ⟨1127899282130503119998137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503865709507337493330849 1127899282130503119998137)
                      ·
                        rfl

theorem cell23_2196576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 3, 2, 2].length) (baseStart_2196576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196576 prefixEnd_2196576 := by exact prefixLift 2196576
  have htrace : WordTrace (prefixWord ++ tailWord_2196576) baseStart_2196576 baseEnd_2196576 := by
    simpa [prefixWord, tailWord_2196576, baseEnd_2196576] using wordTrace_append hprefix tailTrace_2196576
  have hstable : (prefixWord ++ tailWord_2196576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196576).length < 2 ^ (prefixWord ++ tailWord_2196576).sum := by decide
  have hdescent : baseEnd_2196576 < baseStart_2196576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196593 : List Nat := [1, 2, 2, 2, 1, 1, 2, 7, 1, 2, 2]
def baseStart_2196593 : Nat := 118140960795 + 2196593 * 2 ^ 59
def prefixEnd_2196593 : Nat := 4983230072969 + 3 ^ 40 * 2196593 * 2
def baseEnd_2196593 : Nat := 1127908011301629553485559

theorem tailTrace_2196593 : CollatzResearch.WordTrace tailWord_2196593 prefixEnd_2196593 1127908011301629553485559 := by
  unfold tailWord_2196593
  simp only [CollatzResearch.WordTrace]
  refine ⟨80116328531126184062434433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53410885687417456041622955 80116328531126184062434433)
  ·
    refine ⟨60087246398344638046825825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80116328531126184062434433 60087246398344638046825825)
    ·
      refine ⟨45065434798758478535119369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60087246398344638046825825 45065434798758478535119369)
      ·
        refine ⟨33799076099068858901339527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45065434798758478535119369 33799076099068858901339527)
        ·
          refine ⟨50698614148603288352009291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33799076099068858901339527 50698614148603288352009291)
          ·
            refine ⟨76047921222904932528013937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50698614148603288352009291 76047921222904932528013937)
            ·
              refine ⟨57035940917178699396010453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76047921222904932528013937 57035940917178699396010453)
              ·
                refine ⟨1336779865246375767093995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57035940917178699396010453 1336779865246375767093995)
                ·
                  refine ⟨2005169797869563650640993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1336779865246375767093995 2005169797869563650640993)
                  ·
                    refine ⟨1503877348402172737980745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2005169797869563650640993 1503877348402172737980745)
                    ·
                      refine ⟨1127908011301629553485559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503877348402172737980745 1127908011301629553485559)
                      ·
                        rfl

theorem cell23_2196593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 7, 1, 2, 2].length) (baseStart_2196593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196593 prefixEnd_2196593 := by exact prefixLift 2196593
  have htrace : WordTrace (prefixWord ++ tailWord_2196593) baseStart_2196593 baseEnd_2196593 := by
    simpa [prefixWord, tailWord_2196593, baseEnd_2196593] using wordTrace_append hprefix tailTrace_2196593
  have hstable : (prefixWord ++ tailWord_2196593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196593).length < 2 ^ (prefixWord ++ tailWord_2196593).sum := by decide
  have hdescent : baseEnd_2196593 < baseStart_2196593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196652 : List Nat := [2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 5]
def baseStart_2196652 : Nat := 118140960795 + 2196652 * 2 ^ 59
def prefixEnd_2196652 : Nat := 4983230072969 + 3 ^ 40 * 2196652 * 2
def baseEnd_2196652 : Nat := 1127938306660244822647787

theorem tailTrace_2196652 : CollatzResearch.WordTrace tailWord_2196652 prefixEnd_2196652 1127938306660244822647787 := by
  unfold tailWord_2196652
  simp only [CollatzResearch.WordTrace]
  refine ⟨40059240218956218569416105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53412320291941624759221473 40059240218956218569416105)
  ·
    refine ⟨30044430164217163927062079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40059240218956218569416105 30044430164217163927062079)
    ·
      refine ⟨45066645246325745890593119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30044430164217163927062079 45066645246325745890593119)
      ·
        refine ⟨67599967869488618835889679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45066645246325745890593119 67599967869488618835889679)
        ·
          refine ⟨101399951804232928253834519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67599967869488618835889679 101399951804232928253834519)
          ·
            refine ⟨152099927706349392380751779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101399951804232928253834519 152099927706349392380751779)
            ·
              refine ⟨228149891559524088571127669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152099927706349392380751779 228149891559524088571127669)
              ·
                refine ⟨21389052333705383303543219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 228149891559524088571127669 21389052333705383303543219)
                ·
                  refine ⟨32083578500558074955314829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21389052333705383303543219 32083578500558074955314829)
                  ·
                    refine ⟨12031341937709278108243061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32083578500558074955314829 12031341937709278108243061)
                    ·
                      refine ⟨1127938306660244822647787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12031341937709278108243061 1127938306660244822647787)
                      ·
                        rfl

theorem cell23_2196652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_2196652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196652 prefixEnd_2196652 := by exact prefixLift 2196652
  have htrace : WordTrace (prefixWord ++ tailWord_2196652) baseStart_2196652 baseEnd_2196652 := by
    simpa [prefixWord, tailWord_2196652, baseEnd_2196652] using wordTrace_append hprefix tailTrace_2196652
  have hstable : (prefixWord ++ tailWord_2196652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196652).length < 2 ^ (prefixWord ++ tailWord_2196652).sum := by decide
  have hdescent : baseEnd_2196652 < baseStart_2196652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196669 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2196669 : Nat := 118140960795 + 2196669 * 2 ^ 59
def prefixEnd_2196669 : Nat := 4983230072969 + 3 ^ 40 * 2196669 * 2
def baseEnd_2196669 : Nat := 1127947035831371256135209

theorem tailTrace_2196669 : CollatzResearch.WordTrace tailWord_2196669 prefixEnd_2196669 1127947035831371256135209 := by
  unfold tailWord_2196669
  simp only [CollatzResearch.WordTrace]
  refine ⟨80119100478850849042201061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53412733652567232694800707 80119100478850849042201061)
  ·
    refine ⟨15022331339784534195412699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80119100478850849042201061 15022331339784534195412699)
    ·
      refine ⟨22533497009676801293119049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15022331339784534195412699 22533497009676801293119049)
      ·
        refine ⟨16900122757257600969839287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22533497009676801293119049 16900122757257600969839287)
        ·
          refine ⟨25350184135886401454758931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16900122757257600969839287 25350184135886401454758931)
          ·
            refine ⟨38025276203829602182138397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25350184135886401454758931 38025276203829602182138397)
            ·
              refine ⟨14259478576436100818301899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38025276203829602182138397 14259478576436100818301899)
              ·
                refine ⟨21389217864654151227452849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14259478576436100818301899 21389217864654151227452849)
                ·
                  refine ⟨16041913398490613420589637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21389217864654151227452849 16041913398490613420589637)
                  ·
                    refine ⟨3007858762216990016360557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16041913398490613420589637 3007858762216990016360557)
                    ·
                      refine ⟨1127947035831371256135209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3007858762216990016360557 1127947035831371256135209)
                      ·
                        rfl

theorem cell23_2196669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2196669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196669 prefixEnd_2196669 := by exact prefixLift 2196669
  have htrace : WordTrace (prefixWord ++ tailWord_2196669) baseStart_2196669 baseEnd_2196669 := by
    simpa [prefixWord, tailWord_2196669, baseEnd_2196669] using wordTrace_append hprefix tailTrace_2196669
  have hstable : (prefixWord ++ tailWord_2196669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196669).length < 2 ^ (prefixWord ++ tailWord_2196669).sum := by decide
  have hdescent : baseEnd_2196669 < baseStart_2196669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196676 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2196676 : Nat := 118140960795 + 2196676 * 2 ^ 59
def prefixEnd_2196676 : Nat := 4983230072969 + 3 ^ 40 * 2196676 * 2
def baseEnd_2196676 : Nat := 375983543398650909582559

theorem tailTrace_2196676 : CollatzResearch.WordTrace tailWord_2196676 prefixEnd_2196676 375983543398650909582559 := by
  unfold tailWord_2196676
  simp only [CollatzResearch.WordTrace]
  refine ⟨40059677894912744618852941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53412903859883659491803921 40059677894912744618852941)
  ·
    refine ⟨15022379210592279232069853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40059677894912744618852941 15022379210592279232069853)
    ·
      refine ⟨5633392203972104712026195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15022379210592279232069853 5633392203972104712026195)
      ·
        refine ⟨8450088305958157068039293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5633392203972104712026195 8450088305958157068039293)
        ·
          refine ⟨3168783114734308900514735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8450088305958157068039293 3168783114734308900514735)
          ·
            refine ⟨4753174672101463350772103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168783114734308900514735 4753174672101463350772103)
            ·
              refine ⟨7129762008152195026158155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753174672101463350772103 7129762008152195026158155)
              ·
                refine ⟨10694643012228292539237233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7129762008152195026158155 10694643012228292539237233)
                ·
                  refine ⟨8020982259171219404427925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10694643012228292539237233 8020982259171219404427925)
                  ·
                    refine ⟨375983543398650909582559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8020982259171219404427925 375983543398650909582559)
                    ·
                      rfl

theorem cell23_2196676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2196676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196676 prefixEnd_2196676 := by exact prefixLift 2196676
  have htrace : WordTrace (prefixWord ++ tailWord_2196676) baseStart_2196676 baseEnd_2196676 := by
    simpa [prefixWord, tailWord_2196676, baseEnd_2196676] using wordTrace_append hprefix tailTrace_2196676
  have hstable : (prefixWord ++ tailWord_2196676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196676).length < 2 ^ (prefixWord ++ tailWord_2196676).sum := by decide
  have hdescent : baseEnd_2196676 < baseStart_2196676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196717 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2196717 : Nat := 118140960795 + 2196717 * 2 ^ 59
def prefixEnd_2196717 : Nat := 4983230072969 + 3 ^ 40 * 2196717 * 2
def baseEnd_2196717 : Nat := 1127971682902787068334989

theorem tailTrace_2196717 : CollatzResearch.WordTrace tailWord_2196717 prefixEnd_2196717 1127971682902787068334989 := by
  unfold tailWord_2196717
  simp only [CollatzResearch.WordTrace]
  refine ⟨80120851182676953239948405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53413900788451302159965603 80120851182676953239948405)
  ·
    refine ⟨7511329798375964366245163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80120851182676953239948405 7511329798375964366245163)
    ·
      refine ⟨11266994697563946549367745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7511329798375964366245163 11266994697563946549367745)
      ·
        refine ⟨8450246023172959912025809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11266994697563946549367745 8450246023172959912025809)
        ·
          refine ⟨6337684517379719934019357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8450246023172959912025809 6337684517379719934019357)
          ·
            refine ⟨2376631694017394975257259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6337684517379719934019357 2376631694017394975257259)
            ·
              refine ⟨3564947541026092462885889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2376631694017394975257259 3564947541026092462885889)
              ·
                refine ⟨2673710655769569347164417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564947541026092462885889 2673710655769569347164417)
                ·
                  refine ⟨2005282991827177010373313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2673710655769569347164417 2005282991827177010373313)
                  ·
                    refine ⟨1503962243870382757779985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2005282991827177010373313 1503962243870382757779985)
                    ·
                      refine ⟨1127971682902787068334989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1503962243870382757779985 1127971682902787068334989)
                      ·
                        rfl

theorem cell23_2196717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2196717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196717 prefixEnd_2196717 := by exact prefixLift 2196717
  have htrace : WordTrace (prefixWord ++ tailWord_2196717) baseStart_2196717 baseEnd_2196717 := by
    simpa [prefixWord, tailWord_2196717, baseEnd_2196717] using wordTrace_append hprefix tailTrace_2196717
  have hstable : (prefixWord ++ tailWord_2196717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196717).length < 2 ^ (prefixWord ++ tailWord_2196717).sum := by decide
  have hdescent : baseEnd_2196717 < baseStart_2196717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196739 : List Nat := [1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4]
def baseStart_2196739 : Nat := 118140960795 + 2196739 * 2 ^ 59
def prefixEnd_2196739 : Nat := 4983230072969 + 3 ^ 40 * 2196739 * 2
def baseEnd_2196739 : Nat := 1127982979477185982259887

theorem tailTrace_2196739 : CollatzResearch.WordTrace tailWord_2196739 prefixEnd_2196739 1127982979477185982259887 := by
  unfold tailWord_2196739
  simp only [CollatzResearch.WordTrace]
  refine ⟨80121653588597250997249271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53414435725731500664832847 80121653588597250997249271)
  ·
    refine ⟨120182480382895876495873907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80121653588597250997249271 120182480382895876495873907)
    ·
      refine ⟨180273720574343814743810861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120182480382895876495873907 180273720574343814743810861)
      ·
        refine ⟨67602645215378930528929073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180273720574343814743810861 67602645215378930528929073)
        ·
          refine ⟨50701983911534197896696805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67602645215378930528929073 50701983911534197896696805)
          ·
            refine ⟨9506621983412662105630651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50701983911534197896696805 9506621983412662105630651)
            ·
              refine ⟨14259932975118993158445977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9506621983412662105630651 14259932975118993158445977)
              ·
                refine ⟨10694949731339244868834483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14259932975118993158445977 10694949731339244868834483)
                ·
                  refine ⟨16042424597008867303251725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10694949731339244868834483 16042424597008867303251725)
                  ·
                    refine ⟨6015909223878325238719397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16042424597008867303251725 6015909223878325238719397)
                    ·
                      refine ⟨1127982979477185982259887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6015909223878325238719397 1127982979477185982259887)
                      ·
                        rfl

theorem cell23_2196739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_2196739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196739 prefixEnd_2196739 := by exact prefixLift 2196739
  have htrace : WordTrace (prefixWord ++ tailWord_2196739) baseStart_2196739 baseEnd_2196739 := by
    simpa [prefixWord, tailWord_2196739, baseEnd_2196739] using wordTrace_append hprefix tailTrace_2196739
  have hstable : (prefixWord ++ tailWord_2196739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196739).length < 2 ^ (prefixWord ++ tailWord_2196739).sum := by decide
  have hdescent : baseEnd_2196739 < baseStart_2196739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196796 : List Nat := [2, 2, 2, 2, 1, 4, 1, 3, 6]
def baseStart_2196796 : Nat := 118140960795 + 2196796 * 2 ^ 59
def prefixEnd_2196796 : Nat := 4983230072969 + 3 ^ 40 * 2196796 * 2
def baseEnd_2196796 : Nat := 125334694208276917694125

theorem tailTrace_2196796 : CollatzResearch.WordTrace tailWord_2196796 prefixEnd_2196796 125334694208276917694125 := by
  unfold tailWord_2196796
  simp only [CollatzResearch.WordTrace]
  refine ⟨40061866274695374866037121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53415821699593833154716161 40061866274695374866037121)
  ·
    refine ⟨30046399706021531149527841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40061866274695374866037121 30046399706021531149527841)
    ·
      refine ⟨22534799779516148362145881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30046399706021531149527841 22534799779516148362145881)
      ·
        refine ⟨16901099834637111271609411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22534799779516148362145881 16901099834637111271609411)
        ·
          refine ⟨25351649751955666907414117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16901099834637111271609411 25351649751955666907414117)
          ·
            refine ⟨4753434328491687545140147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25351649751955666907414117 4753434328491687545140147)
            ·
              refine ⟨7130151492737531317710221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753434328491687545140147 7130151492737531317710221)
              ·
                refine ⟨2673806809776574244141333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7130151492737531317710221 2673806809776574244141333)
                ·
                  refine ⟨125334694208276917694125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2673806809776574244141333 125334694208276917694125)
                  ·
                    rfl

theorem cell23_2196796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 6].length) (baseStart_2196796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196796 prefixEnd_2196796 := by exact prefixLift 2196796
  have htrace : WordTrace (prefixWord ++ tailWord_2196796) baseStart_2196796 baseEnd_2196796 := by
    simpa [prefixWord, tailWord_2196796, baseEnd_2196796] using wordTrace_append hprefix tailTrace_2196796
  have hstable : (prefixWord ++ tailWord_2196796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196796).length < 2 ^ (prefixWord ++ tailWord_2196796).sum := by decide
  have hdescent : baseEnd_2196796 < baseStart_2196796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196826 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_2196826 : Nat := 118140960795 + 2196826 * 2 ^ 59
def prefixEnd_2196826 : Nat := 4983230072969 + 3 ^ 40 * 2196826 * 2
def baseEnd_2196826 : Nat := 376009217431375713957329

theorem tailTrace_2196826 : CollatzResearch.WordTrace tailWord_2196826 prefixEnd_2196826 376009217431375713957329 := by
  unfold tailWord_2196826
  simp only [CollatzResearch.WordTrace]
  refine ⟨20031206684820516213916583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53416551159521376570444221 20031206684820516213916583)
  ·
    refine ⟨30046810027230774320874875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20031206684820516213916583 30046810027230774320874875)
    ·
      refine ⟨45070215040846161481312313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30046810027230774320874875 45070215040846161481312313)
      ·
        refine ⟨33802661280634621110984235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45070215040846161481312313 33802661280634621110984235)
        ·
          refine ⟨50703991920951931666476353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33802661280634621110984235 50703991920951931666476353)
          ·
            refine ⟨38027993940713948749857265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50703991920951931666476353 38027993940713948749857265)
            ·
              refine ⟨28520995455535461562392949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38027993940713948749857265 28520995455535461562392949)
              ·
                refine ⟨2673843323956449521474339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28520995455535461562392949 2673843323956449521474339)
                ·
                  refine ⟨4010764985934674282211509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2673843323956449521474339 4010764985934674282211509)
                  ·
                    refine ⟨376009217431375713957329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4010764985934674282211509 376009217431375713957329)
                    ·
                      rfl

theorem cell23_2196826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_2196826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196826 prefixEnd_2196826 := by exact prefixLift 2196826
  have htrace : WordTrace (prefixWord ++ tailWord_2196826) baseStart_2196826 baseEnd_2196826 := by
    simpa [prefixWord, tailWord_2196826, baseEnd_2196826] using wordTrace_append hprefix tailTrace_2196826
  have hstable : (prefixWord ++ tailWord_2196826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196826).length < 2 ^ (prefixWord ++ tailWord_2196826).sum := by decide
  have hdescent : baseEnd_2196826 < baseStart_2196826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196869 : List Nat := [1, 3, 1, 1, 3, 1, 2, 11]
def baseStart_2196869 : Nat := 118140960795 + 2196869 * 2 ^ 59
def prefixEnd_2196869 : Nat := 4983230072969 + 3 ^ 40 * 2196869 * 2
def baseEnd_2196869 : Nat := 41779619702306313838307

theorem tailTrace_2196869 : CollatzResearch.WordTrace tailWord_2196869 prefixEnd_2196869 41779619702306313838307 := by
  unfold tailWord_2196869
  simp only [CollatzResearch.WordTrace]
  refine ⟨80126395078126283199481661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53417596718750855466321107 80126395078126283199481661)
  ·
    refine ⟨30047398154297356199805623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80126395078126283199481661 30047398154297356199805623)
    ·
      refine ⟨45071097231446034299708435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30047398154297356199805623 45071097231446034299708435)
      ·
        refine ⟨67606645847169051449562653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45071097231446034299708435 67606645847169051449562653)
        ·
          refine ⟨25352492192688394293585995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67606645847169051449562653 25352492192688394293585995)
          ·
            refine ⟨38028738289032591440378993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25352492192688394293585995 38028738289032591440378993)
            ·
              refine ⟨28521553716774443580284245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38028738289032591440378993 28521553716774443580284245)
              ·
                refine ⟨41779619702306313838307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 28521553716774443580284245 41779619702306313838307)
                ·
                  rfl

theorem cell23_2196869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 11].length) (baseStart_2196869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196869 prefixEnd_2196869 := by exact prefixLift 2196869
  have htrace : WordTrace (prefixWord ++ tailWord_2196869) baseStart_2196869 baseEnd_2196869 := by
    simpa [prefixWord, tailWord_2196869, baseEnd_2196869] using wordTrace_append hprefix tailTrace_2196869
  have hstable : (prefixWord ++ tailWord_2196869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196869).length < 2 ^ (prefixWord ++ tailWord_2196869).sum := by decide
  have hdescent : baseEnd_2196869 < baseStart_2196869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196876 : List Nat := [2, 2, 1, 2, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2196876 : Nat := 118140960795 + 2196876 * 2 ^ 59
def prefixEnd_2196876 : Nat := 4983230072969 + 3 ^ 40 * 2196876 * 2
def baseEnd_2196876 : Nat := 1128053326326851946246757

theorem tailTrace_2196876 : CollatzResearch.WordTrace tailWord_2196876 prefixEnd_2196876 1128053326326851946246757 := by
  unfold tailWord_2196876
  simp only [CollatzResearch.WordTrace]
  refine ⟨40063325194550461697493241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53417766926067282263324321 40063325194550461697493241)
  ·
    refine ⟨30047493895912846273119931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40063325194550461697493241 30047493895912846273119931)
    ·
      refine ⟨45071240843869269409679897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30047493895912846273119931 45071240843869269409679897)
      ·
        refine ⟨33803430632901952057259923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45071240843869269409679897 33803430632901952057259923)
        ·
          refine ⟨50705145949352928085889885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33803430632901952057259923 50705145949352928085889885)
          ·
            refine ⟨19014429731007348032208707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50705145949352928085889885 19014429731007348032208707)
            ·
              refine ⟨28521644596511022048313061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19014429731007348032208707 28521644596511022048313061)
              ·
                refine ⟨5347808361845816634058699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28521644596511022048313061 5347808361845816634058699)
                ·
                  refine ⟨8021712542768724951088049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5347808361845816634058699 8021712542768724951088049)
                  ·
                    refine ⟨6016284407076543713316037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8021712542768724951088049 6016284407076543713316037)
                    ·
                      refine ⟨1128053326326851946246757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6016284407076543713316037 1128053326326851946246757)
                      ·
                        rfl

theorem cell23_2196876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2196876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196876 prefixEnd_2196876 := by exact prefixLift 2196876
  have htrace : WordTrace (prefixWord ++ tailWord_2196876) baseStart_2196876 baseEnd_2196876 := by
    simpa [prefixWord, tailWord_2196876, baseEnd_2196876] using wordTrace_append hprefix tailTrace_2196876
  have hstable : (prefixWord ++ tailWord_2196876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196876).length < 2 ^ (prefixWord ++ tailWord_2196876).sum := by decide
  have hdescent : baseEnd_2196876 < baseStart_2196876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2196998 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_2196998 : Nat := 118140960795 + 2196998 * 2 ^ 59
def prefixEnd_2196998 : Nat := 4983230072969 + 3 ^ 40 * 2196998 * 2
def baseEnd_2196998 : Nat := 1128115970966700468921197

theorem tailTrace_2196998 : CollatzResearch.WordTrace tailWord_2196998 prefixEnd_2196998 1128115970966700468921197 := by
  unfold tailWord_2196998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2504096877958091819716489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 53420733396439292153951765 2504096877958091819716489)
  ·
    refine ⟨1878072658468568864787367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2504096877958091819716489 1878072658468568864787367)
    ·
      refine ⟨2817108987702853297181051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1878072658468568864787367 2817108987702853297181051)
      ·
        refine ⟨4225663481554279945771577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2817108987702853297181051 4225663481554279945771577)
        ·
          refine ⟨3169247611165709959328683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4225663481554279945771577 3169247611165709959328683)
          ·
            refine ⟨4753871416748564938993025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169247611165709959328683 4753871416748564938993025)
            ·
              refine ⟨3565403562561423704244769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4753871416748564938993025 3565403562561423704244769)
              ·
                refine ⟨2674052671921067778183577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3565403562561423704244769 2674052671921067778183577)
                ·
                  refine ⟨2005539503940800833637683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2674052671921067778183577 2005539503940800833637683)
                  ·
                    refine ⟨3008309255911201250456525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005539503940800833637683 3008309255911201250456525)
                    ·
                      refine ⟨1128115970966700468921197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3008309255911201250456525 1128115970966700468921197)
                      ·
                        rfl

theorem cell23_2196998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_2196998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2196998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2196998 prefixEnd_2196998 := by exact prefixLift 2196998
  have htrace : WordTrace (prefixWord ++ tailWord_2196998) baseStart_2196998 baseEnd_2196998 := by
    simpa [prefixWord, tailWord_2196998, baseEnd_2196998] using wordTrace_append hprefix tailTrace_2196998
  have hstable : (prefixWord ++ tailWord_2196998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2196998).length < 2 ^ (prefixWord ++ tailWord_2196998).sum := by decide
  have hdescent : baseEnd_2196998 < baseStart_2196998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2196998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197004 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 2, 2, 2]
def baseStart_2197004 : Nat := 118140960795 + 2197004 * 2 ^ 59
def prefixEnd_2197004 : Nat := 4983230072969 + 3 ^ 40 * 2197004 * 2
def baseEnd_2197004 : Nat := 1128119051850627445446169

theorem tailTrace_2197004 : CollatzResearch.WordTrace tailWord_2197004 prefixEnd_2197004 1128119051850627445446169 := by
  unfold tailWord_2197004
  simp only [CollatzResearch.WordTrace]
  refine ⟨40065659466318600627823033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53420879288424800837097377 40065659466318600627823033)
  ·
    refine ⟨30049244599738950470867275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40065659466318600627823033 30049244599738950470867275)
    ·
      refine ⟨45073866899608425706300913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30049244599738950470867275 45073866899608425706300913)
      ·
        refine ⟨33805400174706319279725685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45073866899608425706300913 33805400174706319279725685)
        ·
          refine ⟨3169256266378717432474283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33805400174706319279725685 3169256266378717432474283)
          ·
            refine ⟨4753884399568076148711425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169256266378717432474283 4753884399568076148711425)
            ·
              refine ⟨3565413299676057111533569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4753884399568076148711425 3565413299676057111533569)
              ·
                refine ⟨2674059974757042833650177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3565413299676057111533569 2674059974757042833650177)
                ·
                  refine ⟨2005544981067782125237633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2674059974757042833650177 2005544981067782125237633)
                  ·
                    refine ⟨1504158735800836593928225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2005544981067782125237633 1504158735800836593928225)
                    ·
                      refine ⟨1128119051850627445446169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1504158735800836593928225 1128119051850627445446169)
                      ·
                        rfl

theorem cell23_2197004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_2197004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197004 prefixEnd_2197004 := by exact prefixLift 2197004
  have htrace : WordTrace (prefixWord ++ tailWord_2197004) baseStart_2197004 baseEnd_2197004 := by
    simpa [prefixWord, tailWord_2197004, baseEnd_2197004] using wordTrace_append hprefix tailTrace_2197004
  have hstable : (prefixWord ++ tailWord_2197004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197004).length < 2 ^ (prefixWord ++ tailWord_2197004).sum := by decide
  have hdescent : baseEnd_2197004 < baseStart_2197004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197043 : List Nat := [1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4]
def baseStart_2197043 : Nat := 118140960795 + 2197043 * 2 ^ 59
def prefixEnd_2197043 : Nat := 4983230072969 + 3 ^ 40 * 2197043 * 2
def baseEnd_2197043 : Nat := 1128139077596152792858489

theorem tailTrace_2197043 : CollatzResearch.WordTrace tailWord_2197043 prefixEnd_2197043 1128139077596152792858489 := by
  unfold tailWord_2197043
  simp only [CollatzResearch.WordTrace]
  refine ⟨80132741379495910916315783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53421827586330607277543855 80132741379495910916315783)
  ·
    refine ⟨120199112069243866374473675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80132741379495910916315783 120199112069243866374473675)
    ·
      refine ⟨180298668103865799561710513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120199112069243866374473675 180298668103865799561710513)
      ·
        refine ⟨135224001077899349671282885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180298668103865799561710513 135224001077899349671282885)
        ·
          refine ⟨25354500202106128063365541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135224001077899349671282885 25354500202106128063365541)
          ·
            refine ⟨4753968787894899011881039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25354500202106128063365541 4753968787894899011881039)
            ·
              refine ⟨7130953181842348517821559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4753968787894899011881039 7130953181842348517821559)
              ·
                refine ⟨10696429772763522776732339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7130953181842348517821559 10696429772763522776732339)
                ·
                  refine ⟨16044644659145284165098509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10696429772763522776732339 16044644659145284165098509)
                  ·
                    refine ⟨6016741747179481561911941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16044644659145284165098509 6016741747179481561911941)
                    ·
                      refine ⟨1128139077596152792858489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6016741747179481561911941 1128139077596152792858489)
                      ·
                        rfl

theorem cell23_2197043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_2197043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197043 prefixEnd_2197043 := by exact prefixLift 2197043
  have htrace : WordTrace (prefixWord ++ tailWord_2197043) baseStart_2197043 baseEnd_2197043 := by
    simpa [prefixWord, tailWord_2197043, baseEnd_2197043] using wordTrace_append hprefix tailTrace_2197043
  have hstable : (prefixWord ++ tailWord_2197043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197043).length < 2 ^ (prefixWord ++ tailWord_2197043).sum := by decide
  have hdescent : baseEnd_2197043 < baseStart_2197043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197104 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 1, 4]
def baseStart_2197104 : Nat := 118140960795 + 2197104 * 2 ^ 59
def prefixEnd_2197104 : Nat := 4983230072969 + 3 ^ 40 * 2197104 * 2
def baseEnd_2197104 : Nat := 376056799972025684731903

theorem tailTrace_2197104 : CollatzResearch.WordTrace tailWord_2197104 prefixEnd_2197104 376056799972025684731903 := by
  unfold tailWord_2197104
  simp only [CollatzResearch.WordTrace]
  refine ⟨40067483116137459167143183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53423310821516612222857577 40067483116137459167143183)
  ·
    refine ⟨60101224674206188750714775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40067483116137459167143183 60101224674206188750714775)
    ·
      refine ⟨90151837011309283126072163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60101224674206188750714775 90151837011309283126072163)
      ·
        refine ⟨135227755516963924689108245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90151837011309283126072163 135227755516963924689108245)
        ·
          refine ⟨6338801039857683969801949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135227755516963924689108245 6338801039857683969801949)
          ·
            refine ⟨2377050389946631488675731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6338801039857683969801949 2377050389946631488675731)
            ·
              refine ⟨3565575584919947233013597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377050389946631488675731 3565575584919947233013597)
              ·
                refine ⟨1337090844344980212380099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3565575584919947233013597 1337090844344980212380099)
                ·
                  refine ⟨2005636266517470318570149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337090844344980212380099 2005636266517470318570149)
                  ·
                    refine ⟨376056799972025684731903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2005636266517470318570149 376056799972025684731903)
                    ·
                      rfl

theorem cell23_2197104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 4].length) (baseStart_2197104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197104 prefixEnd_2197104 := by exact prefixLift 2197104
  have htrace : WordTrace (prefixWord ++ tailWord_2197104) baseStart_2197104 baseEnd_2197104 := by
    simpa [prefixWord, tailWord_2197104, baseEnd_2197104] using wordTrace_append hprefix tailTrace_2197104
  have hstable : (prefixWord ++ tailWord_2197104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197104).length < 2 ^ (prefixWord ++ tailWord_2197104).sum := by decide
  have hdescent : baseEnd_2197104 < baseStart_2197104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197127 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 3]
def baseStart_2197127 : Nat := 118140960795 + 2197127 * 2 ^ 59
def prefixEnd_2197127 : Nat := 4983230072969 + 3 ^ 40 * 2197127 * 2
def baseEnd_2197127 : Nat := 1128182209971130464208103

theorem tailTrace_2197127 : CollatzResearch.WordTrace tailWord_2197127 prefixEnd_2197127 1128182209971130464208103 := by
  unfold tailWord_2197127
  simp only [CollatzResearch.WordTrace]
  refine ⟨80135805111191593262373635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53423870074127728841582423 80135805111191593262373635)
  ·
    refine ⟨120203707666787389893560453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80135805111191593262373635 120203707666787389893560453)
    ·
      refine ⟨22538195187522635605042585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120203707666787389893560453 22538195187522635605042585)
      ·
        refine ⟨16903646390641976703781939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22538195187522635605042585 16903646390641976703781939)
        ·
          refine ⟨25355469585962965055672909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16903646390641976703781939 25355469585962965055672909)
          ·
            refine ⟨9508301094736111895877341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25355469585962965055672909 9508301094736111895877341)
            ·
              refine ⟨3565612910526041960954003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9508301094736111895877341 3565612910526041960954003)
              ·
                refine ⟨5348419365789062941431005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565612910526041960954003 5348419365789062941431005)
                ·
                  refine ⟨2005657262170898603036627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5348419365789062941431005 2005657262170898603036627)
                  ·
                    refine ⟨3008485893256347904554941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005657262170898603036627 3008485893256347904554941)
                    ·
                      refine ⟨1128182209971130464208103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3008485893256347904554941 1128182209971130464208103)
                      ·
                        rfl

theorem cell23_2197127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_2197127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197127 prefixEnd_2197127 := by exact prefixLift 2197127
  have htrace : WordTrace (prefixWord ++ tailWord_2197127) baseStart_2197127 baseEnd_2197127 := by
    simpa [prefixWord, tailWord_2197127, baseEnd_2197127] using wordTrace_append hprefix tailTrace_2197127
  have hstable : (prefixWord ++ tailWord_2197127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197127).length < 2 ^ (prefixWord ++ tailWord_2197127).sum := by decide
  have hdescent : baseEnd_2197127 < baseStart_2197127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197167 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 1, 1, 4]
def baseStart_2197167 : Nat := 118140960795 + 2197167 * 2 ^ 59
def prefixEnd_2197167 : Nat := 4983230072969 + 3 ^ 40 * 2197167 * 2
def baseEnd_2197167 : Nat := 1128202749197310307707919

theorem tailTrace_2197167 : CollatzResearch.WordTrace tailWord_2197167 prefixEnd_2197167 1128202749197310307707919 := by
  unfold tailWord_2197167
  simp only [CollatzResearch.WordTrace]
  refine ⟨80137264031046680093829755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53424842687364453395886503 80137264031046680093829755)
  ·
    refine ⟨120205896046570020140744633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80137264031046680093829755 120205896046570020140744633)
    ·
      refine ⟨90154422034927515105558475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120205896046570020140744633 90154422034927515105558475)
      ·
        refine ⟨135231633052391272658337713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90154422034927515105558475 135231633052391272658337713)
        ·
          refine ⟨101423724789293454493753285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135231633052391272658337713 101423724789293454493753285)
          ·
            refine ⟨19016948397992522717578741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101423724789293454493753285 19016948397992522717578741)
            ·
              refine ⟨1782838912311799004773007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19016948397992522717578741 1782838912311799004773007)
              ·
                refine ⟨2674258368467698507159511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782838912311799004773007 2674258368467698507159511)
                ·
                  refine ⟨4011387552701547760739267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674258368467698507159511 4011387552701547760739267)
                  ·
                    refine ⟨6017081329052321641108901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4011387552701547760739267 6017081329052321641108901)
                    ·
                      refine ⟨1128202749197310307707919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6017081329052321641108901 1128202749197310307707919)
                      ·
                        rfl

theorem cell23_2197167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 1, 1, 4].length) (baseStart_2197167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197167 prefixEnd_2197167 := by exact prefixLift 2197167
  have htrace : WordTrace (prefixWord ++ tailWord_2197167) baseStart_2197167 baseEnd_2197167 := by
    simpa [prefixWord, tailWord_2197167, baseEnd_2197167] using wordTrace_append hprefix tailTrace_2197167
  have hstable : (prefixWord ++ tailWord_2197167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197167).length < 2 ^ (prefixWord ++ tailWord_2197167).sum := by decide
  have hdescent : baseEnd_2197167 < baseStart_2197167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197170 : List Nat := [3, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2197170 : Nat := 118140960795 + 2197170 * 2 ^ 59
def prefixEnd_2197170 : Nat := 4983230072969 + 3 ^ 40 * 2197170 * 2
def baseEnd_2197170 : Nat := 1128204289639273795970405

theorem tailTrace_2197170 : CollatzResearch.WordTrace tailWord_2197170 prefixEnd_2197170 1128204289639273795970405 := by
  unfold tailWord_2197170
  simp only [CollatzResearch.WordTrace]
  refine ⟨20034343362508952901547241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53424915633357207737459309 20034343362508952901547241)
  ·
    refine ⟨15025757521881714676160431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20034343362508952901547241 15025757521881714676160431)
    ·
      refine ⟨22538636282822572014240647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15025757521881714676160431 22538636282822572014240647)
      ·
        refine ⟨33807954424233858021360971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22538636282822572014240647 33807954424233858021360971)
        ·
          refine ⟨50711931636350787032041457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33807954424233858021360971 50711931636350787032041457)
          ·
            refine ⟨38033948727263090274031093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50711931636350787032041457 38033948727263090274031093)
            ·
              refine ⟨3565682693180914713190415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38033948727263090274031093 3565682693180914713190415)
              ·
                refine ⟨5348524039771372069785623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565682693180914713190415 5348524039771372069785623)
                ·
                  refine ⟨8022786059657058104678435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5348524039771372069785623 8022786059657058104678435)
                  ·
                    refine ⟨12034179089485587157017653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8022786059657058104678435 12034179089485587157017653)
                    ·
                      refine ⟨1128204289639273795970405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12034179089485587157017653 1128204289639273795970405)
                      ·
                        rfl

theorem cell23_2197170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2197170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197170 prefixEnd_2197170 := by exact prefixLift 2197170
  have htrace : WordTrace (prefixWord ++ tailWord_2197170) baseStart_2197170 baseEnd_2197170 := by
    simpa [prefixWord, tailWord_2197170, baseEnd_2197170] using wordTrace_append hprefix tailTrace_2197170
  have hstable : (prefixWord ++ tailWord_2197170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197170).length < 2 ^ (prefixWord ++ tailWord_2197170).sum := by decide
  have hdescent : baseEnd_2197170 < baseStart_2197170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197173 : List Nat := [1, 3, 3, 3, 13]
def baseStart_2197173 : Nat := 118140960795 + 2197173 * 2 ^ 59
def prefixEnd_2197173 : Nat := 4983230072969 + 3 ^ 40 * 2197173 * 2
def baseEnd_2197173 : Nat := 1547607448671107385779

theorem tailTrace_2197173 : CollatzResearch.WordTrace tailWord_2197173 prefixEnd_2197173 1547607448671107385779 := by
  unfold tailWord_2197173
  simp only [CollatzResearch.WordTrace]
  refine ⟨80137482869024943118548173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53424988579349962079032115 80137482869024943118548173)
  ·
    refine ⟨30051556075884353669455565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80137482869024943118548173 30051556075884353669455565)
    ·
      refine ⟨11269333528456632626045837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30051556075884353669455565 11269333528456632626045837)
      ·
        refine ⟨4226000073171237234767189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11269333528456632626045837 4226000073171237234767189)
        ·
          refine ⟨1547607448671107385779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4226000073171237234767189 1547607448671107385779)
          ·
            rfl

theorem cell23_2197173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 13].length) (baseStart_2197173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197173 prefixEnd_2197173 := by exact prefixLift 2197173
  have htrace : WordTrace (prefixWord ++ tailWord_2197173) baseStart_2197173 baseEnd_2197173 := by
    simpa [prefixWord, tailWord_2197173, baseEnd_2197173] using wordTrace_append hprefix tailTrace_2197173
  have hstable : (prefixWord ++ tailWord_2197173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197173).length < 2 ^ (prefixWord ++ tailWord_2197173).sum := by decide
  have hdescent : baseEnd_2197173 < baseStart_2197173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197243 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5]
def baseStart_2197243 : Nat := 118140960795 + 2197243 * 2 ^ 59
def prefixEnd_2197243 : Nat := 4983230072969 + 3 ^ 40 * 2197243 * 2
def baseEnd_2197243 : Nat := 1128241773727052010357569

theorem tailTrace_2197243 : CollatzResearch.WordTrace tailWord_2197243 prefixEnd_2197243 1128241773727052010357569 := by
  unfold tailWord_2197243
  simp only [CollatzResearch.WordTrace]
  refine ⟨80140035978771345073596383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53426690652514230049064255 80140035978771345073596383)
  ·
    refine ⟨120210053968157017610394575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80140035978771345073596383 120210053968157017610394575)
    ·
      refine ⟨180315080952235526415591863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120210053968157017610394575 180315080952235526415591863)
      ·
        refine ⟨270472621428353289623387795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180315080952235526415591863 270472621428353289623387795)
        ·
          refine ⟨405708932142529934435081693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270472621428353289623387795 405708932142529934435081693)
          ·
            refine ⟨152140849553448725413155635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 405708932142529934435081693 152140849553448725413155635)
            ·
              refine ⟨228211274330173088119733453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152140849553448725413155635 228211274330173088119733453)
              ·
                refine ⟨85579227873814908044900045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228211274330173088119733453 85579227873814908044900045)
                ·
                  refine ⟨32092210452680590516837517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85579227873814908044900045 32092210452680590516837517)
                  ·
                    refine ⟨12034578919755221443814069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32092210452680590516837517 12034578919755221443814069)
                    ·
                      refine ⟨1128241773727052010357569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12034578919755221443814069 1128241773727052010357569)
                      ·
                        rfl

theorem cell23_2197243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 3, 5].length) (baseStart_2197243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197243 prefixEnd_2197243 := by exact prefixLift 2197243
  have htrace : WordTrace (prefixWord ++ tailWord_2197243) baseStart_2197243 baseEnd_2197243 := by
    simpa [prefixWord, tailWord_2197243, baseEnd_2197243] using wordTrace_append hprefix tailTrace_2197243
  have hstable : (prefixWord ++ tailWord_2197243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197243).length < 2 ^ (prefixWord ++ tailWord_2197243).sum := by decide
  have hdescent : baseEnd_2197243 < baseStart_2197243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197260 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 2, 4, 3]
def baseStart_2197260 : Nat := 118140960795 + 2197260 * 2 ^ 59
def prefixEnd_2197260 : Nat := 4983230072969 + 3 ^ 40 * 2197260 * 2
def baseEnd_2197260 : Nat := 1128250502898178443844991

theorem tailTrace_2197260 : CollatzResearch.WordTrace tailWord_2197260 prefixEnd_2197260 1128250502898178443844991 := by
  unfold tailWord_2197260
  simp only [CollatzResearch.WordTrace]
  refine ⟨40070328009854878488482617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53427104013139837984643489 40070328009854878488482617)
  ·
    refine ⟨30052746007391158866361963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40070328009854878488482617 30052746007391158866361963)
    ·
      refine ⟨45079119011086738299542945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30052746007391158866361963 45079119011086738299542945)
      ·
        refine ⟨33809339258315053724657209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45079119011086738299542945 33809339258315053724657209)
        ·
          refine ⟨25357004443736290293492907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33809339258315053724657209 25357004443736290293492907)
          ·
            refine ⟨38035506665604435440239361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25357004443736290293492907 38035506665604435440239361)
            ·
              refine ⟨28526629999203326580179521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38035506665604435440239361 28526629999203326580179521)
              ·
                refine ⟨21394972499402494935134641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28526629999203326580179521 21394972499402494935134641)
                ·
                  refine ⟨16046229374551871201350981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21394972499402494935134641 16046229374551871201350981)
                  ·
                    refine ⟨3008668007728475850253309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16046229374551871201350981 3008668007728475850253309)
                    ·
                      refine ⟨1128250502898178443844991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3008668007728475850253309 1128250502898178443844991)
                      ·
                        rfl

theorem cell23_2197260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_2197260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197260 prefixEnd_2197260 := by exact prefixLift 2197260
  have htrace : WordTrace (prefixWord ++ tailWord_2197260) baseStart_2197260 baseEnd_2197260 := by
    simpa [prefixWord, tailWord_2197260, baseEnd_2197260] using wordTrace_append hprefix tailTrace_2197260
  have hstable : (prefixWord ++ tailWord_2197260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197260).length < 2 ^ (prefixWord ++ tailWord_2197260).sum := by decide
  have hdescent : baseEnd_2197260 < baseStart_2197260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197263 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 9]
def baseStart_2197263 : Nat := 118140960795 + 2197263 * 2 ^ 59
def prefixEnd_2197263 : Nat := 4983230072969 + 3 ^ 40 * 2197263 * 2
def baseEnd_2197263 : Nat := 125361338148904659123053

theorem tailTrace_2197263 : CollatzResearch.WordTrace tailWord_2197263 prefixEnd_2197263 125361338148904659123053 := by
  unfold tailWord_2197263
  simp only [CollatzResearch.WordTrace]
  refine ⟨80140765438698888489324443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53427176959132592326216295 80140765438698888489324443)
  ·
    refine ⟨120211148158048332733986665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80140765438698888489324443 120211148158048332733986665)
    ·
      refine ⟨90158361118536249550489999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120211148158048332733986665 90158361118536249550489999)
      ·
        refine ⟨135237541677804374325734999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90158361118536249550489999 135237541677804374325734999)
        ·
          refine ⟨202856312516706561488602499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135237541677804374325734999 202856312516706561488602499)
          ·
            refine ⟨304284468775059842232903749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202856312516706561488602499 304284468775059842232903749)
            ·
              refine ⟨57053337895323720418669453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304284468775059842232903749 57053337895323720418669453)
              ·
                refine ⟨21395001710746395157001045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57053337895323720418669453 21395001710746395157001045)
                ·
                  refine ⟨125361338148904659123053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21395001710746395157001045 125361338148904659123053)
                  ·
                    rfl

theorem cell23_2197263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 9].length) (baseStart_2197263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197263 prefixEnd_2197263 := by exact prefixLift 2197263
  have htrace : WordTrace (prefixWord ++ tailWord_2197263) baseStart_2197263 baseEnd_2197263 := by
    simpa [prefixWord, tailWord_2197263, baseEnd_2197263] using wordTrace_append hprefix tailTrace_2197263
  have hstable : (prefixWord ++ tailWord_2197263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197263).length < 2 ^ (prefixWord ++ tailWord_2197263).sum := by decide
  have hdescent : baseEnd_2197263 < baseStart_2197263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197274 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2]
def baseStart_2197274 : Nat := 118140960795 + 2197274 * 2 ^ 59
def prefixEnd_2197274 : Nat := 4983230072969 + 3 ^ 40 * 2197274 * 2
def baseEnd_2197274 : Nat := 1128257691627341389069927

theorem tailTrace_2197274 : CollatzResearch.WordTrace tailWord_2197274 prefixEnd_2197274 1128257691627341389069927 := by
  unfold tailWord_2197274
  simp only [CollatzResearch.WordTrace]
  refine ⟨20035291660414759341993719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53427444427772691578649917 20035291660414759341993719)
  ·
    refine ⟨30052937490622139012990579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20035291660414759341993719 30052937490622139012990579)
    ·
      refine ⟨45079406235933208519485869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30052937490622139012990579 45079406235933208519485869)
      ·
        refine ⟨16904777338474953194807201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45079406235933208519485869 16904777338474953194807201)
        ·
          refine ⟨12678583003856214896105401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16904777338474953194807201 12678583003856214896105401)
          ·
            refine ⟨9508937252892161172079051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12678583003856214896105401 9508937252892161172079051)
            ·
              refine ⟨14263405879338241758118577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9508937252892161172079051 14263405879338241758118577)
              ·
                refine ⟨10697554409503681318588933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14263405879338241758118577 10697554409503681318588933)
                ·
                  refine ⟨2005791451781940247235425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10697554409503681318588933 2005791451781940247235425)
                  ·
                    refine ⟨1504343588836455185426569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2005791451781940247235425 1504343588836455185426569)
                    ·
                      refine ⟨1128257691627341389069927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1504343588836455185426569 1128257691627341389069927)
                      ·
                        rfl

theorem cell23_2197274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_2197274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197274 prefixEnd_2197274 := by exact prefixLift 2197274
  have htrace : WordTrace (prefixWord ++ tailWord_2197274) baseStart_2197274 baseEnd_2197274 := by
    simpa [prefixWord, tailWord_2197274, baseEnd_2197274] using wordTrace_append hprefix tailTrace_2197274
  have hstable : (prefixWord ++ tailWord_2197274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197274).length < 2 ^ (prefixWord ++ tailWord_2197274).sum := by decide
  have hdescent : baseEnd_2197274 < baseStart_2197274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197297 : List Nat := [1, 2, 2, 3, 2, 4, 1, 1, 7]
def baseStart_2197297 : Nat := 118140960795 + 2197297 * 2 ^ 59
def prefixEnd_2197297 : Nat := 4983230072969 + 3 ^ 40 * 2197297 * 2
def baseEnd_2197297 : Nat := 125363277964710533231369

theorem tailTrace_2197297 : CollatzResearch.WordTrace tailWord_2197297 prefixEnd_2197297 125363277964710533231369 := by
  unfold tailWord_2197297
  simp only [CollatzResearch.WordTrace]
  refine ⟨80142005520575712296062145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53428003680383808197374763 80142005520575712296062145)
  ·
    refine ⟨60106504140431784222046609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80142005520575712296062145 60106504140431784222046609)
    ·
      refine ⟨45079878105323838166534957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60106504140431784222046609 45079878105323838166534957)
      ·
        refine ⟨16904954289496439312450609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45079878105323838166534957 16904954289496439312450609)
        ·
          refine ⟨12678715717122329484337957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16904954289496439312450609 12678715717122329484337957)
          ·
            refine ⟨2377259196960436778313367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12678715717122329484337957 2377259196960436778313367)
            ·
              refine ⟨3565888795440655167470051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377259196960436778313367 3565888795440655167470051)
              ·
                refine ⟨5348833193160982751205077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3565888795440655167470051 5348833193160982751205077)
                ·
                  refine ⟨125363277964710533231369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5348833193160982751205077 125363277964710533231369)
                  ·
                    rfl

theorem cell23_2197297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 7].length) (baseStart_2197297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197297 prefixEnd_2197297 := by exact prefixLift 2197297
  have htrace : WordTrace (prefixWord ++ tailWord_2197297) baseStart_2197297 baseEnd_2197297 := by
    simpa [prefixWord, tailWord_2197297, baseEnd_2197297] using wordTrace_append hprefix tailTrace_2197297
  have hstable : (prefixWord ++ tailWord_2197297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197297).length < 2 ^ (prefixWord ++ tailWord_2197297).sum := by decide
  have hdescent : baseEnd_2197297 < baseStart_2197297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197348 : List Nat := [2, 3, 1, 1, 6, 1, 2, 2, 5]
def baseStart_2197348 : Nat := 118140960795 + 2197348 * 2 ^ 59
def prefixEnd_2197348 : Nat := 4983230072969 + 3 ^ 40 * 2197348 * 2
def baseEnd_2197348 : Nat := 125366187688419344393843

theorem tailTrace_2197348 : CollatzResearch.WordTrace tailWord_2197348 prefixEnd_2197348 125366187688419344393843 := by
  unfold tailWord_2197348
  simp only [CollatzResearch.WordTrace]
  refine ⟨40071932821695474003084349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53429243762260632004112465 40071932821695474003084349)
  ·
    refine ⟨15026974808135802751156631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40071932821695474003084349 15026974808135802751156631)
    ·
      refine ⟨22540462212203704126734947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15026974808135802751156631 22540462212203704126734947)
      ·
        refine ⟨33810693318305556190102421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22540462212203704126734947 33810693318305556190102421)
        ·
          refine ⟨1584876249295572946411051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 33810693318305556190102421 1584876249295572946411051)
          ·
            refine ⟨2377314373943359419616577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584876249295572946411051 2377314373943359419616577)
            ·
              refine ⟨1782985780457519564712433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2377314373943359419616577 1782985780457519564712433)
              ·
                refine ⟨1337239335343139673534325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1782985780457519564712433 1337239335343139673534325)
                ·
                  refine ⟨125366187688419344393843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1337239335343139673534325 125366187688419344393843)
                  ·
                    rfl

theorem cell23_2197348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_2197348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197348 prefixEnd_2197348 := by exact prefixLift 2197348
  have htrace : WordTrace (prefixWord ++ tailWord_2197348) baseStart_2197348 baseEnd_2197348 := by
    simpa [prefixWord, tailWord_2197348, baseEnd_2197348] using wordTrace_append hprefix tailTrace_2197348
  have hstable : (prefixWord ++ tailWord_2197348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197348).length < 2 ^ (prefixWord ++ tailWord_2197348).sum := by decide
  have hdescent : baseEnd_2197348 < baseStart_2197348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197360 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_2197360 : Nat := 118140960795 + 2197360 * 2 ^ 59
def prefixEnd_2197360 : Nat := 4983230072969 + 3 ^ 40 * 2197360 * 2
def baseEnd_2197360 : Nat := 1128301850963628052594531

theorem tailTrace_2197360 : CollatzResearch.WordTrace tailWord_2197360 prefixEnd_2197360 1128301850963628052594531 := by
  unfold tailWord_2197360
  simp only [CollatzResearch.WordTrace]
  refine ⟨40072151659673737027802767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53429535546231649370403689 40072151659673737027802767)
  ·
    refine ⟨60108227489510605541704151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40072151659673737027802767 60108227489510605541704151)
    ·
      refine ⟨90162341234265908312556227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60108227489510605541704151 90162341234265908312556227)
      ·
        refine ⟨135243511851398862468834341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90162341234265908312556227 135243511851398862468834341)
        ·
          refine ⟨25358158472137286712906439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135243511851398862468834341 25358158472137286712906439)
          ·
            refine ⟨38037237708205930069359659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25358158472137286712906439 38037237708205930069359659)
            ·
              refine ⟨57055856562308895104039489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38037237708205930069359659 57055856562308895104039489)
              ·
                refine ⟨42791892421731671328029617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57055856562308895104039489 42791892421731671328029617)
                ·
                  refine ⟨32093919316298753496022213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42791892421731671328029617 32093919316298753496022213)
                  ·
                    refine ⟨6017609871806016280504165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32093919316298753496022213 6017609871806016280504165)
                    ·
                      refine ⟨1128301850963628052594531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6017609871806016280504165 1128301850963628052594531)
                      ·
                        rfl

theorem cell23_2197360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_2197360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197360 prefixEnd_2197360 := by exact prefixLift 2197360
  have htrace : WordTrace (prefixWord ++ tailWord_2197360) baseStart_2197360 baseEnd_2197360 := by
    simpa [prefixWord, tailWord_2197360, baseEnd_2197360] using wordTrace_append hprefix tailTrace_2197360
  have hstable : (prefixWord ++ tailWord_2197360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197360).length < 2 ^ (prefixWord ++ tailWord_2197360).sum := by decide
  have hdescent : baseEnd_2197360 < baseStart_2197360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197384 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 1, 4, 3]
def baseStart_2197384 : Nat := 118140960795 + 2197384 * 2 ^ 59
def prefixEnd_2197384 : Nat := 4983230072969 + 3 ^ 40 * 2197384 * 2
def baseEnd_2197384 : Nat := 1128314174499335958694421

theorem tailTrace_2197384 : CollatzResearch.WordTrace tailWord_2197384 prefixEnd_2197384 1128314174499335958694421 := by
  unfold tailWord_2197384
  simp only [CollatzResearch.WordTrace]
  refine ⟨40072589335630263077239603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53430119114173684102986137 40072589335630263077239603)
  ·
    refine ⟨60108884003445394615859405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40072589335630263077239603 60108884003445394615859405)
    ·
      refine ⟨22540831501292022980947277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60108884003445394615859405 22540831501292022980947277)
      ·
        refine ⟨8452811812984508617855229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22540831501292022980947277 8452811812984508617855229)
        ·
          refine ⟨3169804429869190731695711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8452811812984508617855229 3169804429869190731695711)
          ·
            refine ⟨4754706644803786097543567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169804429869190731695711 4754706644803786097543567)
            ·
              refine ⟨7132059967205679146315351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754706644803786097543567 7132059967205679146315351)
              ·
                refine ⟨10698089950808518719473027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7132059967205679146315351 10698089950808518719473027)
                ·
                  refine ⟨16047134926212778079209541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10698089950808518719473027 16047134926212778079209541)
                  ·
                    refine ⟨3008837798664895889851789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16047134926212778079209541 3008837798664895889851789)
                    ·
                      refine ⟨1128314174499335958694421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3008837798664895889851789 1128314174499335958694421)
                      ·
                        rfl

theorem cell23_2197384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_2197384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197384 prefixEnd_2197384 := by exact prefixLift 2197384
  have htrace : WordTrace (prefixWord ++ tailWord_2197384) baseStart_2197384 baseEnd_2197384 := by
    simpa [prefixWord, tailWord_2197384, baseEnd_2197384] using wordTrace_append hprefix tailTrace_2197384
  have hstable : (prefixWord ++ tailWord_2197384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197384).length < 2 ^ (prefixWord ++ tailWord_2197384).sum := by decide
  have hdescent : baseEnd_2197384 < baseStart_2197384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197404 : List Nat := [2, 2, 3, 3, 1, 1, 3, 2, 6]
def baseStart_2197404 : Nat := 118140960795 + 2197404 * 2 ^ 59
def prefixEnd_2197404 : Nat := 4983230072969 + 3 ^ 40 * 2197404 * 2
def baseEnd_2197404 : Nat := 125369382679158431160481

theorem tailTrace_2197404 : CollatzResearch.WordTrace tailWord_2197404 prefixEnd_2197404 125369382679158431160481 := by
  unfold tailWord_2197404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40072954065594034785103633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53430605420792046380138177 40072954065594034785103633)
  ·
    refine ⟨30054715549195526088827725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40072954065594034785103633 30054715549195526088827725)
    ·
      refine ⟨11270518330948322283310397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30054715549195526088827725 11270518330948322283310397)
      ·
        refine ⟨4226444374105620856241399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11270518330948322283310397 4226444374105620856241399)
        ·
          refine ⟨6339666561158431284362099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4226444374105620856241399 6339666561158431284362099)
          ·
            refine ⟨9509499841737646926543149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339666561158431284362099 9509499841737646926543149)
            ·
              refine ⟨3566062440651617597453681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9509499841737646926543149 3566062440651617597453681)
              ·
                refine ⟨2674546830488713198090261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566062440651617597453681 2674546830488713198090261)
                ·
                  refine ⟨125369382679158431160481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2674546830488713198090261 125369382679158431160481)
                  ·
                    rfl

theorem cell23_2197404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 6].length) (baseStart_2197404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197404 prefixEnd_2197404 := by exact prefixLift 2197404
  have htrace : WordTrace (prefixWord ++ tailWord_2197404) baseStart_2197404 baseEnd_2197404 := by
    simpa [prefixWord, tailWord_2197404, baseEnd_2197404] using wordTrace_append hprefix tailTrace_2197404
  have hstable : (prefixWord ++ tailWord_2197404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197404).length < 2 ^ (prefixWord ++ tailWord_2197404).sum := by decide
  have hdescent : baseEnd_2197404 < baseStart_2197404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197448 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 1, 1, 3]
def baseStart_2197448 : Nat := 118140960795 + 2197448 * 2 ^ 59
def prefixEnd_2197448 : Nat := 4983230072969 + 3 ^ 40 * 2197448 * 2
def baseEnd_2197448 : Nat := 1128347037261223708294127

theorem tailTrace_2197448 : CollatzResearch.WordTrace tailWord_2197448 prefixEnd_2197448 1128347037261223708294127 := by
  unfold tailWord_2197448
  simp only [CollatzResearch.WordTrace]
  refine ⟨40073756471514332542404499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53431675295352443389872665 40073756471514332542404499)
  ·
    refine ⟨60110634707271498813606749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40073756471514332542404499 60110634707271498813606749)
    ·
      refine ⟨22541488015226812055102531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60110634707271498813606749 22541488015226812055102531)
      ·
        refine ⟨33812232022840218082653797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22541488015226812055102531 33812232022840218082653797)
        ·
          refine ⟨6339793504282540890497587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33812232022840218082653797 6339793504282540890497587)
          ·
            refine ⟨9509690256423811335746381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6339793504282540890497587 9509690256423811335746381)
            ·
              refine ⟨3566133846158929250904893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9509690256423811335746381 3566133846158929250904893)
              ·
                refine ⟨1337300192309598469089335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3566133846158929250904893 1337300192309598469089335)
                ·
                  refine ⟨2005950288464397703634003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337300192309598469089335 2005950288464397703634003)
                  ·
                    refine ⟨3008925432696596555451005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005950288464397703634003 3008925432696596555451005)
                    ·
                      refine ⟨1128347037261223708294127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3008925432696596555451005 1128347037261223708294127)
                      ·
                        rfl

theorem cell23_2197448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_2197448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197448 prefixEnd_2197448 := by exact prefixLift 2197448
  have htrace : WordTrace (prefixWord ++ tailWord_2197448) baseStart_2197448 baseEnd_2197448 := by
    simpa [prefixWord, tailWord_2197448, baseEnd_2197448] using wordTrace_append hprefix tailTrace_2197448
  have hstable : (prefixWord ++ tailWord_2197448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197448).length < 2 ^ (prefixWord ++ tailWord_2197448).sum := by decide
  have hdescent : baseEnd_2197448 < baseStart_2197448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197454 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4]
def baseStart_2197454 : Nat := 118140960795 + 2197454 * 2 ^ 59
def prefixEnd_2197454 : Nat := 4983230072969 + 3 ^ 40 * 2197454 * 2
def baseEnd_2197454 : Nat := 1128350118145150684819099

theorem tailTrace_2197454 : CollatzResearch.WordTrace tailWord_2197454 prefixEnd_2197454 1128350118145150684819099 := by
  unfold tailWord_2197454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10018466472625866013690927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53431821187337952073018277 10018466472625866013690927)
  ·
    refine ⟨15027699708938799020536391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10018466472625866013690927 15027699708938799020536391)
    ·
      refine ⟨22541549563408198530804587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15027699708938799020536391 22541549563408198530804587)
      ·
        refine ⟨33812324345112297796206881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22541549563408198530804587 33812324345112297796206881)
        ·
          refine ⟨25359243258834223347155161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33812324345112297796206881 25359243258834223347155161)
          ·
            refine ⟨19019432444125667510366371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25359243258834223347155161 19019432444125667510366371)
            ·
              refine ⟨28529148666188501265549557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19019432444125667510366371 28529148666188501265549557)
              ·
                refine ⟨2674607687455171993645271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28529148666188501265549557 2674607687455171993645271)
                ·
                  refine ⟨4011911531182757990467907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674607687455171993645271 4011911531182757990467907)
                  ·
                    refine ⟨6017867296774136985701861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4011911531182757990467907 6017867296774136985701861)
                    ·
                      refine ⟨1128350118145150684819099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6017867296774136985701861 1128350118145150684819099)
                      ·
                        rfl

theorem cell23_2197454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 1, 1, 4].length) (baseStart_2197454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197454 prefixEnd_2197454 := by exact prefixLift 2197454
  have htrace : WordTrace (prefixWord ++ tailWord_2197454) baseStart_2197454 baseEnd_2197454 := by
    simpa [prefixWord, tailWord_2197454, baseEnd_2197454] using wordTrace_append hprefix tailTrace_2197454
  have hstable : (prefixWord ++ tailWord_2197454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197454).length < 2 ^ (prefixWord ++ tailWord_2197454).sum := by decide
  have hdescent : baseEnd_2197454 < baseStart_2197454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197458 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_2197458 : Nat := 118140960795 + 2197458 * 2 ^ 59
def prefixEnd_2197458 : Nat := 4983230072969 + 3 ^ 40 * 2197458 * 2
def baseEnd_2197458 : Nat := 1128352172067768669169081

theorem tailTrace_2197458 : CollatzResearch.WordTrace tailWord_2197458 prefixEnd_2197458 1128352172067768669169081 := by
  unfold tailWord_2197458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20036969418248109198168257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53431918448661624528448685 20036969418248109198168257)
  ·
    refine ⟨15027727063686081898626193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20036969418248109198168257 15027727063686081898626193)
    ·
      refine ⟨11270795297764561423969645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15027727063686081898626193 11270795297764561423969645)
      ·
        refine ⟨4226548236661710533988617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11270795297764561423969645 4226548236661710533988617)
        ·
          refine ⟨3169911177496282900491463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4226548236661710533988617 3169911177496282900491463)
          ·
            refine ⟨4754866766244424350737195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169911177496282900491463 4754866766244424350737195)
            ·
              refine ⟨7132300149366636526105793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4754866766244424350737195 7132300149366636526105793)
              ·
                refine ⟨5349225112024977394579345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7132300149366636526105793 5349225112024977394579345)
                ·
                  refine ⟨4011918834018733045934509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349225112024977394579345 4011918834018733045934509)
                  ·
                    refine ⟨1504469562757024892225441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4011918834018733045934509 1504469562757024892225441)
                    ·
                      refine ⟨1128352172067768669169081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1504469562757024892225441 1128352172067768669169081)
                      ·
                        rfl

theorem cell23_2197458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_2197458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197458 prefixEnd_2197458 := by exact prefixLift 2197458
  have htrace : WordTrace (prefixWord ++ tailWord_2197458) baseStart_2197458 baseEnd_2197458 := by
    simpa [prefixWord, tailWord_2197458, baseEnd_2197458] using wordTrace_append hprefix tailTrace_2197458
  have hstable : (prefixWord ++ tailWord_2197458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197458).length < 2 ^ (prefixWord ++ tailWord_2197458).sum := by decide
  have hdescent : baseEnd_2197458 < baseStart_2197458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197464 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 2, 4]
def baseStart_2197464 : Nat := 118140960795 + 2197464 * 2 ^ 59
def prefixEnd_2197464 : Nat := 4983230072969 + 3 ^ 40 * 2197464 * 2
def baseEnd_2197464 : Nat := 376118417650565215231351

theorem tailTrace_2197464 : CollatzResearch.WordTrace tailWord_2197464 prefixEnd_2197464 376118417650565215231351 := by
  unfold tailWord_2197464
  simp only [CollatzResearch.WordTrace]
  refine ⟨40074048255485349908695723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53432064340647133211594297 40074048255485349908695723)
  ·
    refine ⟨60111072383228024863043585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40074048255485349908695723 60111072383228024863043585)
    ·
      refine ⟨45083304287421018647282689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60111072383228024863043585 45083304287421018647282689)
      ·
        refine ⟨33812478215565763985462017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45083304287421018647282689 33812478215565763985462017)
        ·
          refine ⟨25359358661674322989096513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33812478215565763985462017 25359358661674322989096513)
          ·
            refine ⟨19019518996255742241822385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25359358661674322989096513 19019518996255742241822385)
            ·
              refine ⟨14264639247191806681366789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19019518996255742241822385 14264639247191806681366789)
              ·
                refine ⟨2674619858848463752756273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14264639247191806681366789 2674619858848463752756273)
                ·
                  refine ⟨2005964894136347814567205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2674619858848463752756273 2005964894136347814567205)
                  ·
                    refine ⟨376118417650565215231351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2005964894136347814567205 376118417650565215231351)
                    ·
                      rfl

theorem cell23_2197464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_2197464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197464 prefixEnd_2197464 := by exact prefixLift 2197464
  have htrace : WordTrace (prefixWord ++ tailWord_2197464) baseStart_2197464 baseEnd_2197464 := by
    simpa [prefixWord, tailWord_2197464, baseEnd_2197464] using wordTrace_append hprefix tailTrace_2197464
  have hstable : (prefixWord ++ tailWord_2197464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197464).length < 2 ^ (prefixWord ++ tailWord_2197464).sum := by decide
  have hdescent : baseEnd_2197464 < baseStart_2197464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197465 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 1, 1, 3]
def baseStart_2197465 : Nat := 118140960795 + 2197465 * 2 ^ 59
def prefixEnd_2197465 : Nat := 4983230072969 + 3 ^ 40 * 2197465 * 2
def baseEnd_2197465 : Nat := 1128355766432350141781549

theorem tailTrace_2197465 : CollatzResearch.WordTrace tailWord_2197465 prefixEnd_2197465 1128355766432350141781549 := by
  unfold tailWord_2197465
  simp only [CollatzResearch.WordTrace]
  refine ⟨80148132983967076988177849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53432088655978051325451899 80148132983967076988177849)
  ·
    refine ⟨60111099737975307741133387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80148132983967076988177849 60111099737975307741133387)
    ·
      refine ⟨90166649606962961611700081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60111099737975307741133387 90166649606962961611700081)
      ·
        refine ⟨67624987205222221208775061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90166649606962961611700081 67624987205222221208775061)
        ·
          refine ⟨3169921275244791619161331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67624987205222221208775061 3169921275244791619161331)
          ·
            refine ⟨4754881912867187428741997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169921275244791619161331 4754881912867187428741997)
            ·
              refine ⟨1783080717325195285778249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4754881912867187428741997 1783080717325195285778249)
              ·
                refine ⟨1337310537993896464333687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1783080717325195285778249 1337310537993896464333687)
                ·
                  refine ⟨2005965806990844696500531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337310537993896464333687 2005965806990844696500531)
                  ·
                    refine ⟨3008948710486267044750797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2005965806990844696500531 3008948710486267044750797)
                    ·
                      refine ⟨1128355766432350141781549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3008948710486267044750797 1128355766432350141781549)
                      ·
                        rfl

theorem cell23_2197465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 1, 3].length) (baseStart_2197465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197465 prefixEnd_2197465 := by exact prefixLift 2197465
  have htrace : WordTrace (prefixWord ++ tailWord_2197465) baseStart_2197465 baseEnd_2197465 := by
    simpa [prefixWord, tailWord_2197465, baseEnd_2197465] using wordTrace_append hprefix tailTrace_2197465
  have hstable : (prefixWord ++ tailWord_2197465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197465).length < 2 ^ (prefixWord ++ tailWord_2197465).sum := by decide
  have hdescent : baseEnd_2197465 < baseStart_2197465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197485 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2197485 : Nat := 118140960795 + 2197485 * 2 ^ 59
def prefixEnd_2197485 : Nat := 4983230072969 + 3 ^ 40 * 2197485 * 2
def baseEnd_2197485 : Nat := 376122012015146687843819

theorem tailTrace_2197485 : CollatzResearch.WordTrace tailWord_2197485 prefixEnd_2197485 376122012015146687843819 := by
  unfold tailWord_2197485
  simp only [CollatzResearch.WordTrace]
  refine ⟨80148862443894620403905909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53432574962596413602603939 80148862443894620403905909)
  ·
    refine ⟨7513955854115120662866179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80148862443894620403905909 7513955854115120662866179)
    ·
      refine ⟨11270933781172680994299269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7513955854115120662866179 11270933781172680994299269)
      ·
        refine ⟨2113300083969877686431113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11270933781172680994299269 2113300083969877686431113)
        ·
          refine ⟨1584975062977408264823335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113300083969877686431113 1584975062977408264823335)
          ·
            refine ⟨2377462594466112397235003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584975062977408264823335 2377462594466112397235003)
            ·
              refine ⟨3566193891699168595852505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377462594466112397235003 3566193891699168595852505)
              ·
                refine ⟨2674645418774376446889379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566193891699168595852505 2674645418774376446889379)
                ·
                  refine ⟨4011968128161564670334069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2674645418774376446889379 4011968128161564670334069)
                  ·
                    refine ⟨376122012015146687843819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4011968128161564670334069 376122012015146687843819)
                    ·
                      rfl

theorem cell23_2197485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2197485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197485 prefixEnd_2197485 := by exact prefixLift 2197485
  have htrace : WordTrace (prefixWord ++ tailWord_2197485) baseStart_2197485 baseEnd_2197485 := by
    simpa [prefixWord, tailWord_2197485, baseEnd_2197485] using wordTrace_append hprefix tailTrace_2197485
  have hstable : (prefixWord ++ tailWord_2197485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197485).length < 2 ^ (prefixWord ++ tailWord_2197485).sum := by decide
  have hdescent : baseEnd_2197485 < baseStart_2197485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197504 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 4, 1, 3]
def baseStart_2197504 : Nat := 118140960795 + 2197504 * 2 ^ 59
def prefixEnd_2197504 : Nat := 4983230072969 + 3 ^ 40 * 2197504 * 2
def baseEnd_2197504 : Nat := 1128375792177875489193869

theorem tailTrace_2197504 : CollatzResearch.WordTrace tailWord_2197504 prefixEnd_2197504 1128375792177875489193869 := by
  unfold tailWord_2197504
  simp only [CollatzResearch.WordTrace]
  refine ⟨40074777715412893324423783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53433036953883857765898377 40074777715412893324423783)
  ·
    refine ⟨60112166573119339986635675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40074777715412893324423783 60112166573119339986635675)
    ·
      refine ⟨90168249859679009979953513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60112166573119339986635675 90168249859679009979953513)
      ·
        refine ⟨67626187394759257484965135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90168249859679009979953513 67626187394759257484965135)
        ·
          refine ⟨101439281092138886227447703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67626187394759257484965135 101439281092138886227447703)
          ·
            refine ⟨152158921638208329341171555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101439281092138886227447703 152158921638208329341171555)
            ·
              refine ⟨228238382457312494011757333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152158921638208329341171555 228238382457312494011757333)
              ·
                refine ⟨10698674177686523156801125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228238382457312494011757333 10698674177686523156801125)
                ·
                  refine ⟨2006001408316223091900211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10698674177686523156801125 2006001408316223091900211)
                  ·
                    refine ⟨3009002112474334637850317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2006001408316223091900211 3009002112474334637850317)
                    ·
                      refine ⟨1128375792177875489193869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3009002112474334637850317 1128375792177875489193869)
                      ·
                        rfl

theorem cell23_2197504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 1, 3].length) (baseStart_2197504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197504 prefixEnd_2197504 := by exact prefixLift 2197504
  have htrace : WordTrace (prefixWord ++ tailWord_2197504) baseStart_2197504 baseEnd_2197504 := by
    simpa [prefixWord, tailWord_2197504, baseEnd_2197504] using wordTrace_append hprefix tailTrace_2197504
  have hstable : (prefixWord ++ tailWord_2197504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197504).length < 2 ^ (prefixWord ++ tailWord_2197504).sum := by decide
  have hdescent : baseEnd_2197504 < baseStart_2197504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197508 : List Nat := [2, 3, 2, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2197508 : Nat := 118140960795 + 2197508 * 2 ^ 59
def prefixEnd_2197508 : Nat := 4983230072969 + 3 ^ 40 * 2197508 * 2
def baseEnd_2197508 : Nat := 1128377846100493473543851

theorem tailTrace_2197508 : CollatzResearch.WordTrace tailWord_2197508 prefixEnd_2197508 1128377846100493473543851 := by
  unfold tailWord_2197508
  simp only [CollatzResearch.WordTrace]
  refine ⟨40074850661405647665996589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53433134215207530221328785 40074850661405647665996589)
  ·
    refine ⟨15028068998027117874748721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40074850661405647665996589 15028068998027117874748721)
    ·
      refine ⟨11271051748520338406061541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15028068998027117874748721 11271051748520338406061541)
      ·
        refine ⟨2113322202847563451136539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11271051748520338406061541 2113322202847563451136539)
        ·
          refine ⟨3169983304271345176704809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2113322202847563451136539 3169983304271345176704809)
          ·
            refine ⟨2377487478203508882528607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3169983304271345176704809 2377487478203508882528607)
            ·
              refine ⟨3566231217305263323792911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377487478203508882528607 3566231217305263323792911)
              ·
                refine ⟨5349346825957894985689367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566231217305263323792911 5349346825957894985689367)
                ·
                  refine ⟨8024020238936842478534051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5349346825957894985689367 8024020238936842478534051)
                  ·
                    refine ⟨12036030358405263717801077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8024020238936842478534051 12036030358405263717801077)
                    ·
                      refine ⟨1128377846100493473543851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12036030358405263717801077 1128377846100493473543851)
                      ·
                        rfl

theorem cell23_2197508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2197508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197508 prefixEnd_2197508 := by exact prefixLift 2197508
  have htrace : WordTrace (prefixWord ++ tailWord_2197508) baseStart_2197508 baseEnd_2197508 := by
    simpa [prefixWord, tailWord_2197508, baseEnd_2197508] using wordTrace_append hprefix tailTrace_2197508
  have hstable : (prefixWord ++ tailWord_2197508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197508).length < 2 ^ (prefixWord ++ tailWord_2197508).sum := by decide
  have hdescent : baseEnd_2197508 < baseStart_2197508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197547 : List Nat := [1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5]
def baseStart_2197547 : Nat := 118140960795 + 2197547 * 2 ^ 59
def prefixEnd_2197547 : Nat := 4983230072969 + 3 ^ 40 * 2197547 * 2
def baseEnd_2197547 : Nat := 1128397871846018820956171

theorem tailTrace_2197547 : CollatzResearch.WordTrace tailWord_2197547 prefixEnd_2197547 1128397871846018820956171 := by
  unfold tailWord_2197547
  simp only [CollatzResearch.WordTrace]
  refine ⟨80151123769670004992662895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53434082513113336661775263 80151123769670004992662895)
  ·
    refine ⟨120226685654505007488994343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80151123769670004992662895 120226685654505007488994343)
    ·
      refine ⟨180340028481757511233491515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120226685654505007488994343 180340028481757511233491515)
      ·
        refine ⟨270510042722636266850237273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180340028481757511233491515 270510042722636266850237273)
        ·
          refine ⟨202882532041977200137677955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270510042722636266850237273 202882532041977200137677955)
          ·
            refine ⟨304323798062965800206516933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202882532041977200137677955 304323798062965800206516933)
            ·
              refine ⟨57060712136806087538721925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 304323798062965800206516933 57060712136806087538721925)
              ·
                refine ⟨10698883525651141413510361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57060712136806087538721925 10698883525651141413510361)
                ·
                  refine ⟨8024162644238356060132771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10698883525651141413510361 8024162644238356060132771)
                  ·
                    refine ⟨12036243966357534090199157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8024162644238356060132771 12036243966357534090199157)
                    ·
                      refine ⟨1128397871846018820956171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12036243966357534090199157 1128397871846018820956171)
                      ·
                        rfl

theorem cell23_2197547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 1, 5].length) (baseStart_2197547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197547 prefixEnd_2197547 := by exact prefixLift 2197547
  have htrace : WordTrace (prefixWord ++ tailWord_2197547) baseStart_2197547 baseEnd_2197547 := by
    simpa [prefixWord, tailWord_2197547, baseEnd_2197547] using wordTrace_append hprefix tailTrace_2197547
  have hstable : (prefixWord ++ tailWord_2197547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197547).length < 2 ^ (prefixWord ++ tailWord_2197547).sum := by decide
  have hdescent : baseEnd_2197547 < baseStart_2197547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197594 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3]
def baseStart_2197594 : Nat := 118140960795 + 2197594 * 2 ^ 59
def prefixEnd_2197594 : Nat := 4983230072969 + 3 ^ 40 * 2197594 * 2
def baseEnd_2197594 : Nat := 1128422005436780137068455

theorem tailTrace_2197594 : CollatzResearch.WordTrace tailWord_2197594 prefixEnd_2197594 1128422005436780137068455 := by
  unfold tailWord_2197594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20038209500124933004905959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53435225333666488013082557 20038209500124933004905959)
  ·
    refine ⟨30057314250187399507358939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20038209500124933004905959 30057314250187399507358939)
    ·
      refine ⟨45085971375281099261038409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30057314250187399507358939 45085971375281099261038409)
      ·
        refine ⟨33814478531460824445778807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45085971375281099261038409 33814478531460824445778807)
        ·
          refine ⟨50721717797191236668668211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33814478531460824445778807 50721717797191236668668211)
          ·
            refine ⟨76082576695786855003002317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50721717797191236668668211 76082576695786855003002317)
            ·
              refine ⟨28530966260920070626125869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76082576695786855003002317 28530966260920070626125869)
              ·
                refine ⟨10699112347845026484797201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28530966260920070626125869 10699112347845026484797201)
                ·
                  refine ⟨8024334260883769863597901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10699112347845026484797201 8024334260883769863597901)
                  ·
                    refine ⟨3009125347831413698849213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8024334260883769863597901 3009125347831413698849213)
                    ·
                      refine ⟨1128422005436780137068455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3009125347831413698849213 1128422005436780137068455)
                      ·
                        rfl

theorem cell23_2197594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3].length) (baseStart_2197594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197594 prefixEnd_2197594 := by exact prefixLift 2197594
  have htrace : WordTrace (prefixWord ++ tailWord_2197594) baseStart_2197594 baseEnd_2197594 := by
    simpa [prefixWord, tailWord_2197594, baseEnd_2197594] using wordTrace_append hprefix tailTrace_2197594
  have hstable : (prefixWord ++ tailWord_2197594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197594).length < 2 ^ (prefixWord ++ tailWord_2197594).sum := by decide
  have hdescent : baseEnd_2197594 < baseStart_2197594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197614 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_2197614 : Nat := 118140960795 + 2197614 * 2 ^ 59
def prefixEnd_2197614 : Nat := 4983230072969 + 3 ^ 40 * 2197614 * 2
def baseEnd_2197614 : Nat := 376144091683290019606121

theorem tailTrace_2197614 : CollatzResearch.WordTrace tailWord_2197614 prefixEnd_2197614 376144091683290019606121 := by
  unfold tailWord_2197614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10019195932553409429418987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53435711640284850290234597 10019195932553409429418987)
  ·
    refine ⟨15028793898830114144128481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10019195932553409429418987 15028793898830114144128481)
    ·
      refine ⟨11271595424122585608096361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15028793898830114144128481 11271595424122585608096361)
      ·
        refine ⟨8453696568091939206072271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11271595424122585608096361 8453696568091939206072271)
        ·
          refine ⟨12680544852137908809108407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8453696568091939206072271 12680544852137908809108407)
          ·
            refine ⟨19020817278206863213662611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12680544852137908809108407 19020817278206863213662611)
            ·
              refine ⟨28531225917310294820493917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19020817278206863213662611 28531225917310294820493917)
              ·
                refine ⟨10699209718991360557685219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28531225917310294820493917 10699209718991360557685219)
                ·
                  refine ⟨16048814578487040836527829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10699209718991360557685219 16048814578487040836527829)
                  ·
                    refine ⟨376144091683290019606121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16048814578487040836527829 376144091683290019606121)
                    ·
                      rfl

theorem cell23_2197614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_2197614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197614 prefixEnd_2197614 := by exact prefixLift 2197614
  have htrace : WordTrace (prefixWord ++ tailWord_2197614) baseStart_2197614 baseEnd_2197614 := by
    simpa [prefixWord, tailWord_2197614, baseEnd_2197614] using wordTrace_append hprefix tailTrace_2197614
  have hstable : (prefixWord ++ tailWord_2197614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197614).length < 2 ^ (prefixWord ++ tailWord_2197614).sum := by decide
  have hdescent : baseEnd_2197614 < baseStart_2197614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197618 : List Nat := [3, 2, 1, 2, 2, 4, 1, 3, 5]
def baseStart_2197618 : Nat := 118140960795 + 2197618 * 2 ^ 59
def prefixEnd_2197618 : Nat := 4983230072969 + 3 ^ 40 * 2197618 * 2
def baseEnd_2197618 : Nat := 125381592108054227018705

theorem tailTrace_2197618 : CollatzResearch.WordTrace tailWord_2197618 prefixEnd_2197618 125381592108054227018705 := by
  unfold tailWord_2197618
  simp only [CollatzResearch.WordTrace]
  refine ⟨20038428338103196029624377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53435808901608522745665005 20038428338103196029624377)
  ·
    refine ⟨15028821253577397022218283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20038428338103196029624377 15028821253577397022218283)
    ·
      refine ⟨22543231880366095533327425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15028821253577397022218283 22543231880366095533327425)
      ·
        refine ⟨16907423910274571649995569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22543231880366095533327425 16907423910274571649995569)
        ·
          refine ⟨12680567932705928737496677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16907423910274571649995569 12680567932705928737496677)
          ·
            refine ⟨2377606487382361638280627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12680567932705928737496677 2377606487382361638280627)
            ·
              refine ⟨3566409731073542457420941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377606487382361638280627 3566409731073542457420941)
              ·
                refine ⟨1337403649152578421532853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3566409731073542457420941 1337403649152578421532853)
                ·
                  refine ⟨125381592108054227018705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1337403649152578421532853 125381592108054227018705)
                  ·
                    rfl

theorem cell23_2197618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_2197618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197618 prefixEnd_2197618 := by exact prefixLift 2197618
  have htrace : WordTrace (prefixWord ++ tailWord_2197618) baseStart_2197618 baseEnd_2197618 := by
    simpa [prefixWord, tailWord_2197618, baseEnd_2197618] using wordTrace_append hprefix tailTrace_2197618
  have hstable : (prefixWord ++ tailWord_2197618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197618).length < 2 ^ (prefixWord ++ tailWord_2197618).sum := by decide
  have hdescent : baseEnd_2197618 < baseStart_2197618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197668 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_2197668 : Nat := 118140960795 + 2197668 * 2 ^ 59
def prefixEnd_2197668 : Nat := 4983230072969 + 3 ^ 40 * 2197668 * 2
def baseEnd_2197668 : Nat := 1128460003005212847543115

theorem tailTrace_2197668 : CollatzResearch.WordTrace tailWord_2197668 prefixEnd_2197668 1128460003005212847543115 := by
  unfold tailWord_2197668
  simp only [CollatzResearch.WordTrace]
  refine ⟨40077768501115821328908829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53437024668154428438545105 40077768501115821328908829)
  ·
    refine ⟨15029163187918432998340811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40077768501115821328908829 15029163187918432998340811)
    ·
      refine ⟨22543744781877649497511217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15029163187918432998340811 22543744781877649497511217)
      ·
        refine ⟨16907808586408237123133413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22543744781877649497511217 16907808586408237123133413)
        ·
          refine ⟨3170214109951544460587515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16907808586408237123133413 3170214109951544460587515)
          ·
            refine ⟨4755321164927316690881273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3170214109951544460587515 4755321164927316690881273)
            ·
              refine ⟨3566490873695487518160955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4755321164927316690881273 3566490873695487518160955)
              ·
                refine ⟨5349736310543231277241433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566490873695487518160955 5349736310543231277241433)
                ·
                  refine ⟨4012302232907423457931075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5349736310543231277241433 4012302232907423457931075)
                  ·
                    refine ⟨6018453349361135186896613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012302232907423457931075 6018453349361135186896613)
                    ·
                      refine ⟨1128460003005212847543115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6018453349361135186896613 1128460003005212847543115)
                      ·
                        rfl

theorem cell23_2197668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_2197668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197668 prefixEnd_2197668 := by exact prefixLift 2197668
  have htrace : WordTrace (prefixWord ++ tailWord_2197668) baseStart_2197668 baseEnd_2197668 := by
    simpa [prefixWord, tailWord_2197668, baseEnd_2197668] using wordTrace_append hprefix tailTrace_2197668
  have hstable : (prefixWord ++ tailWord_2197668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197668).length < 2 ^ (prefixWord ++ tailWord_2197668).sum := by decide
  have hdescent : baseEnd_2197668 < baseStart_2197668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197711 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 1, 5, 2]
def baseStart_2197711 : Nat := 118140960795 + 2197711 * 2 ^ 59
def prefixEnd_2197711 : Nat := 4983230072969 + 3 ^ 40 * 2197711 * 2
def baseEnd_2197711 : Nat := 1128482082673356179305417

theorem tailTrace_2197711 : CollatzResearch.WordTrace tailWord_2197711 prefixEnd_2197711 1128482082673356179305417 := by
  unfold tailWord_2197711
  simp only [CollatzResearch.WordTrace]
  refine ⟨80157105341075861001632987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53438070227383907334421991 80157105341075861001632987)
  ·
    refine ⟨120235658011613791502449481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80157105341075861001632987 120235658011613791502449481)
    ·
      refine ⟨90176743508710343626837111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120235658011613791502449481 90176743508710343626837111)
      ·
        refine ⟨135265115263065515440255667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90176743508710343626837111 135265115263065515440255667)
        ·
          refine ⟨202897672894598273160383501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135265115263065515440255667 202897672894598273160383501)
          ·
            refine ⟨76086627335474352435143813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202897672894598273160383501 76086627335474352435143813)
            ·
              refine ⟨14266242625401441081589465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76086627335474352435143813 14266242625401441081589465)
              ·
                refine ⟨10699681969051080811192099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14266242625401441081589465 10699681969051080811192099)
                ·
                  refine ⟨16049522953576621216788149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10699681969051080811192099 16049522953576621216788149)
                  ·
                    refine ⟨1504642776897808239073889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16049522953576621216788149 1504642776897808239073889)
                    ·
                      refine ⟨1128482082673356179305417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1504642776897808239073889 1128482082673356179305417)
                      ·
                        rfl

theorem cell23_2197711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 5, 2].length) (baseStart_2197711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197711 prefixEnd_2197711 := by exact prefixLift 2197711
  have htrace : WordTrace (prefixWord ++ tailWord_2197711) baseStart_2197711 baseEnd_2197711 := by
    simpa [prefixWord, tailWord_2197711, baseEnd_2197711] using wordTrace_append hprefix tailTrace_2197711
  have hstable : (prefixWord ++ tailWord_2197711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197711).length < 2 ^ (prefixWord ++ tailWord_2197711).sum := by decide
  have hdescent : baseEnd_2197711 < baseStart_2197711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197744 : List Nat := [2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_2197744 : Nat := 118140960795 + 2197744 * 2 ^ 59
def prefixEnd_2197744 : Nat := 4983230072969 + 3 ^ 40 * 2197744 * 2
def baseEnd_2197744 : Nat := 1128499027534954550192765

theorem tailTrace_2197744 : CollatzResearch.WordTrace tailWord_2197744 prefixEnd_2197744 1128499027534954550192765 := by
  unfold tailWord_2197744
  simp only [CollatzResearch.WordTrace]
  refine ⟨40079154474978153818792143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53438872633304205091722857 40079154474978153818792143)
  ·
    refine ⟨60118731712467230728188215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40079154474978153818792143 60118731712467230728188215)
    ·
      refine ⟨90178097568700846092282323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60118731712467230728188215 90178097568700846092282323)
      ·
        refine ⟨135267146353051269138423485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90178097568700846092282323 135267146353051269138423485)
        ·
          refine ⟨50725179882394225926908807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135267146353051269138423485 50725179882394225926908807)
          ·
            refine ⟨76087769823591338890363211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50725179882394225926908807 76087769823591338890363211)
            ·
              refine ⟨114131654735387008335544817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76087769823591338890363211 114131654735387008335544817)
              ·
                refine ⟨85598741051540256251658613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114131654735387008335544817 85598741051540256251658613)
                ·
                  refine ⟨8024881973581899023592995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85598741051540256251658613 8024881973581899023592995)
                  ·
                    refine ⟨12037322960372848535389493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8024881973581899023592995 12037322960372848535389493)
                    ·
                      refine ⟨1128499027534954550192765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12037322960372848535389493 1128499027534954550192765)
                      ·
                        rfl

theorem cell23_2197744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_2197744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197744 prefixEnd_2197744 := by exact prefixLift 2197744
  have htrace : WordTrace (prefixWord ++ tailWord_2197744) baseStart_2197744 baseEnd_2197744 := by
    simpa [prefixWord, tailWord_2197744, baseEnd_2197744] using wordTrace_append hprefix tailTrace_2197744
  have hstable : (prefixWord ++ tailWord_2197744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197744).length < 2 ^ (prefixWord ++ tailWord_2197744).sum := by decide
  have hdescent : baseEnd_2197744 < baseStart_2197744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197761 : List Nat := [1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 5]
def baseStart_2197761 : Nat := 118140960795 + 2197761 * 2 ^ 59
def prefixEnd_2197761 : Nat := 4983230072969 + 3 ^ 40 * 2197761 * 2
def baseEnd_2197761 : Nat := 1128507756706080983680187

theorem tailTrace_2197761 : CollatzResearch.WordTrace tailWord_2197761 prefixEnd_2197761 1128507756706080983680187 := by
  unfold tailWord_2197761
  simp only [CollatzResearch.WordTrace]
  refine ⟨80158928990894719540953137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53439285993929813027302091 80158928990894719540953137)
  ·
    refine ⟨60119196743171039655714853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80158928990894719540953137 60119196743171039655714853)
    ·
      refine ⟨11272349389344569935446535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60119196743171039655714853 11272349389344569935446535)
      ·
        refine ⟨16908524084016854903169803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11272349389344569935446535 16908524084016854903169803)
        ·
          refine ⟨25362786126025282354754705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16908524084016854903169803 25362786126025282354754705)
          ·
            refine ⟨19022089594518961766066029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25362786126025282354754705 19022089594518961766066029)
            ·
              refine ⟨7133283597944610662274761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19022089594518961766066029 7133283597944610662274761)
              ·
                refine ⟨5349962698458457996706071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7133283597944610662274761 5349962698458457996706071)
                ·
                  refine ⟨8024944047687686995059107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5349962698458457996706071 8024944047687686995059107)
                  ·
                    refine ⟨12037416071531530492588661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8024944047687686995059107 12037416071531530492588661)
                    ·
                      refine ⟨1128507756706080983680187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12037416071531530492588661 1128507756706080983680187)
                      ·
                        rfl

theorem cell23_2197761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_2197761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197761 prefixEnd_2197761 := by exact prefixLift 2197761
  have htrace : WordTrace (prefixWord ++ tailWord_2197761) baseStart_2197761 baseEnd_2197761 := by
    simpa [prefixWord, tailWord_2197761, baseEnd_2197761] using wordTrace_append hprefix tailTrace_2197761
  have hstable : (prefixWord ++ tailWord_2197761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197761).length < 2 ^ (prefixWord ++ tailWord_2197761).sum := by decide
  have hdescent : baseEnd_2197761 < baseStart_2197761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197768 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 1, 6]
def baseStart_2197768 : Nat := 118140960795 + 2197768 * 2 ^ 59
def prefixEnd_2197768 : Nat := 4983230072969 + 3 ^ 40 * 2197768 * 2
def baseEnd_2197768 : Nat := 376170450356887485430885

theorem tailTrace_2197768 : CollatzResearch.WordTrace tailWord_2197768 prefixEnd_2197768 376170450356887485430885 := by
  unfold tailWord_2197768
  simp only [CollatzResearch.WordTrace]
  refine ⟨40079592150934679868228979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53439456201246239824305305 40079592150934679868228979)
  ·
    refine ⟨60119388226402019802343469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40079592150934679868228979 60119388226402019802343469)
    ·
      refine ⟨22544770584900757425878801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60119388226402019802343469 22544770584900757425878801)
      ·
        refine ⟨16908577938675568069409101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22544770584900757425878801 16908577938675568069409101)
        ·
          refine ⟨6340716727003338026028413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16908577938675568069409101 6340716727003338026028413)
          ·
            refine ⟨2377768772626251759760655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6340716727003338026028413 2377768772626251759760655)
            ·
              refine ⟨3566653158939377639640983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377768772626251759760655 3566653158939377639640983)
              ·
                refine ⟨5349979738409066459461475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566653158939377639640983 5349979738409066459461475)
                ·
                  refine ⟨8024969607613599689192213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5349979738409066459461475 8024969607613599689192213)
                  ·
                    refine ⟨376170450356887485430885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8024969607613599689192213 376170450356887485430885)
                    ·
                      rfl

theorem cell23_2197768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_2197768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197768 prefixEnd_2197768 := by exact prefixLift 2197768
  have htrace : WordTrace (prefixWord ++ tailWord_2197768) baseStart_2197768 baseEnd_2197768 := by
    simpa [prefixWord, tailWord_2197768, baseEnd_2197768] using wordTrace_append hprefix tailTrace_2197768
  have hstable : (prefixWord ++ tailWord_2197768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197768).length < 2 ^ (prefixWord ++ tailWord_2197768).sum := by decide
  have hdescent : baseEnd_2197768 < baseStart_2197768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197781 : List Nat := [1, 3, 2, 1, 2, 1, 6, 7]
def baseStart_2197781 : Nat := 118140960795 + 2197781 * 2 ^ 59
def prefixEnd_2197781 : Nat := 4983230072969 + 3 ^ 40 * 2197781 * 2
def baseEnd_2197781 : Nat := 41796963937747070571485

theorem tailTrace_2197781 : CollatzResearch.WordTrace tailWord_2197781 prefixEnd_2197781 41796963937747070571485 := by
  unfold tailWord_2197781
  simp only [CollatzResearch.WordTrace]
  refine ⟨80159658450822262956681197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53439772300548175304454131 80159658450822262956681197)
  ·
    refine ⟨30059871919058348608755449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80159658450822262956681197 30059871919058348608755449)
    ·
      refine ⟨22544903939293761456566587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30059871919058348608755449 22544903939293761456566587)
      ·
        refine ⟨33817355908940642184849881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22544903939293761456566587 33817355908940642184849881)
        ·
          refine ⟨25363016931705481638637411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33817355908940642184849881 25363016931705481638637411)
          ·
            refine ⟨38044525397558222457956117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25363016931705481638637411 38044525397558222457956117)
            ·
              refine ⟨1783337128010541677716693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38044525397558222457956117 1783337128010541677716693)
              ·
                refine ⟨41796963937747070571485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1783337128010541677716693 41796963937747070571485)
                ·
                  rfl

theorem cell23_2197781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 7].length) (baseStart_2197781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197781 prefixEnd_2197781 := by exact prefixLift 2197781
  have htrace : WordTrace (prefixWord ++ tailWord_2197781) baseStart_2197781 baseEnd_2197781 := by
    simpa [prefixWord, tailWord_2197781, baseEnd_2197781] using wordTrace_append hprefix tailTrace_2197781
  have hstable : (prefixWord ++ tailWord_2197781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197781).length < 2 ^ (prefixWord ++ tailWord_2197781).sum := by decide
  have hdescent : baseEnd_2197781 < baseStart_2197781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197809 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 3, 2, 2]
def baseStart_2197809 : Nat := 118140960795 + 2197809 * 2 ^ 59
def prefixEnd_2197809 : Nat := 4983230072969 + 3 ^ 40 * 2197809 * 2
def baseEnd_2197809 : Nat := 1128532403777496795879967

theorem tailTrace_2197809 : CollatzResearch.WordTrace tailWord_2197809 prefixEnd_2197809 1128532403777496795879967 := by
  unfold tailWord_2197809
  simp only [CollatzResearch.WordTrace]
  refine ⟨80160679694720823738700481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53440453129813882492466987 80160679694720823738700481)
  ·
    refine ⟨60120509771040617804025361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80160679694720823738700481 60120509771040617804025361)
    ·
      refine ⟨45090382328280463353019021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60120509771040617804025361 45090382328280463353019021)
      ·
        refine ⟨16908893373105173757382133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45090382328280463353019021 16908893373105173757382133)
        ·
          refine ⟨1585208753728610039754575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16908893373105173757382133 1585208753728610039754575)
          ·
            refine ⟨2377813130592915059631863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585208753728610039754575 2377813130592915059631863)
            ·
              refine ⟨3566719695889372589447795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377813130592915059631863 3566719695889372589447795)
              ·
                refine ⟨5350079543834058884171693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566719695889372589447795 5350079543834058884171693)
                ·
                  refine ⟨2006279828937772081564385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5350079543834058884171693 2006279828937772081564385)
                  ·
                    refine ⟨1504709871703329061173289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2006279828937772081564385 1504709871703329061173289)
                    ·
                      refine ⟨1128532403777496795879967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1504709871703329061173289 1128532403777496795879967)
                      ·
                        rfl

theorem cell23_2197809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 3, 2, 2].length) (baseStart_2197809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197809 prefixEnd_2197809 := by exact prefixLift 2197809
  have htrace : WordTrace (prefixWord ++ tailWord_2197809) baseStart_2197809 baseEnd_2197809 := by
    simpa [prefixWord, tailWord_2197809, baseEnd_2197809] using wordTrace_append hprefix tailTrace_2197809
  have hstable : (prefixWord ++ tailWord_2197809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197809).length < 2 ^ (prefixWord ++ tailWord_2197809).sum := by decide
  have hdescent : baseEnd_2197809 < baseStart_2197809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197910 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2197910 : Nat := 118140960795 + 2197910 * 2 ^ 59
def prefixEnd_2197910 : Nat := 4983230072969 + 3 ^ 40 * 2197910 * 2
def baseEnd_2197910 : Nat := 1128584265323600900717003

theorem tailTrace_2197910 : CollatzResearch.WordTrace tailWord_2197910 prefixEnd_2197910 1128584265323600900717003 := by
  unfold tailWord_2197910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010272716709682374257949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53442908978236611992084789 5010272716709682374257949)
  ·
    refine ⟨1878852268766130890346731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5010272716709682374257949 1878852268766130890346731)
    ·
      refine ⟨2818278403149196335520097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1878852268766130890346731 2818278403149196335520097)
      ·
        refine ⟨2113708802361897251640073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2818278403149196335520097 2113708802361897251640073)
        ·
          refine ⟨1585281601771422938730055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2113708802361897251640073 1585281601771422938730055)
          ·
            refine ⟨2377922402657134408095083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585281601771422938730055 2377922402657134408095083)
            ·
              refine ⟨3566883603985701612142625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2377922402657134408095083 3566883603985701612142625)
              ·
                refine ⟨2675162702989276209106969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3566883603985701612142625 2675162702989276209106969)
                ·
                  refine ⟨2006372027241957156830227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675162702989276209106969 2006372027241957156830227)
                  ·
                    refine ⟨3009558040862935735245341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2006372027241957156830227 3009558040862935735245341)
                    ·
                      refine ⟨1128584265323600900717003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3009558040862935735245341 1128584265323600900717003)
                      ·
                        rfl

theorem cell23_2197910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2197910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197910 prefixEnd_2197910 := by exact prefixLift 2197910
  have htrace : WordTrace (prefixWord ++ tailWord_2197910) baseStart_2197910 baseEnd_2197910 := by
    simpa [prefixWord, tailWord_2197910, baseEnd_2197910] using wordTrace_append hprefix tailTrace_2197910
  have hstable : (prefixWord ++ tailWord_2197910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197910).length < 2 ^ (prefixWord ++ tailWord_2197910).sum := by decide
  have hdescent : baseEnd_2197910 < baseStart_2197910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197911 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2197911 : Nat := 118140960795 + 2197911 * 2 ^ 59
def prefixEnd_2197911 : Nat := 4983230072969 + 3 ^ 40 * 2197911 * 2
def baseEnd_2197911 : Nat := 1128584778804255396804497

theorem tailTrace_2197911 : CollatzResearch.WordTrace tailWord_2197911 prefixEnd_2197911 1128584778804255396804497 := by
  unfold tailWord_2197911
  simp only [CollatzResearch.WordTrace]
  refine ⟨80164399940351295158913587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53442933293567530105942391 80164399940351295158913587)
  ·
    refine ⟨120246599910526942738370381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80164399940351295158913587 120246599910526942738370381)
    ·
      refine ⟨45092474966447603526888893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120246599910526942738370381 45092474966447603526888893)
      ·
        refine ⟨16909678112417851322583335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45092474966447603526888893 16909678112417851322583335)
        ·
          refine ⟨25364517168626776983875003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16909678112417851322583335 25364517168626776983875003)
          ·
            refine ⟨38046775752940165475812505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25364517168626776983875003 38046775752940165475812505)
            ·
              refine ⟨28535081814705124106859379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38046775752940165475812505 28535081814705124106859379)
              ·
                refine ⟨42802622722057686160289069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28535081814705124106859379 42802622722057686160289069)
                ·
                  refine ⟨16050983520771632310108401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42802622722057686160289069 16050983520771632310108401)
                  ·
                    refine ⟨12038237640578724232581301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16050983520771632310108401 12038237640578724232581301)
                    ·
                      refine ⟨1128584778804255396804497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12038237640578724232581301 1128584778804255396804497)
                      ·
                        rfl

theorem cell23_2197911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2197911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197911 prefixEnd_2197911 := by exact prefixLift 2197911
  have htrace : WordTrace (prefixWord ++ tailWord_2197911) baseStart_2197911 baseEnd_2197911 := by
    simpa [prefixWord, tailWord_2197911, baseEnd_2197911] using wordTrace_append hprefix tailTrace_2197911
  have hstable : (prefixWord ++ tailWord_2197911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197911).length < 2 ^ (prefixWord ++ tailWord_2197911).sum := by decide
  have hdescent : baseEnd_2197911 < baseStart_2197911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197961 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 8]
def baseStart_2197961 : Nat := 118140960795 + 2197961 * 2 ^ 59
def prefixEnd_2197961 : Nat := 4983230072969 + 3 ^ 40 * 2197961 * 2
def baseEnd_2197961 : Nat := 125401161426331133464363

theorem tailTrace_2197961 : CollatzResearch.WordTrace tailWord_2197961 prefixEnd_2197961 125401161426331133464363 := by
  unfold tailWord_2197961
  simp only [CollatzResearch.WordTrace]
  refine ⟨80166223590170153698233737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53444149060113435798822491 80166223590170153698233737)
  ·
    refine ⟨60124667692627615273675303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80166223590170153698233737 60124667692627615273675303)
    ·
      refine ⟨90187001538941422910512955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60124667692627615273675303 90187001538941422910512955)
      ·
        refine ⟨135280502308412134365769433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90187001538941422910512955 135280502308412134365769433)
        ·
          refine ⟨101460376731309100774327075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135280502308412134365769433 101460376731309100774327075)
          ·
            refine ⟨152190565096963651161490613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101460376731309100774327075 152190565096963651161490613)
            ·
              refine ⟨14267865477840342296389745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152190565096963651161490613 14267865477840342296389745)
              ·
                refine ⟨10700899108380256722292309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14267865477840342296389745 10700899108380256722292309)
                ·
                  refine ⟨125401161426331133464363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10700899108380256722292309 125401161426331133464363)
                  ·
                    rfl

theorem cell23_2197961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 8].length) (baseStart_2197961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197961 prefixEnd_2197961 := by exact prefixLift 2197961
  have htrace : WordTrace (prefixWord ++ tailWord_2197961) baseStart_2197961 baseEnd_2197961 := by
    simpa [prefixWord, tailWord_2197961, baseEnd_2197961] using wordTrace_append hprefix tailTrace_2197961
  have hstable : (prefixWord ++ tailWord_2197961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197961).length < 2 ^ (prefixWord ++ tailWord_2197961).sum := by decide
  have hdescent : baseEnd_2197961 < baseStart_2197961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2197978 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 6]
def baseStart_2197978 : Nat := 118140960795 + 2197978 * 2 ^ 59
def prefixEnd_2197978 : Nat := 4983230072969 + 3 ^ 40 * 2197978 * 2
def baseEnd_2197978 : Nat := 125402131334234070518521

theorem tailTrace_2197978 : CollatzResearch.WordTrace tailWord_2197978 prefixEnd_2197978 125402131334234070518521 := by
  unfold tailWord_2197978
  simp only [CollatzResearch.WordTrace]
  refine ⟨20041710907777141400400647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53444562420739043734401725 20041710907777141400400647)
  ·
    refine ⟨30062566361665712100600971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20041710907777141400400647 30062566361665712100600971)
    ·
      refine ⟨45093849542498568150901457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30062566361665712100600971 45093849542498568150901457)
      ·
        refine ⟨33820387156873926113176093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45093849542498568150901457 33820387156873926113176093)
        ·
          refine ⟨12682645183827722292441035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33820387156873926113176093 12682645183827722292441035)
          ·
            refine ⟨19023967775741583438661553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12682645183827722292441035 19023967775741583438661553)
            ·
              refine ⟨14267975831806187578996165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19023967775741583438661553 14267975831806187578996165)
              ·
                refine ⟨2675245468463660171061781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14267975831806187578996165 2675245468463660171061781)
                ·
                  refine ⟨125402131334234070518521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2675245468463660171061781 125402131334234070518521)
                  ·
                    rfl

theorem cell23_2197978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_2197978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2197978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2197978 prefixEnd_2197978 := by exact prefixLift 2197978
  have htrace : WordTrace (prefixWord ++ tailWord_2197978) baseStart_2197978 baseEnd_2197978 := by
    simpa [prefixWord, tailWord_2197978, baseEnd_2197978] using wordTrace_append hprefix tailTrace_2197978
  have hstable : (prefixWord ++ tailWord_2197978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2197978).length < 2 ^ (prefixWord ++ tailWord_2197978).sum := by decide
  have hdescent : baseEnd_2197978 < baseStart_2197978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2197978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198008 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 3, 5]
def baseStart_2198008 : Nat := 118140960795 + 2198008 * 2 ^ 59
def prefixEnd_2198008 : Nat := 4983230072969 + 3 ^ 40 * 2198008 * 2
def baseEnd_2198008 : Nat := 376211528809247172430517

theorem tailTrace_2198008 : CollatzResearch.WordTrace tailWord_2198008 prefixEnd_2198008 376211528809247172430517 := by
  unfold tailWord_2198008
  simp only [CollatzResearch.WordTrace]
  refine ⟨40083968910499940362597339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53445291880666587150129785 40083968910499940362597339)
  ·
    refine ⟨60125953365749910543896009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40083968910499940362597339 60125953365749910543896009)
    ·
      refine ⟨45094465024312432907922007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60125953365749910543896009 45094465024312432907922007)
      ·
        refine ⟨67641697536468649361883011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45094465024312432907922007 67641697536468649361883011)
        ·
          refine ⟨101462546304702974042824517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67641697536468649361883011 101462546304702974042824517)
          ·
            refine ⟨19024227432131807633029597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101462546304702974042824517 19024227432131807633029597)
            ·
              refine ⟨7134085287049427862386099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19024227432131807633029597 7134085287049427862386099)
              ·
                refine ⟨10701127930574141793579149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7134085287049427862386099 10701127930574141793579149)
                ·
                  refine ⟨4012922973965303172592181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10701127930574141793579149 4012922973965303172592181)
                  ·
                    refine ⟨376211528809247172430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4012922973965303172592181 376211528809247172430517)
                    ·
                      rfl

theorem cell23_2198008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_2198008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198008 prefixEnd_2198008 := by exact prefixLift 2198008
  have htrace : WordTrace (prefixWord ++ tailWord_2198008) baseStart_2198008 baseEnd_2198008 := by
    simpa [prefixWord, tailWord_2198008, baseEnd_2198008] using wordTrace_append hprefix tailTrace_2198008
  have hstable : (prefixWord ++ tailWord_2198008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198008).length < 2 ^ (prefixWord ++ tailWord_2198008).sum := by decide
  have hdescent : baseEnd_2198008 < baseStart_2198008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198029 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2198029 : Nat := 118140960795 + 2198029 * 2 ^ 59
def prefixEnd_2198029 : Nat := 4983230072969 + 3 ^ 40 * 2198029 * 2
def baseEnd_2198029 : Nat := 125405041057942881680995

theorem tailTrace_2198029 : CollatzResearch.WordTrace tailWord_2198029 prefixEnd_2198029 125405041057942881680995 := by
  unfold tailWord_2198029
  simp only [CollatzResearch.WordTrace]
  refine ⟨80168703753923801311709141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53445802502615867541139427 80168703753923801311709141)
  ·
    refine ⟨1878953994232589093243183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 80168703753923801311709141 1878953994232589093243183)
    ·
      refine ⟨2818430991348883639864775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1878953994232589093243183 2818430991348883639864775)
      ·
        refine ⟨4227646487023325459797163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2818430991348883639864775 4227646487023325459797163)
        ·
          refine ⟨6341469730534988189695745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4227646487023325459797163 6341469730534988189695745)
          ·
            refine ⟨4756102297901241142271809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6341469730534988189695745 4756102297901241142271809)
            ·
              refine ⟨3567076723425930856703857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4756102297901241142271809 3567076723425930856703857)
              ·
                refine ⟨2675307542569448142527893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567076723425930856703857 2675307542569448142527893)
                ·
                  refine ⟨125405041057942881680995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2675307542569448142527893 125405041057942881680995)
                  ·
                    rfl

theorem cell23_2198029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2198029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198029 prefixEnd_2198029 := by exact prefixLift 2198029
  have htrace : WordTrace (prefixWord ++ tailWord_2198029) baseStart_2198029 baseEnd_2198029 := by
    simpa [prefixWord, tailWord_2198029, baseEnd_2198029] using wordTrace_append hprefix tailTrace_2198029
  have hstable : (prefixWord ++ tailWord_2198029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198029).length < 2 ^ (prefixWord ++ tailWord_2198029).sum := by decide
  have hdescent : baseEnd_2198029 < baseStart_2198029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198045 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_2198045 : Nat := 118140960795 + 2198045 * 2 ^ 59
def prefixEnd_2198045 : Nat := 4983230072969 + 3 ^ 40 * 2198045 * 2
def baseEnd_2198045 : Nat := 1128653585211957872528881

theorem tailTrace_2198045 : CollatzResearch.WordTrace tailWord_2198045 prefixEnd_2198045 1128653585211957872528881 := by
  unfold tailWord_2198045
  simp only [CollatzResearch.WordTrace]
  refine ⟨80169287321865836044291589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53446191547910557362861059 80169287321865836044291589)
  ·
    refine ⟨15031741372849844258304673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80169287321865836044291589 15031741372849844258304673)
    ·
      refine ⟨11273806029637383193728505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15031741372849844258304673 11273806029637383193728505)
      ·
        refine ⟨8455354522228037395296379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11273806029637383193728505 8455354522228037395296379)
        ·
          refine ⟨12683031783342056092944569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8455354522228037395296379 12683031783342056092944569)
          ·
            refine ⟨9512273837506542069708427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12683031783342056092944569 9512273837506542069708427)
            ·
              refine ⟨14268410756259813104562641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9512273837506542069708427 14268410756259813104562641)
              ·
                refine ⟨10701308067194859828421981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14268410756259813104562641 10701308067194859828421981)
                ·
                  refine ⟨4012990525198072435658243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10701308067194859828421981 4012990525198072435658243)
                  ·
                    refine ⟨6019485787797108653487365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4012990525198072435658243 6019485787797108653487365)
                    ·
                      refine ⟨1128653585211957872528881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6019485787797108653487365 1128653585211957872528881)
                      ·
                        rfl

theorem cell23_2198045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_2198045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198045 prefixEnd_2198045 := by exact prefixLift 2198045
  have htrace : WordTrace (prefixWord ++ tailWord_2198045) baseStart_2198045 baseEnd_2198045 := by
    simpa [prefixWord, tailWord_2198045, baseEnd_2198045] using wordTrace_append hprefix tailTrace_2198045
  have hstable : (prefixWord ++ tailWord_2198045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198045).length < 2 ^ (prefixWord ++ tailWord_2198045).sum := by decide
  have hdescent : baseEnd_2198045 < baseStart_2198045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198065 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 3]
def baseStart_2198065 : Nat := 118140960795 + 2198065 * 2 ^ 59
def prefixEnd_2198065 : Nat := 4983230072969 + 3 ^ 40 * 2198065 * 2
def baseEnd_2198065 : Nat := 1128663854825047794278789

theorem tailTrace_2198065 : CollatzResearch.WordTrace tailWord_2198065 prefixEnd_2198065 1128663854825047794278789 := by
  unfold tailWord_2198065
  simp only [CollatzResearch.WordTrace]
  refine ⟨80170016781793379460019649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53446677854528919640013099 80170016781793379460019649)
  ·
    refine ⟨60127512586345034595014737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80170016781793379460019649 60127512586345034595014737)
    ·
      refine ⟨45095634439758775946261053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60127512586345034595014737 45095634439758775946261053)
      ·
        refine ⟨16910862914909540979847895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45095634439758775946261053 16910862914909540979847895)
        ·
          refine ⟨25366294372364311469771843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16910862914909540979847895 25366294372364311469771843)
          ·
            refine ⟨38049441558546467204657765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25366294372364311469771843 38049441558546467204657765)
            ·
              refine ⟨7134270292227462600873331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38049441558546467204657765 7134270292227462600873331)
              ·
                refine ⟨10701405438341193901309997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7134270292227462600873331 10701405438341193901309997)
                ·
                  refine ⟨4013027039377947712991249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10701405438341193901309997 4013027039377947712991249)
                  ·
                    refine ⟨3009770279533460784743437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4013027039377947712991249 3009770279533460784743437)
                    ·
                      refine ⟨1128663854825047794278789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3009770279533460784743437 1128663854825047794278789)
                      ·
                        rfl

theorem cell23_2198065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_2198065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198065 prefixEnd_2198065 := by exact prefixLift 2198065
  have htrace : WordTrace (prefixWord ++ tailWord_2198065) baseStart_2198065 baseEnd_2198065 := by
    simpa [prefixWord, tailWord_2198065, baseEnd_2198065] using wordTrace_append hprefix tailTrace_2198065
  have hstable : (prefixWord ++ tailWord_2198065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198065).length < 2 ^ (prefixWord ++ tailWord_2198065).sum := by decide
  have hdescent : baseEnd_2198065 < baseStart_2198065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198112 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 2, 1, 3]
def baseStart_2198112 : Nat := 118140960795 + 2198112 * 2 ^ 59
def prefixEnd_2198112 : Nat := 4983230072969 + 3 ^ 40 * 2198112 * 2
def baseEnd_2198112 : Nat := 1128687988415809110391073

theorem tailTrace_2198112 : CollatzResearch.WordTrace tailWord_2198112 prefixEnd_2198112 1128687988415809110391073 := by
  unfold tailWord_2198112
  simp only [CollatzResearch.WordTrace]
  refine ⟨40085865506311553243490295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53447820675082070991320393 40085865506311553243490295)
  ·
    refine ⟨60128798259467329865235443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40085865506311553243490295 60128798259467329865235443)
    ·
      refine ⟨90193197389200994797853165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60128798259467329865235443 90193197389200994797853165)
      ·
        refine ⟨33822449020950373049194937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90193197389200994797853165 33822449020950373049194937)
        ·
          refine ⟨25366836765712779786896203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33822449020950373049194937 25366836765712779786896203)
          ·
            refine ⟨38050255148569169680344305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25366836765712779786896203 38050255148569169680344305)
            ·
              refine ⟨28537691361426877260258229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38050255148569169680344305 28537691361426877260258229)
              ·
                refine ⟨2675408565133769743149209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28537691361426877260258229 2675408565133769743149209)
                ·
                  refine ⟨2006556423850327307361907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675408565133769743149209 2006556423850327307361907)
                  ·
                    refine ⟨3009834635775490961042861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2006556423850327307361907 3009834635775490961042861)
                    ·
                      refine ⟨1128687988415809110391073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3009834635775490961042861 1128687988415809110391073)
                      ·
                        rfl

theorem cell23_2198112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 1, 3].length) (baseStart_2198112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198112 prefixEnd_2198112 := by exact prefixLift 2198112
  have htrace : WordTrace (prefixWord ++ tailWord_2198112) baseStart_2198112 baseEnd_2198112 := by
    simpa [prefixWord, tailWord_2198112, baseEnd_2198112] using wordTrace_append hprefix tailTrace_2198112
  have hstable : (prefixWord ++ tailWord_2198112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198112).length < 2 ^ (prefixWord ++ tailWord_2198112).sum := by decide
  have hdescent : baseEnd_2198112 < baseStart_2198112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198125 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2198125 : Nat := 118140960795 + 2198125 * 2 ^ 59
def prefixEnd_2198125 : Nat := 4983230072969 + 3 ^ 40 * 2198125 * 2
def baseEnd_2198125 : Nat := 1128694663664317559528513

theorem tailTrace_2198125 : CollatzResearch.WordTrace tailWord_2198125 prefixEnd_2198125 1128694663664317559528513 := by
  unfold tailWord_2198125
  simp only [CollatzResearch.WordTrace]
  refine ⟨80172205161576009707203829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53448136774384006471469219 80172205161576009707203829)
  ·
    refine ⟨7516144233897750910050359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80172205161576009707203829 7516144233897750910050359)
    ·
      refine ⟨11274216350846626365075539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7516144233897750910050359 11274216350846626365075539)
      ·
        refine ⟨16911324526269939547613309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11274216350846626365075539 16911324526269939547613309)
        ·
          refine ⟨6341746697351227330354991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16911324526269939547613309 6341746697351227330354991)
          ·
            refine ⟨9512620046026840995532487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6341746697351227330354991 9512620046026840995532487)
            ·
              refine ⟨14268930069040261493298731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9512620046026840995532487 14268930069040261493298731)
              ·
                refine ⟨21403395103560392239948097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14268930069040261493298731 21403395103560392239948097)
                ·
                  refine ⟨16052546327670294179961073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21403395103560392239948097 16052546327670294179961073)
                  ·
                    refine ⟨12039409745752720634970805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16052546327670294179961073 12039409745752720634970805)
                    ·
                      refine ⟨1128694663664317559528513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12039409745752720634970805 1128694663664317559528513)
                      ·
                        rfl

theorem cell23_2198125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2198125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198125 prefixEnd_2198125 := by exact prefixLift 2198125
  have htrace : WordTrace (prefixWord ++ tailWord_2198125) baseStart_2198125 baseEnd_2198125 := by
    simpa [prefixWord, tailWord_2198125, baseEnd_2198125] using wordTrace_append hprefix tailTrace_2198125
  have hstable : (prefixWord ++ tailWord_2198125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198125).length < 2 ^ (prefixWord ++ tailWord_2198125).sum := by decide
  have hdescent : baseEnd_2198125 < baseStart_2198125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198130 : List Nat := [3, 2, 1, 2, 5, 1, 1, 3, 1, 2, 2]
def baseStart_2198130 : Nat := 118140960795 + 2198130 * 2 ^ 59
def prefixEnd_2198130 : Nat := 4983230072969 + 3 ^ 40 * 2198130 * 2
def baseEnd_2198130 : Nat := 1128697231067590039965991

theorem tailTrace_2198130 : CollatzResearch.WordTrace tailWord_2198130 prefixEnd_2198130 1128697231067590039965991 := by
  unfold tailWord_2198130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20043096881639473890283961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53448258351038597040757229 20043096881639473890283961)
  ·
    refine ⟨15032322661229605417712971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20043096881639473890283961 15032322661229605417712971)
    ·
      refine ⟨22548483991844408126569457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15032322661229605417712971 22548483991844408126569457)
      ·
        refine ⟨16911362993883306094927093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22548483991844408126569457 16911362993883306094927093)
        ·
          refine ⟨1585440280676559946399415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16911362993883306094927093 1585440280676559946399415)
          ·
            refine ⟨2378160421014839919599123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585440280676559946399415 2378160421014839919599123)
            ·
              refine ⟨3567240631522259879398685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378160421014839919599123 3567240631522259879398685)
              ·
                refine ⟨1337715236820847454774507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3567240631522259879398685 1337715236820847454774507)
                ·
                  refine ⟨2006572855231271182161761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337715236820847454774507 2006572855231271182161761)
                  ·
                    refine ⟨1504929641423453386621321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2006572855231271182161761 1504929641423453386621321)
                    ·
                      refine ⟨1128697231067590039965991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1504929641423453386621321 1128697231067590039965991)
                      ·
                        rfl

theorem cell23_2198130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_2198130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198130 prefixEnd_2198130 := by exact prefixLift 2198130
  have htrace : WordTrace (prefixWord ++ tailWord_2198130) baseStart_2198130 baseEnd_2198130 := by
    simpa [prefixWord, tailWord_2198130, baseEnd_2198130] using wordTrace_append hprefix tailTrace_2198130
  have hstable : (prefixWord ++ tailWord_2198130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198130).length < 2 ^ (prefixWord ++ tailWord_2198130).sum := by decide
  have hdescent : baseEnd_2198130 < baseStart_2198130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198169 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 2, 2, 2]
def baseStart_2198169 : Nat := 118140960795 + 2198169 * 2 ^ 59
def prefixEnd_2198169 : Nat := 4983230072969 + 3 ^ 40 * 2198169 * 2
def baseEnd_2198169 : Nat := 1128717256813115387378311

theorem tailTrace_2198169 : CollatzResearch.WordTrace tailWord_2198169 prefixEnd_2198169 1128717256813115387378311 := by
  unfold tailWord_2198169
  simp only [CollatzResearch.WordTrace]
  refine ⟨80173809973416605221805561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53449206648944403481203707 80173809973416605221805561)
  ·
    refine ⟨60130357480062453916354171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80173809973416605221805561 60130357480062453916354171)
    ·
      refine ⟨90195536220093680874531257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60130357480062453916354171 90195536220093680874531257)
      ·
        refine ⟨67646652165070260655898443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90195536220093680874531257 67646652165070260655898443)
        ·
          refine ⟨101469978247605390983847665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67646652165070260655898443 101469978247605390983847665)
          ·
            refine ⟨76102483685704043237885749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101469978247605390983847665 76102483685704043237885749)
            ·
              refine ⟨7134607845534754053551789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76102483685704043237885749 7134607845534754053551789)
              ·
                refine ⟨2675477942075532770081921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7134607845534754053551789 2675477942075532770081921)
                ·
                  refine ⟨2006608456556649577561441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675477942075532770081921 2006608456556649577561441)
                  ·
                    refine ⟨1504956342417487183171081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2006608456556649577561441 1504956342417487183171081)
                    ·
                      refine ⟨1128717256813115387378311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1504956342417487183171081 1128717256813115387378311)
                      ·
                        rfl

theorem cell23_2198169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 2, 2, 2].length) (baseStart_2198169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198169 prefixEnd_2198169 := by exact prefixLift 2198169
  have htrace : WordTrace (prefixWord ++ tailWord_2198169) baseStart_2198169 baseEnd_2198169 := by
    simpa [prefixWord, tailWord_2198169, baseEnd_2198169] using wordTrace_append hprefix tailTrace_2198169
  have hstable : (prefixWord ++ tailWord_2198169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198169).length < 2 ^ (prefixWord ++ tailWord_2198169).sum := by decide
  have hdescent : baseEnd_2198169 < baseStart_2198169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198225 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 4]
def baseStart_2198225 : Nat := 118140960795 + 2198225 * 2 ^ 59
def prefixEnd_2198225 : Nat := 4983230072969 + 3 ^ 40 * 2198225 * 2
def baseEnd_2198225 : Nat := 1128746011729767168278053

theorem tailTrace_2198225 : CollatzResearch.WordTrace tailWord_2198225 prefixEnd_2198225 1128746011729767168278053 := by
  unfold tailWord_2198225
  simp only [CollatzResearch.WordTrace]
  refine ⟨80175852461213726785844129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53450568307475817857229419 80175852461213726785844129)
  ·
    refine ⟨60131889345910295089383097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80175852461213726785844129 60131889345910295089383097)
    ·
      refine ⟨45098917009432721317037323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60131889345910295089383097 45098917009432721317037323)
      ·
        refine ⟨67648375514149081975555985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45098917009432721317037323 67648375514149081975555985)
        ·
          refine ⟨50736281635611811481666989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67648375514149081975555985 50736281635611811481666989)
          ·
            refine ⟨19026105613354429305625121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50736281635611811481666989 19026105613354429305625121)
            ·
              refine ⟨14269579210015821979218841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19026105613354429305625121 14269579210015821979218841)
              ·
                refine ⟨10702184407511866484414131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14269579210015821979218841 10702184407511866484414131)
                ·
                  refine ⟨16053276611267799726621197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10702184407511866484414131 16053276611267799726621197)
                  ·
                    refine ⟨6019978729225424897482949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16053276611267799726621197 6019978729225424897482949)
                    ·
                      refine ⟨1128746011729767168278053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6019978729225424897482949 1128746011729767168278053)
                      ·
                        rfl

theorem cell23_2198225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 3, 4].length) (baseStart_2198225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198225 prefixEnd_2198225 := by exact prefixLift 2198225
  have htrace : WordTrace (prefixWord ++ tailWord_2198225) baseStart_2198225 baseEnd_2198225 := by
    simpa [prefixWord, tailWord_2198225, baseEnd_2198225] using wordTrace_append hprefix tailTrace_2198225
  have hstable : (prefixWord ++ tailWord_2198225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198225).length < 2 ^ (prefixWord ++ tailWord_2198225).sum := by decide
  have hdescent : baseEnd_2198225 < baseStart_2198225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198255 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 6]
def baseStart_2198255 : Nat := 118140960795 + 2198255 * 2 ^ 59
def prefixEnd_2198255 : Nat := 4983230072969 + 3 ^ 40 * 2198255 * 2
def baseEnd_2198255 : Nat := 1128761416149402050902915

theorem tailTrace_2198255 : CollatzResearch.WordTrace tailWord_2198255 prefixEnd_2198255 1128761416149402050902915 := by
  unfold tailWord_2198255
  simp only [CollatzResearch.WordTrace]
  refine ⟨80176946651105041909436219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53451297767403361272957479 80176946651105041909436219)
  ·
    refine ⟨120265419976657562864154329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80176946651105041909436219 120265419976657562864154329)
    ·
      refine ⟨90199064982493172148115747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120265419976657562864154329 90199064982493172148115747)
      ·
        refine ⟨135298597473739758222173621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90199064982493172148115747 135298597473739758222173621)
        ·
          refine ⟨12684243513163102333328777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135298597473739758222173621 12684243513163102333328777)
          ·
            refine ⟨9513182634872326749996583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12684243513163102333328777 9513182634872326749996583)
            ·
              refine ⟨14269773952308490124994875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9513182634872326749996583 14269773952308490124994875)
              ·
                refine ⟨21404660928462735187492313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14269773952308490124994875 21404660928462735187492313)
                ·
                  refine ⟨16053495696347051390619235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21404660928462735187492313 16053495696347051390619235)
                  ·
                    refine ⟨24080243544520577085928853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16053495696347051390619235 24080243544520577085928853)
                    ·
                      refine ⟨1128761416149402050902915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24080243544520577085928853 1128761416149402050902915)
                      ·
                        rfl

theorem cell23_2198255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_2198255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198255 prefixEnd_2198255 := by exact prefixLift 2198255
  have htrace : WordTrace (prefixWord ++ tailWord_2198255) baseStart_2198255 baseEnd_2198255 := by
    simpa [prefixWord, tailWord_2198255, baseEnd_2198255] using wordTrace_append hprefix tailTrace_2198255
  have hstable : (prefixWord ++ tailWord_2198255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198255).length < 2 ^ (prefixWord ++ tailWord_2198255).sum := by decide
  have hdescent : baseEnd_2198255 < baseStart_2198255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198269 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 1, 4]
def baseStart_2198269 : Nat := 118140960795 + 2198269 * 2 ^ 59
def prefixEnd_2198269 : Nat := 4983230072969 + 3 ^ 40 * 2198269 * 2
def baseEnd_2198269 : Nat := 376256201626188332042617

theorem tailTrace_2198269 : CollatzResearch.WordTrace tailWord_2198269 prefixEnd_2198269 376256201626188332042617 := by
  unfold tailWord_2198269
  simp only [CollatzResearch.WordTrace]
  refine ⟨80177457273054322300445861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53451638182036214866963907 80177457273054322300445861)
  ·
    refine ⟨15033273238697685431333599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80177457273054322300445861 15033273238697685431333599)
    ·
      refine ⟨22549909858046528147000399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15033273238697685431333599 22549909858046528147000399)
      ·
        refine ⟨33824864787069792220500599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22549909858046528147000399 33824864787069792220500599)
        ·
          refine ⟨50737297180604688330750899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33824864787069792220500599 50737297180604688330750899)
          ·
            refine ⟨76105945770907032496126349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50737297180604688330750899 76105945770907032496126349)
            ·
              refine ⟨28539729664090137186047381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76105945770907032496126349 28539729664090137186047381)
              ·
                refine ⟨1337799828004225180595971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28539729664090137186047381 1337799828004225180595971)
                ·
                  refine ⟨2006699742006337770893957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337799828004225180595971 2006699742006337770893957)
                  ·
                    refine ⟨376256201626188332042617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2006699742006337770893957 376256201626188332042617)
                    ·
                      rfl

theorem cell23_2198269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 4].length) (baseStart_2198269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198269 prefixEnd_2198269 := by exact prefixLift 2198269
  have htrace : WordTrace (prefixWord ++ tailWord_2198269) baseStart_2198269 baseEnd_2198269 := by
    simpa [prefixWord, tailWord_2198269, baseEnd_2198269] using wordTrace_append hprefix tailTrace_2198269
  have hstable : (prefixWord ++ tailWord_2198269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198269).length < 2 ^ (prefixWord ++ tailWord_2198269).sum := by decide
  have hdescent : baseEnd_2198269 < baseStart_2198269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198332 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 3, 1, 4]
def baseStart_2198332 : Nat := 118140960795 + 2198332 * 2 ^ 59
def prefixEnd_2198332 : Nat := 4983230072969 + 3 ^ 40 * 2198332 * 2
def baseEnd_2198332 : Nat := 1128800954159798249640061

theorem tailTrace_2198332 : CollatzResearch.WordTrace tailWord_2198332 prefixEnd_2198332 1128800954159798249640061 := by
  unfold tailWord_2198332
  simp only [CollatzResearch.WordTrace]
  refine ⟨40089877535913042029994625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53453170047884056039992833 40089877535913042029994625)
  ·
    refine ⟨30067408151934781522495969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40089877535913042029994625 30067408151934781522495969)
    ·
      refine ⟨22550556113951086141871977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30067408151934781522495969 22550556113951086141871977)
      ·
        refine ⟨16912917085463314606403983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22550556113951086141871977 16912917085463314606403983)
        ·
          refine ⟨25369375628194971909605975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16912917085463314606403983 25369375628194971909605975)
          ·
            refine ⟨38054063442292457864408963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25369375628194971909605975 38054063442292457864408963)
            ·
              refine ⟨57081095163438686796613445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38054063442292457864408963 57081095163438686796613445)
              ·
                refine ⟨10702705343144753774365021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57081095163438686796613445 10702705343144753774365021)
                ·
                  refine ⟨4013514503679282665386883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10702705343144753774365021 4013514503679282665386883)
                  ·
                    refine ⟨6020271755518923998080325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4013514503679282665386883 6020271755518923998080325)
                    ·
                      refine ⟨1128800954159798249640061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6020271755518923998080325 1128800954159798249640061)
                      ·
                        rfl

theorem cell23_2198332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_2198332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198332 prefixEnd_2198332 := by exact prefixLift 2198332
  have htrace : WordTrace (prefixWord ++ tailWord_2198332) baseStart_2198332 baseEnd_2198332 := by
    simpa [prefixWord, tailWord_2198332, baseEnd_2198332] using wordTrace_append hprefix tailTrace_2198332
  have hstable : (prefixWord ++ tailWord_2198332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198332).length < 2 ^ (prefixWord ++ tailWord_2198332).sum := by decide
  have hdescent : baseEnd_2198332 < baseStart_2198332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198333 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 6]
def baseStart_2198333 : Nat := 118140960795 + 2198333 * 2 ^ 59
def prefixEnd_2198333 : Nat := 4983230072969 + 3 ^ 40 * 2198333 * 2
def baseEnd_2198333 : Nat := 125422385293383638414173

theorem tailTrace_2198333 : CollatzResearch.WordTrace tailWord_2198333 prefixEnd_2198333 125422385293383638414173 := by
  unfold tailWord_2198333
  simp only [CollatzResearch.WordTrace]
  refine ⟨80179791544822461230775653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53453194363214974153850435 80179791544822461230775653)
  ·
    refine ⟨15033710914654211480770435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80179791544822461230775653 15033710914654211480770435)
    ·
      refine ⟨22550566371981317221155653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15033710914654211480770435 22550566371981317221155653)
      ·
        refine ⟨4228231194746496978966685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22550566371981317221155653 4228231194746496978966685)
        ·
          refine ⟨1585586698029936367112507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4228231194746496978966685 1585586698029936367112507)
          ·
            refine ⟨2378380047044904550668761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585586698029936367112507 2378380047044904550668761)
            ·
              refine ⟨1783785035283678413001571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2378380047044904550668761 1783785035283678413001571)
              ·
                refine ⟨2675677552925517619502357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1783785035283678413001571 2675677552925517619502357)
                ·
                  refine ⟨125422385293383638414173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2675677552925517619502357 125422385293383638414173)
                  ·
                    rfl

theorem cell23_2198333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_2198333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198333 prefixEnd_2198333 := by exact prefixLift 2198333
  have htrace : WordTrace (prefixWord ++ tailWord_2198333) baseStart_2198333 baseEnd_2198333 := by
    simpa [prefixWord, tailWord_2198333, baseEnd_2198333] using wordTrace_append hprefix tailTrace_2198333
  have hstable : (prefixWord ++ tailWord_2198333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198333).length < 2 ^ (prefixWord ++ tailWord_2198333).sum := by decide
  have hdescent : baseEnd_2198333 < baseStart_2198333 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198362 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4]
def baseStart_2198362 : Nat := 118140960795 + 2198362 * 2 ^ 59
def prefixEnd_2198362 : Nat := 4983230072969 + 3 ^ 40 * 2198362 * 2
def baseEnd_2198362 : Nat := 1128816358579433132264923

theorem tailTrace_2198362 : CollatzResearch.WordTrace tailWord_2198362 prefixEnd_2198362 1128816358579433132264923 := by
  unfold tailWord_2198362
  simp only [CollatzResearch.WordTrace]
  refine ⟨20045212315429349795895335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53453899507811599455720893 20045212315429349795895335)
  ·
    refine ⟨30067818473144024693843003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20045212315429349795895335 30067818473144024693843003)
    ·
      refine ⟨45101727709716037040764505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30067818473144024693843003 45101727709716037040764505)
      ·
        refine ⟨33826295782287027780573379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45101727709716037040764505 33826295782287027780573379)
        ·
          refine ⟨50739443673430541670860069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33826295782287027780573379 50739443673430541670860069)
          ·
            refine ⟨9513645688768226563286263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50739443673430541670860069 9513645688768226563286263)
            ·
              refine ⟨14270468533152339844929395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9513645688768226563286263 14270468533152339844929395)
              ·
                refine ⟨21405702799728509767394093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14270468533152339844929395 21405702799728509767394093)
                ·
                  refine ⟨8027138549898191162772785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21405702799728509767394093 8027138549898191162772785)
                  ·
                    refine ⟨6020353912423643372079589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8027138549898191162772785 6020353912423643372079589)
                    ·
                      refine ⟨1128816358579433132264923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6020353912423643372079589 1128816358579433132264923)
                      ·
                        rfl

theorem cell23_2198362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4].length) (baseStart_2198362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198362 prefixEnd_2198362 := by exact prefixLift 2198362
  have htrace : WordTrace (prefixWord ++ tailWord_2198362) baseStart_2198362 baseEnd_2198362 := by
    simpa [prefixWord, tailWord_2198362, baseEnd_2198362] using wordTrace_append hprefix tailTrace_2198362
  have hstable : (prefixWord ++ tailWord_2198362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198362).length < 2 ^ (prefixWord ++ tailWord_2198362).sum := by decide
  have hdescent : baseEnd_2198362 < baseStart_2198362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198376 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 2, 4]
def baseStart_2198376 : Nat := 118140960795 + 2198376 * 2 ^ 59
def prefixEnd_2198376 : Nat := 4983230072969 + 3 ^ 40 * 2198376 * 2
def baseEnd_2198376 : Nat := 376274515769532025829953

theorem tailTrace_2198376 : CollatzResearch.WordTrace tailWord_2198376 prefixEnd_2198376 376274515769532025829953 := by
  unfold tailWord_2198376
  simp only [CollatzResearch.WordTrace]
  refine ⟨40090679941833339787295491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53454239922444453049727321 40090679941833339787295491)
  ·
    refine ⟨60136019912750009680943237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40090679941833339787295491 60136019912750009680943237)
    ·
      refine ⟨11275503733640626815176857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60136019912750009680943237 11275503733640626815176857)
      ·
        refine ⟨8456627800230470111382643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11275503733640626815176857 8456627800230470111382643)
        ·
          refine ⟨12684941700345705167073965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8456627800230470111382643 12684941700345705167073965)
          ·
            refine ⟨4756853137629639437652737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12684941700345705167073965 4756853137629639437652737)
            ·
              refine ⟨3567639853222229578239553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4756853137629639437652737 3567639853222229578239553)
              ·
                refine ⟨2675729889916672183679665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567639853222229578239553 2675729889916672183679665)
                ·
                  refine ⟨2006797417437504137759749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675729889916672183679665 2006797417437504137759749)
                  ·
                    refine ⟨376274515769532025829953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2006797417437504137759749 376274515769532025829953)
                    ·
                      rfl

theorem cell23_2198376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_2198376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198376 prefixEnd_2198376 := by exact prefixLift 2198376
  have htrace : WordTrace (prefixWord ++ tailWord_2198376) baseStart_2198376 baseEnd_2198376 := by
    simpa [prefixWord, tailWord_2198376, baseEnd_2198376] using wordTrace_append hprefix tailTrace_2198376
  have hstable : (prefixWord ++ tailWord_2198376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198376).length < 2 ^ (prefixWord ++ tailWord_2198376).sum := by decide
  have hdescent : baseEnd_2198376 < baseStart_2198376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198389 : List Nat := [1, 3, 4, 1, 1, 4, 1, 8]
def baseStart_2198389 : Nat := 118140960795 + 2198389 * 2 ^ 59
def prefixEnd_2198389 : Nat := 4983230072969 + 3 ^ 40 * 2198389 * 2
def baseEnd_2198389 : Nat := 41808526761374241726937

theorem tailTrace_2198389 : CollatzResearch.WordTrace tailWord_2198389 prefixEnd_2198389 41808526761374241726937 := by
  unfold tailWord_2198389
  simp only [CollatzResearch.WordTrace]
  refine ⟨80181834032619582794814221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53454556021746388529876147 80181834032619582794814221)
  ·
    refine ⟨30068187762232343548055333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80181834032619582794814221 30068187762232343548055333)
    ·
      refine ⟨5637785205418564415260375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30068187762232343548055333 5637785205418564415260375)
      ·
        refine ⟨8456677808127846622890563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5637785205418564415260375 8456677808127846622890563)
        ·
          refine ⟨12685016712191769934335845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8456677808127846622890563 12685016712191769934335845)
          ·
            refine ⟨2378440633535956862687971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12685016712191769934335845 2378440633535956862687971)
            ·
              refine ⟨3567660950303935294031957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378440633535956862687971 3567660950303935294031957)
              ·
                refine ⟨41808526761374241726937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3567660950303935294031957 41808526761374241726937)
                ·
                  rfl

theorem cell23_2198389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 1, 8].length) (baseStart_2198389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198389 prefixEnd_2198389 := by exact prefixLift 2198389
  have htrace : WordTrace (prefixWord ++ tailWord_2198389) baseStart_2198389 baseEnd_2198389 := by
    simpa [prefixWord, tailWord_2198389, baseEnd_2198389] using wordTrace_append hprefix tailTrace_2198389
  have hstable : (prefixWord ++ tailWord_2198389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198389).length < 2 ^ (prefixWord ++ tailWord_2198389).sum := by decide
  have hdescent : baseEnd_2198389 < baseStart_2198389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198432 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_2198432 : Nat := 118140960795 + 2198432 * 2 ^ 59
def prefixEnd_2198432 : Nat := 4983230072969 + 3 ^ 40 * 2198432 * 2
def baseEnd_2198432 : Nat := 376284100741749286129867

theorem tailTrace_2198432 : CollatzResearch.WordTrace tailWord_2198432 prefixEnd_2198432 376284100741749286129867 := by
  unfold tailWord_2198432
  simp only [CollatzResearch.WordTrace]
  refine ⟨40091701185731900569314775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53455601580975867425753033 40091701185731900569314775)
  ·
    refine ⟨60137551778597850853972163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40091701185731900569314775 60137551778597850853972163)
    ·
      refine ⟨90206327667896776280958245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60137551778597850853972163 90206327667896776280958245)
      ·
        refine ⟨16913686437730645552679671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90206327667896776280958245 16913686437730645552679671)
        ·
          refine ⟨25370529656595968329019507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16913686437730645552679671 25370529656595968329019507)
          ·
            refine ⟨38055794484893952493529261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25370529656595968329019507 38055794484893952493529261)
            ·
              refine ⟨14270922931835232185073473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38055794484893952493529261 14270922931835232185073473)
              ·
                refine ⟨10703192198876424138805105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14270922931835232185073473 10703192198876424138805105)
                ·
                  refine ⟨8027394149157318104103829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10703192198876424138805105 8027394149157318104103829)
                  ·
                    refine ⟨376284100741749286129867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8027394149157318104103829 376284100741749286129867)
                    ·
                      rfl

theorem cell23_2198432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_2198432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198432 prefixEnd_2198432 := by exact prefixLift 2198432
  have htrace : WordTrace (prefixWord ++ tailWord_2198432) baseStart_2198432 baseEnd_2198432 := by
    simpa [prefixWord, tailWord_2198432, baseEnd_2198432] using wordTrace_append hprefix tailTrace_2198432
  have hstable : (prefixWord ++ tailWord_2198432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198432).length < 2 ^ (prefixWord ++ tailWord_2198432).sum := by decide
  have hdescent : baseEnd_2198432 < baseStart_2198432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198433 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2198433 : Nat := 118140960795 + 2198433 * 2 ^ 59
def prefixEnd_2198433 : Nat := 4983230072969 + 3 ^ 40 * 2198433 * 2
def baseEnd_2198433 : Nat := 1128852815705902354477097

theorem tailTrace_2198433 : CollatzResearch.WordTrace tailWord_2198433 prefixEnd_2198433 1128852815705902354477097 := by
  unfold tailWord_2198433
  simp only [CollatzResearch.WordTrace]
  refine ⟨80183438844460178309415953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53455625896306785539610635 80183438844460178309415953)
  ·
    refine ⟨60137579133345133732061965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80183438844460178309415953 60137579133345133732061965)
    ·
      refine ⟨22551592175004425149523237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60137579133345133732061965 22551592175004425149523237)
      ·
        refine ⟨4228423532813329715535607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22551592175004425149523237 4228423532813329715535607)
        ·
          refine ⟨6342635299219994573303411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228423532813329715535607 6342635299219994573303411)
          ·
            refine ⟨9513952948829991859955117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6342635299219994573303411 9513952948829991859955117)
            ·
              refine ⟨3567732355811246947483169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9513952948829991859955117 3567732355811246947483169)
              ·
                refine ⟨2675799266858435210612377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3567732355811246947483169 2675799266858435210612377)
                ·
                  refine ⟨2006849450143826407959283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2675799266858435210612377 2006849450143826407959283)
                  ·
                    refine ⟨3010274175215739611938925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2006849450143826407959283 3010274175215739611938925)
                    ·
                      refine ⟨1128852815705902354477097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3010274175215739611938925 1128852815705902354477097)
                      ·
                        rfl

theorem cell23_2198433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2198433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198433 prefixEnd_2198433 := by exact prefixLift 2198433
  have htrace : WordTrace (prefixWord ++ tailWord_2198433) baseStart_2198433 baseEnd_2198433 := by
    simpa [prefixWord, tailWord_2198433, baseEnd_2198433] using wordTrace_append hprefix tailTrace_2198433
  have hstable : (prefixWord ++ tailWord_2198433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198433).length < 2 ^ (prefixWord ++ tailWord_2198433).sum := by decide
  have hdescent : baseEnd_2198433 < baseStart_2198433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198456 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 1, 4, 2]
def baseStart_2198456 : Nat := 118140960795 + 2198456 * 2 ^ 59
def prefixEnd_2198456 : Nat := 4983230072969 + 3 ^ 40 * 2198456 * 2
def baseEnd_2198456 : Nat := 1128864625760955764489491

theorem tailTrace_2198456 : CollatzResearch.WordTrace tailWord_2198456 prefixEnd_2198456 1128864625760955764489491 := by
  unfold tailWord_2198456
  simp only [CollatzResearch.WordTrace]
  refine ⟨40092138861688426618751611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53456185148917902158335481 40092138861688426618751611)
  ·
    refine ⟨60138208292532639928127417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40092138861688426618751611 60138208292532639928127417)
    ·
      refine ⟨45103656219399479946095563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60138208292532639928127417 45103656219399479946095563)
      ·
        refine ⟨67655484329099219919143345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45103656219399479946095563 67655484329099219919143345)
        ·
          refine ⟨50741613246824414939357509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67655484329099219919143345 50741613246824414939357509)
          ·
            refine ⟨9514052483779577801129533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50741613246824414939357509 9514052483779577801129533)
            ·
              refine ⟨3567769681417341675423575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9514052483779577801129533 3567769681417341675423575)
              ·
                refine ⟨5351654522126012513135363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567769681417341675423575 5351654522126012513135363)
                ·
                  refine ⟨8027481783189018769703045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5351654522126012513135363 8027481783189018769703045)
                  ·
                    refine ⟨1505152834347941019319321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8027481783189018769703045 1505152834347941019319321)
                    ·
                      refine ⟨1128864625760955764489491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505152834347941019319321 1128864625760955764489491)
                      ·
                        rfl

theorem cell23_2198456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 4, 2].length) (baseStart_2198456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198456 prefixEnd_2198456 := by exact prefixLift 2198456
  have htrace : WordTrace (prefixWord ++ tailWord_2198456) baseStart_2198456 baseEnd_2198456 := by
    simpa [prefixWord, tailWord_2198456, baseEnd_2198456] using wordTrace_append hprefix tailTrace_2198456
  have hstable : (prefixWord ++ tailWord_2198456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198456).length < 2 ^ (prefixWord ++ tailWord_2198456).sum := by decide
  have hdescent : baseEnd_2198456 < baseStart_2198456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198522 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_2198522 : Nat := 118140960795 + 2198522 * 2 ^ 59
def prefixEnd_2198522 : Nat := 4983230072969 + 3 ^ 40 * 2198522 * 2
def baseEnd_2198522 : Nat := 376299505161384168754729

theorem tailTrace_2198522 : CollatzResearch.WordTrace tailWord_2198522 prefixEnd_2198522 376299505161384168754729 := by
  unfold tailWord_2198522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20046671235284436627351455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53457789960758497672937213 20046671235284436627351455)
  ·
    refine ⟨30070006852926654941027183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20046671235284436627351455 30070006852926654941027183)
    ·
      refine ⟨45105010279389982411540775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30070006852926654941027183 45105010279389982411540775)
      ·
        refine ⟨67657515419084973617311163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45105010279389982411540775 67657515419084973617311163)
        ·
          refine ⟨101486273128627460425966745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67657515419084973617311163 101486273128627460425966745)
          ·
            refine ⟨76114704846470595319475059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101486273128627460425966745 76114704846470595319475059)
            ·
              refine ⟨114172057269705892979212589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76114704846470595319475059 114172057269705892979212589)
              ·
                refine ⟨42814521476139709867204721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114172057269705892979212589 42814521476139709867204721)
                ·
                  refine ⟨32110891107104782400403541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42814521476139709867204721 32110891107104782400403541)
                  ·
                    refine ⟨376299505161384168754729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 32110891107104782400403541 376299505161384168754729)
                    ·
                      rfl

theorem cell23_2198522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_2198522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198522 prefixEnd_2198522 := by exact prefixLift 2198522
  have htrace : WordTrace (prefixWord ++ tailWord_2198522) baseStart_2198522 baseEnd_2198522 := by
    simpa [prefixWord, tailWord_2198522, baseEnd_2198522] using wordTrace_append hprefix tailTrace_2198522
  have hstable : (prefixWord ++ tailWord_2198522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198522).length < 2 ^ (prefixWord ++ tailWord_2198522).sum := by decide
  have hdescent : baseEnd_2198522 < baseStart_2198522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198580 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2198580 : Nat := 118140960795 + 2198580 * 2 ^ 59
def prefixEnd_2198580 : Nat := 4983230072969 + 3 ^ 40 * 2198580 * 2
def baseEnd_2198580 : Nat := 1128928297362113279338921

theorem tailTrace_2198580 : CollatzResearch.WordTrace tailWord_2198580 prefixEnd_2198580 1128928297362113279338921 := by
  unfold tailWord_2198580
  simp only [CollatzResearch.WordTrace]
  refine ⟨40094400187463811207508597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53459200249951748276678129 40094400187463811207508597)
  ·
    refine ⟨3758850017574732300703931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40094400187463811207508597 3758850017574732300703931)
    ·
      refine ⟨5638275026362098451055897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3758850017574732300703931 5638275026362098451055897)
      ·
        refine ⟨4228706269771573838291923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5638275026362098451055897 4228706269771573838291923)
        ·
          refine ⟨6343059404657360757437885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228706269771573838291923 6343059404657360757437885)
          ·
            refine ⟨2378647276746510284039207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6343059404657360757437885 2378647276746510284039207)
            ·
              refine ⟨3567970915119765426058811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378647276746510284039207 3567970915119765426058811)
              ·
                refine ⟨5351956372679648139088217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3567970915119765426058811 5351956372679648139088217)
                ·
                  refine ⟨4013967279509736104316163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5351956372679648139088217 4013967279509736104316163)
                  ·
                    refine ⟨6020950919264604156474245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4013967279509736104316163 6020950919264604156474245)
                    ·
                      refine ⟨1128928297362113279338921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6020950919264604156474245 1128928297362113279338921)
                      ·
                        rfl

theorem cell23_2198580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2198580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198580 prefixEnd_2198580 := by exact prefixLift 2198580
  have htrace : WordTrace (prefixWord ++ tailWord_2198580) baseStart_2198580 baseEnd_2198580 := by
    simpa [prefixWord, tailWord_2198580, baseEnd_2198580] using wordTrace_append hprefix tailTrace_2198580
  have hstable : (prefixWord ++ tailWord_2198580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198580).length < 2 ^ (prefixWord ++ tailWord_2198580).sum := by decide
  have hdescent : baseEnd_2198580 < baseStart_2198580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198590 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2198590 : Nat := 118140960795 + 2198590 * 2 ^ 59
def prefixEnd_2198590 : Nat := 4983230072969 + 3 ^ 40 * 2198590 * 2
def baseEnd_2198590 : Nat := 376311144056219413404625

theorem tailTrace_2198590 : CollatzResearch.WordTrace tailWord_2198590 prefixEnd_2198590 376311144056219413404625 := by
  unfold tailWord_2198590
  simp only [CollatzResearch.WordTrace]
  refine ⟨10023645638111424265360153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53459443403260929415254149 10023645638111424265360153)
  ·
    refine ⟨7517734228583568199020115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10023645638111424265360153 7517734228583568199020115)
    ·
      refine ⟨11276601342875352298530173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517734228583568199020115 11276601342875352298530173)
      ·
        refine ⟨4228725503578257111948815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11276601342875352298530173 4228725503578257111948815)
        ·
          refine ⟨6343088255367385667923223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228725503578257111948815 6343088255367385667923223)
          ·
            refine ⟨9514632383051078501884835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343088255367385667923223 9514632383051078501884835)
            ·
              refine ⟨14271948574576617752827253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9514632383051078501884835 14271948574576617752827253)
              ·
                refine ⟨1337995178866557914327555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14271948574576617752827253 1337995178866557914327555)
                ·
                  refine ⟨2006992768299836871491333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1337995178866557914327555 2006992768299836871491333)
                  ·
                    refine ⟨376311144056219413404625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2006992768299836871491333 376311144056219413404625)
                    ·
                      rfl

theorem cell23_2198590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2198590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198590 prefixEnd_2198590 := by exact prefixLift 2198590
  have htrace : WordTrace (prefixWord ++ tailWord_2198590) baseStart_2198590 baseEnd_2198590 := by
    simpa [prefixWord, tailWord_2198590, baseEnd_2198590] using wordTrace_append hprefix tailTrace_2198590
  have hstable : (prefixWord ++ tailWord_2198590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198590).length < 2 ^ (prefixWord ++ tailWord_2198590).sum := by decide
  have hdescent : baseEnd_2198590 < baseStart_2198590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198613 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_2198613 : Nat := 118140960795 + 2198613 * 2 ^ 59
def prefixEnd_2198613 : Nat := 4983230072969 + 3 ^ 40 * 2198613 * 2
def baseEnd_2198613 : Nat := 1128945242223711650226269

theorem tailTrace_2198613 : CollatzResearch.WordTrace tailWord_2198613 prefixEnd_2198613 1128945242223711650226269 := by
  unfold tailWord_2198613
  simp only [CollatzResearch.WordTrace]
  refine ⟨80190003983808069050968493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53460002655872046033978995 80190003983808069050968493)
  ·
    refine ⟨30071251493928025894113185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80190003983808069050968493 30071251493928025894113185)
    ·
      refine ⟨22553438620446019420584889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30071251493928025894113185 22553438620446019420584889)
      ·
        refine ⟨16915078965334514565438667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22553438620446019420584889 16915078965334514565438667)
        ·
          refine ⟨25372618448001771848158001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16915078965334514565438667 25372618448001771848158001)
          ·
            refine ⟨19029463836001328886118501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25372618448001771848158001 19029463836001328886118501)
            ·
              refine ⟨3568024469250249166147219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19029463836001328886118501 3568024469250249166147219)
              ·
                refine ⟨5352036703875373749220829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3568024469250249166147219 5352036703875373749220829)
                ·
                  refine ⟨2007013763953265155957811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5352036703875373749220829 2007013763953265155957811)
                  ·
                    refine ⟨3010520645929897733936717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2007013763953265155957811 3010520645929897733936717)
                    ·
                      refine ⟨1128945242223711650226269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3010520645929897733936717 1128945242223711650226269)
                      ·
                        rfl

theorem cell23_2198613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_2198613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198613 prefixEnd_2198613 := by exact prefixLift 2198613
  have htrace : WordTrace (prefixWord ++ tailWord_2198613) baseStart_2198613 baseEnd_2198613 := by
    simpa [prefixWord, tailWord_2198613, baseEnd_2198613] using wordTrace_append hprefix tailTrace_2198613
  have hstable : (prefixWord ++ tailWord_2198613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198613).length < 2 ^ (prefixWord ++ tailWord_2198613).sum := by decide
  have hdescent : baseEnd_2198613 < baseStart_2198613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198636 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 6, 2]
def baseStart_2198636 : Nat := 118140960795 + 2198636 * 2 ^ 59
def prefixEnd_2198636 : Nat := 4983230072969 + 3 ^ 40 * 2198636 * 2
def baseEnd_2198636 : Nat := 1128957052278765060238663

theorem tailTrace_2198636 : CollatzResearch.WordTrace tailWord_2198636 prefixEnd_2198636 1128957052278765060238663 := by
  unfold tailWord_2198636
  simp only [CollatzResearch.WordTrace]
  refine ⟨40095421431362371989527881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53460561908483162652703841 40095421431362371989527881)
  ·
    refine ⟨30071566073521778992145911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40095421431362371989527881 30071566073521778992145911)
    ·
      refine ⟨45107349110282668488218867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30071566073521778992145911 45107349110282668488218867)
      ·
        refine ⟨67661023665424002732328301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45107349110282668488218867 67661023665424002732328301)
        ·
          refine ⟨25372883874534001024623113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67661023665424002732328301 25372883874534001024623113)
          ·
            refine ⟨19029662905900500768467335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25372883874534001024623113 19029662905900500768467335)
            ·
              refine ⟨28544494358850751152701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19029662905900500768467335 28544494358850751152701003)
              ·
                refine ⟨42816741538276126729051505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28544494358850751152701003 42816741538276126729051505)
                ·
                  refine ⟨32112556153707095046788629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42816741538276126729051505 32112556153707095046788629)
                  ·
                    refine ⟨1505276069705020080318217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 32112556153707095046788629 1505276069705020080318217)
                    ·
                      refine ⟨1128957052278765060238663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505276069705020080318217 1128957052278765060238663)
                      ·
                        rfl

theorem cell23_2198636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_2198636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198636 prefixEnd_2198636 := by exact prefixLift 2198636
  have htrace : WordTrace (prefixWord ++ tailWord_2198636) baseStart_2198636 baseEnd_2198636 := by
    simpa [prefixWord, tailWord_2198636, baseEnd_2198636] using wordTrace_append hprefix tailTrace_2198636
  have hstable : (prefixWord ++ tailWord_2198636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198636).length < 2 ^ (prefixWord ++ tailWord_2198636).sum := by decide
  have hdescent : baseEnd_2198636 < baseStart_2198636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198639 : List Nat := [1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 5]
def baseStart_2198639 : Nat := 118140960795 + 2198639 * 2 ^ 59
def prefixEnd_2198639 : Nat := 4983230072969 + 3 ^ 40 * 2198639 * 2
def baseEnd_2198639 : Nat := 1128958592720728548501149

theorem tailTrace_2198639 : CollatzResearch.WordTrace tailWord_2198639 prefixEnd_2198639 1128958592720728548501149 := by
  unfold tailWord_2198639
  simp only [CollatzResearch.WordTrace]
  refine ⟨80190952281713875491414971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53460634854475916994276647 80190952281713875491414971)
  ·
    refine ⟨120286428422570813237122457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80190952281713875491414971 120286428422570813237122457)
    ·
      refine ⟨90214821316928109927841843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120286428422570813237122457 90214821316928109927841843)
      ·
        refine ⟨135322231975392164891762765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90214821316928109927841843 135322231975392164891762765)
        ·
          refine ⟨50745836990772061834411037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135322231975392164891762765 50745836990772061834411037)
          ·
            refine ⟨19029688871539523187904139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50745836990772061834411037 19029688871539523187904139)
            ·
              refine ⟨28544533307309284781856209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19029688871539523187904139 28544533307309284781856209)
              ·
                refine ⟨21408399980481963586392157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28544533307309284781856209 21408399980481963586392157)
                ·
                  refine ⟨8028149992680736344897059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21408399980481963586392157 8028149992680736344897059)
                  ·
                    refine ⟨12042224989021104517345589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8028149992680736344897059 12042224989021104517345589)
                    ·
                      refine ⟨1128958592720728548501149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12042224989021104517345589 1128958592720728548501149)
                      ·
                        rfl

theorem cell23_2198639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 5].length) (baseStart_2198639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198639 prefixEnd_2198639 := by exact prefixLift 2198639
  have htrace : WordTrace (prefixWord ++ tailWord_2198639) baseStart_2198639 baseEnd_2198639 := by
    simpa [prefixWord, tailWord_2198639, baseEnd_2198639] using wordTrace_append hprefix tailTrace_2198639
  have hstable : (prefixWord ++ tailWord_2198639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198639).length < 2 ^ (prefixWord ++ tailWord_2198639).sum := by decide
  have hdescent : baseEnd_2198639 < baseStart_2198639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198646 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_2198646 : Nat := 118140960795 + 2198646 * 2 ^ 59
def prefixEnd_2198646 : Nat := 4983230072969 + 3 ^ 40 * 2198646 * 2
def baseEnd_2198646 : Nat := 376320729028436673704539

theorem tailTrace_2198646 : CollatzResearch.WordTrace tailWord_2198646 prefixEnd_2198646 376320729028436673704539 := by
  unfold tailWord_2198646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011950474543032230432487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53460805061792343791279861 5011950474543032230432487)
  ·
    refine ⟨7517925711814548345648731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5011950474543032230432487 7517925711814548345648731)
    ·
      refine ⟨11276888567721822518473097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7517925711814548345648731 11276888567721822518473097)
      ·
        refine ⟨8457666425791366888854823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11276888567721822518473097 8457666425791366888854823)
        ·
          refine ⟨12686499638687050333282235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8457666425791366888854823 12686499638687050333282235)
          ·
            refine ⟨19029749458030575499923353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12686499638687050333282235 19029749458030575499923353)
            ·
              refine ⟨14272312093522931624942515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19029749458030575499923353 14272312093522931624942515)
              ·
                refine ⟨21408468140284397437413773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14272312093522931624942515 21408468140284397437413773)
                ·
                  refine ⟨8028175552606649039030165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21408468140284397437413773 8028175552606649039030165)
                  ·
                    refine ⟨376320729028436673704539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8028175552606649039030165 376320729028436673704539)
                    ·
                      rfl

theorem cell23_2198646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_2198646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198646 prefixEnd_2198646 := by exact prefixLift 2198646
  have htrace : WordTrace (prefixWord ++ tailWord_2198646) baseStart_2198646 baseEnd_2198646 := by
    simpa [prefixWord, tailWord_2198646, baseEnd_2198646] using wordTrace_append hprefix tailTrace_2198646
  have hstable : (prefixWord ++ tailWord_2198646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198646).length < 2 ^ (prefixWord ++ tailWord_2198646).sum := by decide
  have hdescent : baseEnd_2198646 < baseStart_2198646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198664 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2198664 : Nat := 118140960795 + 2198664 * 2 ^ 59
def prefixEnd_2198664 : Nat := 4983230072969 + 3 ^ 40 * 2198664 * 2
def baseEnd_2198664 : Nat := 1128971429737090950688535

theorem tailTrace_2198664 : CollatzResearch.WordTrace tailWord_2198664 prefixEnd_2198664 1128971429737090950688535 := by
  unfold tailWord_2198664
  simp only [CollatzResearch.WordTrace]
  refine ⟨40095932053311652380537523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53461242737748869840716697 40095932053311652380537523)
  ·
    refine ⟨60143898079967478570806285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40095932053311652380537523 60143898079967478570806285)
    ·
      refine ⟨22553961779987804464052357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60143898079967478570806285 22553961779987804464052357)
      ·
        refine ⟨4228867833747713337009817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22553961779987804464052357 4228867833747713337009817)
        ·
          refine ⟨3171650875310785002757363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4228867833747713337009817 3171650875310785002757363)
          ·
            refine ⟨4757476312966177504136045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171650875310785002757363 4757476312966177504136045)
            ·
              refine ⟨1784053617362316564051017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4757476312966177504136045 1784053617362316564051017)
              ·
                refine ⟨1338040213021737423038263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784053617362316564051017 1338040213021737423038263)
                ·
                  refine ⟨2007060319532606134557395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338040213021737423038263 2007060319532606134557395)
                  ·
                    refine ⟨3010590479298909201836093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2007060319532606134557395 3010590479298909201836093)
                    ·
                      refine ⟨1128971429737090950688535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3010590479298909201836093 1128971429737090950688535)
                      ·
                        rfl

theorem cell23_2198664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2198664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198664 prefixEnd_2198664 := by exact prefixLift 2198664
  have htrace : WordTrace (prefixWord ++ tailWord_2198664) baseStart_2198664 baseEnd_2198664 := by
    simpa [prefixWord, tailWord_2198664, baseEnd_2198664] using wordTrace_append hprefix tailTrace_2198664
  have hstable : (prefixWord ++ tailWord_2198664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198664).length < 2 ^ (prefixWord ++ tailWord_2198664).sum := by decide
  have hdescent : baseEnd_2198664 < baseStart_2198664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198680 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 2, 4]
def baseStart_2198680 : Nat := 118140960795 + 2198680 * 2 ^ 59
def prefixEnd_2198680 : Nat := 4983230072969 + 3 ^ 40 * 2198680 * 2
def baseEnd_2198680 : Nat := 376326548475854296029487

theorem tailTrace_2198680 : CollatzResearch.WordTrace tailWord_2198680 prefixEnd_2198680 376326548475854296029487 := by
  unfold tailWord_2198680
  simp only [CollatzResearch.WordTrace]
  refine ⟨40096223837282669746828747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53461631783043559662438329 40096223837282669746828747)
  ·
    refine ⟨60144335755924004620243121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40096223837282669746828747 60144335755924004620243121)
    ·
      refine ⟨45108251816943003465182341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60144335755924004620243121 45108251816943003465182341)
      ·
        refine ⟨8457797215676813149721689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45108251816943003465182341 8457797215676813149721689)
        ·
          refine ⟨6343347911757609862291267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8457797215676813149721689 6343347911757609862291267)
          ·
            refine ⟨9515021867636414793436901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343347911757609862291267 9515021867636414793436901)
            ·
              refine ⟨1784066600181827773769419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9515021867636414793436901 1784066600181827773769419)
              ·
                refine ⟨2676099900272741660654129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784066600181827773769419 2676099900272741660654129)
                ·
                  refine ⟨2007074925204556245490597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676099900272741660654129 2007074925204556245490597)
                  ·
                    refine ⟨376326548475854296029487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2007074925204556245490597 376326548475854296029487)
                    ·
                      rfl

theorem cell23_2198680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_2198680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198680 prefixEnd_2198680 := by exact prefixLift 2198680
  have htrace : WordTrace (prefixWord ++ tailWord_2198680) baseStart_2198680 baseEnd_2198680 := by
    simpa [prefixWord, tailWord_2198680, baseEnd_2198680] using wordTrace_append hprefix tailTrace_2198680
  have hstable : (prefixWord ++ tailWord_2198680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198680).length < 2 ^ (prefixWord ++ tailWord_2198680).sum := by decide
  have hdescent : baseEnd_2198680 < baseStart_2198680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198687 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2198687 : Nat := 118140960795 + 2198687 * 2 ^ 59
def prefixEnd_2198687 : Nat := 4983230072969 + 3 ^ 40 * 2198687 * 2
def baseEnd_2198687 : Nat := 1128983239792144360700929

theorem tailTrace_2198687 : CollatzResearch.WordTrace tailWord_2198687 prefixEnd_2198687 1128983239792144360700929 := by
  unfold tailWord_2198687
  simp only [CollatzResearch.WordTrace]
  refine ⟨80192702985539979689162315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53461801990359986459441543 80192702985539979689162315)
  ·
    refine ⟨120289054478309969533743473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80192702985539979689162315 120289054478309969533743473)
    ·
      refine ⟨90216790858732477150307605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120289054478309969533743473 90216790858732477150307605)
      ·
        refine ⟨4228912071503084866420669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90216790858732477150307605 4228912071503084866420669)
        ·
          refine ⟨1585842026813656824907751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4228912071503084866420669 1585842026813656824907751)
          ·
            refine ⟨2378763040220485237361627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1585842026813656824907751 2378763040220485237361627)
            ·
              refine ⟨3568144560330727856042441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2378763040220485237361627 3568144560330727856042441)
              ·
                refine ⟨2676108420248045892031831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3568144560330727856042441 2676108420248045892031831)
                ·
                  refine ⟨4014162630372068838047747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676108420248045892031831 4014162630372068838047747)
                  ·
                    refine ⟨6021243945558103257071621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014162630372068838047747 6021243945558103257071621)
                    ·
                      refine ⟨1128983239792144360700929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6021243945558103257071621 1128983239792144360700929)
                      ·
                        rfl

theorem cell23_2198687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2198687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198687 prefixEnd_2198687 := by exact prefixLift 2198687
  have htrace : WordTrace (prefixWord ++ tailWord_2198687) baseStart_2198687 baseEnd_2198687 := by
    simpa [prefixWord, tailWord_2198687, baseEnd_2198687] using wordTrace_append hprefix tailTrace_2198687
  have hstable : (prefixWord ++ tailWord_2198687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198687).length < 2 ^ (prefixWord ++ tailWord_2198687).sum := by decide
  have hdescent : baseEnd_2198687 < baseStart_2198687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198690 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2198690 : Nat := 118140960795 + 2198690 * 2 ^ 59
def prefixEnd_2198690 : Nat := 4983230072969 + 3 ^ 40 * 2198690 * 2
def baseEnd_2198690 : Nat := 1128984780234107848963415

theorem tailTrace_2198690 : CollatzResearch.WordTrace tailWord_2198690 prefixEnd_2198690 1128984780234107848963415 := by
  unfold tailWord_2198690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20048203101132277800380381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53461874936352740801014349 20048203101132277800380381)
  ·
    refine ⟨7518076162924604175142643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20048203101132277800380381 7518076162924604175142643)
    ·
      refine ⟨11277114244386906262713965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7518076162924604175142643 11277114244386906262713965)
      ·
        refine ⟨4228917841645089848517737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11277114244386906262713965 4228917841645089848517737)
        ·
          refine ⟨3171688381233817386388303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4228917841645089848517737 3171688381233817386388303)
          ·
            refine ⟨4757532571850726079582455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3171688381233817386388303 4757532571850726079582455)
            ·
              refine ⟨7136298857776089119373683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4757532571850726079582455 7136298857776089119373683)
              ·
                refine ⟨10704448286664133679060525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7136298857776089119373683 10704448286664133679060525)
                ·
                  refine ⟨4014168107499050129647697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10704448286664133679060525 4014168107499050129647697)
                  ·
                    refine ⟨3010626080624287597235773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4014168107499050129647697 3010626080624287597235773)
                    ·
                      refine ⟨1128984780234107848963415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3010626080624287597235773 1128984780234107848963415)
                      ·
                        rfl

theorem cell23_2198690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2198690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198690 prefixEnd_2198690 := by exact prefixLift 2198690
  have htrace : WordTrace (prefixWord ++ tailWord_2198690) baseStart_2198690 baseEnd_2198690 := by
    simpa [prefixWord, tailWord_2198690, baseEnd_2198690] using wordTrace_append hprefix tailTrace_2198690
  have hstable : (prefixWord ++ tailWord_2198690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198690).length < 2 ^ (prefixWord ++ tailWord_2198690).sum := by decide
  have hdescent : baseEnd_2198690 < baseStart_2198690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198710 : List Nat := [5, 1, 3, 2, 2, 10]
def baseStart_2198710 : Nat := 118140960795 + 2198710 * 2 ^ 59
def prefixEnd_2198710 : Nat := 4983230072969 + 3 ^ 40 * 2198710 * 2
def baseEnd_2198710 : Nat := 4646070163980237739561

theorem tailTrace_2198710 : CollatzResearch.WordTrace tailWord_2198710 prefixEnd_2198710 4646070163980237739561 := by
  unfold tailWord_2198710
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012096366528540913578099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53462361242971103078166389 5012096366528540913578099)
  ·
    refine ⟨7518144549792811370367149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5012096366528540913578099 7518144549792811370367149)
    ·
      refine ⟨2819304206172304263887681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7518144549792811370367149 2819304206172304263887681)
      ·
        refine ⟨2114478154629228197915761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2819304206172304263887681 2114478154629228197915761)
        ·
          refine ⟨1585858615971921148436821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2114478154629228197915761 1585858615971921148436821)
          ·
            refine ⟨4646070163980237739561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1585858615971921148436821 4646070163980237739561)
            ·
              rfl

theorem cell23_2198710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 10].length) (baseStart_2198710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198710 prefixEnd_2198710 := by exact prefixLift 2198710
  have htrace : WordTrace (prefixWord ++ tailWord_2198710) baseStart_2198710 baseEnd_2198710 := by
    simpa [prefixWord, tailWord_2198710, baseEnd_2198710] using wordTrace_append hprefix tailTrace_2198710
  have hstable : (prefixWord ++ tailWord_2198710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198710).length < 2 ^ (prefixWord ++ tailWord_2198710).sum := by decide
  have hdescent : baseEnd_2198710 < baseStart_2198710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198721 : List Nat := [1, 2, 6, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_2198721 : Nat := 118140960795 + 2198721 * 2 ^ 59
def prefixEnd_2198721 : Nat := 4983230072969 + 3 ^ 40 * 2198721 * 2
def baseEnd_2198721 : Nat := 1129000698134397227675773

theorem tailTrace_2198721 : CollatzResearch.WordTrace tailWord_2198721 prefixEnd_2198721 1129000698134397227675773 := by
  unfold tailWord_2198721
  simp only [CollatzResearch.WordTrace]
  refine ⟨80193943067416803495900017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53462628711611202330600011 80193943067416803495900017)
  ·
    refine ⟨60145457300562602621925013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80193943067416803495900017 60145457300562602621925013)
    ·
      refine ⟨2819318310963871997902735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60145457300562602621925013 2819318310963871997902735)
      ·
        refine ⟨4228977466445807996854103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819318310963871997902735 4228977466445807996854103)
        ·
          refine ⟨6343466199668711995281155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228977466445807996854103 6343466199668711995281155)
          ·
            refine ⟨9515199299503067992921733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343466199668711995281155 9515199299503067992921733)
            ·
              refine ⟨1784099868656825248672825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9515199299503067992921733 1784099868656825248672825)
              ·
                refine ⟨1338074901492618936504619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784099868656825248672825 1338074901492618936504619)
                ·
                  refine ⟨2007112352238928404756929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338074901492618936504619 2007112352238928404756929)
                  ·
                    refine ⟨1505334264179196303567697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2007112352238928404756929 1505334264179196303567697)
                    ·
                      refine ⟨1129000698134397227675773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505334264179196303567697 1129000698134397227675773)
                      ·
                        rfl

theorem cell23_2198721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_2198721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198721 prefixEnd_2198721 := by exact prefixLift 2198721
  have htrace : WordTrace (prefixWord ++ tailWord_2198721) baseStart_2198721 baseEnd_2198721 := by
    simpa [prefixWord, tailWord_2198721, baseEnd_2198721] using wordTrace_append hprefix tailTrace_2198721
  have hstable : (prefixWord ++ tailWord_2198721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198721).length < 2 ^ (prefixWord ++ tailWord_2198721).sum := by decide
  have hdescent : baseEnd_2198721 < baseStart_2198721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198739 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_2198739 : Nat := 118140960795 + 2198739 * 2 ^ 59
def prefixEnd_2198739 : Nat := 4983230072969 + 3 ^ 40 * 2198739 * 2
def baseEnd_2198739 : Nat := 1129009940786178157250689

theorem tailTrace_2198739 : CollatzResearch.WordTrace tailWord_2198739 prefixEnd_2198739 1129009940786178157250689 := by
  unfold tailWord_2198739
  simp only [CollatzResearch.WordTrace]
  refine ⟨80194599581351592570055271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53463066387567728380036847 80194599581351592570055271)
  ·
    refine ⟨120291899372027388855082907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80194599581351592570055271 120291899372027388855082907)
    ·
      refine ⟨180437849058041083282624361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120291899372027388855082907 180437849058041083282624361)
      ·
        refine ⟨135328386793530812461968271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180437849058041083282624361 135328386793530812461968271)
        ·
          refine ⟨202992580190296218692952407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135328386793530812461968271 202992580190296218692952407)
          ·
            refine ⟨304488870285444328039428611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202992580190296218692952407 304488870285444328039428611)
            ·
              refine ⟨456733305428166492059142917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304488870285444328039428611 456733305428166492059142917)
              ·
                refine ⟨85637494767781217261089297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 456733305428166492059142917 85637494767781217261089297)
                ·
                  refine ⟨64228121075835912945816973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85637494767781217261089297 64228121075835912945816973)
                  ·
                    refine ⟨24085545403438467354681365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64228121075835912945816973 24085545403438467354681365)
                    ·
                      refine ⟨1129009940786178157250689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24085545403438467354681365 1129009940786178157250689)
                      ·
                        rfl

theorem cell23_2198739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_2198739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198739 prefixEnd_2198739 := by exact prefixLift 2198739
  have htrace : WordTrace (prefixWord ++ tailWord_2198739) baseStart_2198739 baseEnd_2198739 := by
    simpa [prefixWord, tailWord_2198739, baseEnd_2198739] using wordTrace_append hprefix tailTrace_2198739
  have hstable : (prefixWord ++ tailWord_2198739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198739).length < 2 ^ (prefixWord ++ tailWord_2198739).sum := by decide
  have hdescent : baseEnd_2198739 < baseStart_2198739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198743 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 1, 4, 2]
def baseStart_2198743 : Nat := 118140960795 + 2198743 * 2 ^ 59
def prefixEnd_2198743 : Nat := 4983230072969 + 3 ^ 40 * 2198743 * 2
def baseEnd_2198743 : Nat := 1129011994708796141600671

theorem tailTrace_2198743 : CollatzResearch.WordTrace tailWord_2198743 prefixEnd_2198743 1129011994708796141600671 := by
  unfold tailWord_2198743
  simp only [CollatzResearch.WordTrace]
  refine ⟨80194745473337101253200883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53463163648891400835467255 80194745473337101253200883)
  ·
    refine ⟨120292118210005651879801325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80194745473337101253200883 120292118210005651879801325)
    ·
      refine ⟨45109544328752119454925497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120292118210005651879801325 45109544328752119454925497)
      ·
        refine ⟨33832158246564089591194123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45109544328752119454925497 33832158246564089591194123)
        ·
          refine ⟨50748237369846134386791185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33832158246564089591194123 50748237369846134386791185)
          ·
            refine ⟨38061178027384600790093389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50748237369846134386791185 38061178027384600790093389)
            ·
              refine ⟨14272941760269225296285021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38061178027384600790093389 14272941760269225296285021)
              ·
                refine ⟨5352353160100959486106883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14272941760269225296285021 5352353160100959486106883)
                ·
                  refine ⟨8028529740151439229160325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352353160100959486106883 8028529740151439229160325)
                  ·
                    refine ⟨1505349326278394855467561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8028529740151439229160325 1505349326278394855467561)
                    ·
                      refine ⟨1129011994708796141600671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505349326278394855467561 1129011994708796141600671)
                      ·
                        rfl

theorem cell23_2198743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 4, 2].length) (baseStart_2198743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198743 prefixEnd_2198743 := by exact prefixLift 2198743
  have htrace : WordTrace (prefixWord ++ tailWord_2198743) baseStart_2198743 baseEnd_2198743 := by
    simpa [prefixWord, tailWord_2198743, baseEnd_2198743] using wordTrace_append hprefix tailTrace_2198743
  have hstable : (prefixWord ++ tailWord_2198743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198743).length < 2 ^ (prefixWord ++ tailWord_2198743).sum := by decide
  have hdescent : baseEnd_2198743 < baseStart_2198743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198746 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3]
def baseStart_2198746 : Nat := 118140960795 + 2198746 * 2 ^ 59
def prefixEnd_2198746 : Nat := 4983230072969 + 3 ^ 40 * 2198746 * 2
def baseEnd_2198746 : Nat := 1129013535150759629863157

theorem tailTrace_2198746 : CollatzResearch.WordTrace tailWord_2198746 prefixEnd_2198746 1129013535150759629863157 := by
  unfold tailWord_2198746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20048713723081558191390023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53463236594884155177040061 20048713723081558191390023)
  ·
    refine ⟨30073070584622337287085035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20048713723081558191390023 30073070584622337287085035)
    ·
      refine ⟨45109605876933505930627553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30073070584622337287085035 45109605876933505930627553)
      ·
        refine ⟨33832204407700129447970665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45109605876933505930627553 33832204407700129447970665)
        ·
          refine ⟨25374153305775097085977999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33832204407700129447970665 25374153305775097085977999)
          ·
            refine ⟨38061229958662645628966999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25374153305775097085977999 38061229958662645628966999)
            ·
              refine ⟨57091844937993968443450499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38061229958662645628966999 57091844937993968443450499)
              ·
                refine ⟨85637767406990952665175749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57091844937993968443450499 85637767406990952665175749)
                ·
                  refine ⟨16057081388810803624720453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85637767406990952665175749 16057081388810803624720453)
                  ·
                    refine ⟨3010702760402025679635085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16057081388810803624720453 3010702760402025679635085)
                    ·
                      refine ⟨1129013535150759629863157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3010702760402025679635085 1129013535150759629863157)
                      ·
                        rfl

theorem cell23_2198746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3].length) (baseStart_2198746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198746 prefixEnd_2198746 := by exact prefixLift 2198746
  have htrace : WordTrace (prefixWord ++ tailWord_2198746) baseStart_2198746 baseEnd_2198746 := by
    simpa [prefixWord, tailWord_2198746, baseEnd_2198746] using wordTrace_append hprefix tailTrace_2198746
  have hstable : (prefixWord ++ tailWord_2198746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198746).length < 2 ^ (prefixWord ++ tailWord_2198746).sum := by decide
  have hdescent : baseEnd_2198746 < baseStart_2198746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198760 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_2198760 : Nat := 118140960795 + 2198760 * 2 ^ 59
def prefixEnd_2198760 : Nat := 4983230072969 + 3 ^ 40 * 2198760 * 2
def baseEnd_2198760 : Nat := 1129020723879922575088093

theorem tailTrace_2198760 : CollatzResearch.WordTrace tailWord_2198760 prefixEnd_2198760 1129020723879922575088093 := by
  unfold tailWord_2198760
  simp only [CollatzResearch.WordTrace]
  refine ⟨40097682757137756578284867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53463577009517008771046489 40097682757137756578284867)
  ·
    refine ⟨60146524135706634867427301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40097682757137756578284867 60146524135706634867427301)
    ·
      refine ⟨11277473275444994037642619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60146524135706634867427301 11277473275444994037642619)
      ·
        refine ⟨16916209913167491056463929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11277473275444994037642619 16916209913167491056463929)
        ·
          refine ⟨12687157434875618292347947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16916209913167491056463929 12687157434875618292347947)
          ·
            refine ⟨19030736152313427438521921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12687157434875618292347947 19030736152313427438521921)
            ·
              refine ⟨14273052114235070578891441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19030736152313427438521921 14273052114235070578891441)
              ·
                refine ⟨10704789085676302934168581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14273052114235070578891441 10704789085676302934168581)
                ·
                  refine ⟨2007147953564306800156609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10704789085676302934168581 2007147953564306800156609)
                  ·
                    refine ⟨1505360965173230100117457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2007147953564306800156609 1505360965173230100117457)
                    ·
                      refine ⟨1129020723879922575088093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505360965173230100117457 1129020723879922575088093)
                      ·
                        rfl

theorem cell23_2198760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_2198760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198760 prefixEnd_2198760 := by exact prefixLift 2198760
  have htrace : WordTrace (prefixWord ++ tailWord_2198760) baseStart_2198760 baseEnd_2198760 := by
    simpa [prefixWord, tailWord_2198760, baseEnd_2198760] using wordTrace_append hprefix tailTrace_2198760
  have hstable : (prefixWord ++ tailWord_2198760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198760).length < 2 ^ (prefixWord ++ tailWord_2198760).sum := by decide
  have hdescent : baseEnd_2198760 < baseStart_2198760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198783 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 5]
def baseStart_2198783 : Nat := 118140960795 + 2198783 * 2 ^ 59
def prefixEnd_2198783 : Nat := 4983230072969 + 3 ^ 40 * 2198783 * 2
def baseEnd_2198783 : Nat := 125448059326108442788943

theorem tailTrace_2198783 : CollatzResearch.WordTrace tailWord_2198783 prefixEnd_2198783 125448059326108442788943 := by
  unfold tailWord_2198783
  simp only [CollatzResearch.WordTrace]
  refine ⟨80196204393192188084657003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53464136262128125389771335 80196204393192188084657003)
  ·
    refine ⟨120294306589788282126985505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80196204393192188084657003 120294306589788282126985505)
    ·
      refine ⟨90220729942341211595239129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120294306589788282126985505 90220729942341211595239129)
      ·
        refine ⟨67665547456755908696429347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90220729942341211595239129 67665547456755908696429347)
        ·
          refine ⟨101498321185133863044644021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67665547456755908696429347 101498321185133863044644021)
          ·
            refine ⟨9515467611106299660435377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101498321185133863044644021 9515467611106299660435377)
            ·
              refine ⟨7136600708329724745326533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9515467611106299660435377 7136600708329724745326533)
              ·
                refine ⟨1338112632811823389748725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7136600708329724745326533 1338112632811823389748725)
                ·
                  refine ⟨125448059326108442788943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1338112632811823389748725 125448059326108442788943)
                  ·
                    rfl

theorem cell23_2198783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 5].length) (baseStart_2198783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198783 prefixEnd_2198783 := by exact prefixLift 2198783
  have htrace : WordTrace (prefixWord ++ tailWord_2198783) baseStart_2198783 baseEnd_2198783 := by
    simpa [prefixWord, tailWord_2198783, baseEnd_2198783] using wordTrace_append hprefix tailTrace_2198783
  have hstable : (prefixWord ++ tailWord_2198783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198783).length < 2 ^ (prefixWord ++ tailWord_2198783).sum := by decide
  have hdescent : baseEnd_2198783 < baseStart_2198783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198796 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 1, 7]
def baseStart_2198796 : Nat := 118140960795 + 2198796 * 2 ^ 59
def prefixEnd_2198796 : Nat := 4983230072969 + 3 ^ 40 * 2198796 * 2
def baseEnd_2198796 : Nat := 376346403061161478079309

theorem tailTrace_2198796 : CollatzResearch.WordTrace tailWord_2198796 prefixEnd_2198796 376346403061161478079309 := by
  unfold tailWord_2198796
  simp only [CollatzResearch.WordTrace]
  refine ⟨40098339271072545652440121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53464452361430060869920161 40098339271072545652440121)
  ·
    refine ⟨30073754453304409239330091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40098339271072545652440121 30073754453304409239330091)
    ·
      refine ⟨45110631679956613858995137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30073754453304409239330091 45110631679956613858995137)
      ·
        refine ⟨33832973759967460394246353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45110631679956613858995137 33832973759967460394246353)
        ·
          refine ⟨25374730319975595295684765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33832973759967460394246353 25374730319975595295684765)
          ·
            refine ⟨9515523869990848235881787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25374730319975595295684765 9515523869990848235881787)
            ·
              refine ⟨14273285804986272353822681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9515523869990848235881787 14273285804986272353822681)
              ·
                refine ⟨10704964353739704265367011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14273285804986272353822681 10704964353739704265367011)
                ·
                  refine ⟨16057446530609556398050517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10704964353739704265367011 16057446530609556398050517)
                  ·
                    refine ⟨376346403061161478079309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16057446530609556398050517 376346403061161478079309)
                    ·
                      rfl

theorem cell23_2198796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 7].length) (baseStart_2198796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198796 prefixEnd_2198796 := by exact prefixLift 2198796
  have htrace : WordTrace (prefixWord ++ tailWord_2198796) baseStart_2198796 baseEnd_2198796 := by
    simpa [prefixWord, tailWord_2198796, baseEnd_2198796] using wordTrace_append hprefix tailTrace_2198796
  have hstable : (prefixWord ++ tailWord_2198796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198796).length < 2 ^ (prefixWord ++ tailWord_2198796).sum := by decide
  have hdescent : baseEnd_2198796 < baseStart_2198796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198813 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 1, 7]
def baseStart_2198813 : Nat := 118140960795 + 2198813 * 2 ^ 59
def prefixEnd_2198813 : Nat := 4983230072969 + 3 ^ 40 * 2198813 * 2
def baseEnd_2198813 : Nat := 376349312784870289241783

theorem tailTrace_2198813 : CollatzResearch.WordTrace tailWord_2198813 prefixEnd_2198813 376349312784870289241783 := by
  unfold tailWord_2198813
  simp only [CollatzResearch.WordTrace]
  refine ⟨80197298583083503208249093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53464865722055668805499395 80197298583083503208249093)
  ·
    refine ⟨15036993484328156851546705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80197298583083503208249093 15036993484328156851546705)
    ·
      refine ⟨11277745113246117638660029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15036993484328156851546705 11277745113246117638660029)
      ·
        refine ⟨4229154417467294114497511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11277745113246117638660029 4229154417467294114497511)
        ·
          refine ⟨6343731626200941171746267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4229154417467294114497511 6343731626200941171746267)
          ·
            refine ⟨9515597439301411757619401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343731626200941171746267 9515597439301411757619401)
            ·
              refine ⟨7136698079476058818214551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9515597439301411757619401 7136698079476058818214551)
              ·
                refine ⟨10705047119214088227321827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7136698079476058818214551 10705047119214088227321827)
                ·
                  refine ⟨16057570678821132340982741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10705047119214088227321827 16057570678821132340982741)
                  ·
                    refine ⟨376349312784870289241783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16057570678821132340982741 376349312784870289241783)
                    ·
                      rfl

theorem cell23_2198813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_2198813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198813 prefixEnd_2198813 := by exact prefixLift 2198813
  have htrace : WordTrace (prefixWord ++ tailWord_2198813) baseStart_2198813 baseEnd_2198813 := by
    simpa [prefixWord, tailWord_2198813, baseEnd_2198813] using wordTrace_append hprefix tailTrace_2198813
  have hstable : (prefixWord ++ tailWord_2198813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198813).length < 2 ^ (prefixWord ++ tailWord_2198813).sum := by decide
  have hdescent : baseEnd_2198813 < baseStart_2198813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198833 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 4]
def baseStart_2198833 : Nat := 118140960795 + 2198833 * 2 ^ 59
def prefixEnd_2198833 : Nat := 4983230072969 + 3 ^ 40 * 2198833 * 2
def baseEnd_2198833 : Nat := 1129058207967700789475257

theorem tailTrace_2198833 : CollatzResearch.WordTrace tailWord_2198833 prefixEnd_2198833 1129058207967700789475257 := by
  unfold tailWord_2198833
  simp only [CollatzResearch.WordTrace]
  refine ⟨80198028043011046623977153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53465352028674031082651435 80198028043011046623977153)
  ·
    refine ⟨60148521032258284967982865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80198028043011046623977153 60148521032258284967982865)
    ·
      refine ⟨45111390774193713725987149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60148521032258284967982865 45111390774193713725987149)
      ·
        refine ⟨16916771540322642647245181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45111390774193713725987149 16916771540322642647245181)
        ·
          refine ⟨6343789327620990992716943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16916771540322642647245181 6343789327620990992716943)
          ·
            refine ⟨9515683991431486489075415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343789327620990992716943 9515683991431486489075415)
            ·
              refine ⟨14273525987147229733613123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9515683991431486489075415 14273525987147229733613123)
              ·
                refine ⟨21410288980720844600419685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14273525987147229733613123 21410288980720844600419685)
                ·
                  refine ⟨4014429183885158362578691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21410288980720844600419685 4014429183885158362578691)
                  ·
                    refine ⟨6021643775827737543868037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014429183885158362578691 6021643775827737543868037)
                    ·
                      refine ⟨1129058207967700789475257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6021643775827737543868037 1129058207967700789475257)
                      ·
                        rfl

theorem cell23_2198833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_2198833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198833 prefixEnd_2198833 := by exact prefixLift 2198833
  have htrace : WordTrace (prefixWord ++ tailWord_2198833) baseStart_2198833 baseEnd_2198833 := by
    simpa [prefixWord, tailWord_2198833, baseEnd_2198833] using wordTrace_append hprefix tailTrace_2198833
  have hstable : (prefixWord ++ tailWord_2198833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198833).length < 2 ^ (prefixWord ++ tailWord_2198833).sum := by decide
  have hdescent : baseEnd_2198833 < baseStart_2198833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198923 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 4]
def baseStart_2198923 : Nat := 118140960795 + 2198923 * 2 ^ 59
def prefixEnd_2198923 : Nat := 4983230072969 + 3 ^ 40 * 2198923 * 2
def baseEnd_2198923 : Nat := 1129104421226605437349843

theorem tailTrace_2198923 : CollatzResearch.WordTrace tailWord_2198923 prefixEnd_2198923 1129104421226605437349843 := by
  unfold tailWord_2198923
  simp only [CollatzResearch.WordTrace]
  refine ⟨80201310612684991994753423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53467540408456661329835615 80201310612684991994753423)
  ·
    refine ⟨120301965919027487992130135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80201310612684991994753423 120301965919027487992130135)
    ·
      refine ⟨180452948878541231988195203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120301965919027487992130135 180452948878541231988195203)
      ·
        refine ⟨270679423317811847982292805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180452948878541231988195203 270679423317811847982292805)
        ·
          refine ⟨50752391872089721496679901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 270679423317811847982292805 50752391872089721496679901)
          ·
            refine ⟨19032146952033645561254963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50752391872089721496679901 19032146952033645561254963)
            ·
              refine ⟨28548220428050468341882445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19032146952033645561254963 28548220428050468341882445)
              ·
                refine ⟨10705582660518925628205917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28548220428050468341882445 10705582660518925628205917)
                ·
                  refine ⟨4014593497694597110577219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10705582660518925628205917 4014593497694597110577219)
                  ·
                    refine ⟨6021890246541895665865829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014593497694597110577219 6021890246541895665865829)
                    ·
                      refine ⟨1129104421226605437349843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6021890246541895665865829 1129104421226605437349843)
                      ·
                        rfl

theorem cell23_2198923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 1, 4].length) (baseStart_2198923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198923 prefixEnd_2198923 := by exact prefixLift 2198923
  have htrace : WordTrace (prefixWord ++ tailWord_2198923) baseStart_2198923 baseEnd_2198923 := by
    simpa [prefixWord, tailWord_2198923, baseEnd_2198923] using wordTrace_append hprefix tailTrace_2198923
  have hstable : (prefixWord ++ tailWord_2198923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198923).length < 2 ^ (prefixWord ++ tailWord_2198923).sum := by decide
  have hdescent : baseEnd_2198923 < baseStart_2198923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198933 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_2198933 : Nat := 118140960795 + 2198933 * 2 ^ 59
def prefixEnd_2198933 : Nat := 4983230072969 + 3 ^ 40 * 2198933 * 2
def baseEnd_2198933 : Nat := 376369852011050132741599

theorem tailTrace_2198933 : CollatzResearch.WordTrace tailWord_2198933 prefixEnd_2198933 376369852011050132741599 := by
  unfold tailWord_2198933
  simp only [CollatzResearch.WordTrace]
  refine ⟨80201675342648763702617453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53467783561765842468411635 80201675342648763702617453)
  ·
    refine ⟨30075628253493286388481545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80201675342648763702617453 30075628253493286388481545)
    ·
      refine ⟨22556721190119964791361159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30075628253493286388481545 22556721190119964791361159)
      ·
        refine ⟨33835081785179947187041739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22556721190119964791361159 33835081785179947187041739)
        ·
          refine ⟨50752622677769920780562609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33835081785179947187041739 50752622677769920780562609)
          ·
            refine ⟨38064467008327440585421957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50752622677769920780562609 38064467008327440585421957)
            ·
              refine ⟨7137087564061395109766617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38064467008327440585421957 7137087564061395109766617)
              ·
                refine ⟨5352815673046046332324963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7137087564061395109766617 5352815673046046332324963)
                ·
                  refine ⟨8029223509569069498487445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352815673046046332324963 8029223509569069498487445)
                  ·
                    refine ⟨376369852011050132741599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8029223509569069498487445 376369852011050132741599)
                    ·
                      rfl

theorem cell23_2198933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_2198933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198933 prefixEnd_2198933 := by exact prefixLift 2198933
  have htrace : WordTrace (prefixWord ++ tailWord_2198933) baseStart_2198933 baseEnd_2198933 := by
    simpa [prefixWord, tailWord_2198933, baseEnd_2198933] using wordTrace_append hprefix tailTrace_2198933
  have hstable : (prefixWord ++ tailWord_2198933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198933).length < 2 ^ (prefixWord ++ tailWord_2198933).sum := by decide
  have hdescent : baseEnd_2198933 < baseStart_2198933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198937 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 1, 5]
def baseStart_2198937 : Nat := 118140960795 + 2198937 * 2 ^ 59
def prefixEnd_2198937 : Nat := 4983230072969 + 3 ^ 40 * 2198937 * 2
def baseEnd_2198937 : Nat := 376370536651922794191593

theorem tailTrace_2198937 : CollatzResearch.WordTrace tailWord_2198937 prefixEnd_2198937 376370536651922794191593 := by
  unfold tailWord_2198937
  simp only [CollatzResearch.WordTrace]
  refine ⟨80201821234634272385763065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53467880823089514923842043 80201821234634272385763065)
  ·
    refine ⟨60151365925975704289322299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80201821234634272385763065 60151365925975704289322299)
    ·
      refine ⟨90227048888963556433983449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60151365925975704289322299 90227048888963556433983449)
      ·
        refine ⟨67670286666722667325487587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90227048888963556433983449 67670286666722667325487587)
        ·
          refine ⟨101505430000084000988231381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67670286666722667325487587 101505430000084000988231381)
          ·
            refine ⟨2379033515626968773161673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 101505430000084000988231381 2379033515626968773161673)
            ·
              refine ⟨1784275136720226579871255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379033515626968773161673 1784275136720226579871255)
              ·
                refine ⟨2676412705080339869806883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784275136720226579871255 2676412705080339869806883)
                ·
                  refine ⟨4014619057620509804710325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676412705080339869806883 4014619057620509804710325)
                  ·
                    refine ⟨376370536651922794191593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4014619057620509804710325 376370536651922794191593)
                    ·
                      rfl

theorem cell23_2198937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 5].length) (baseStart_2198937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198937 prefixEnd_2198937 := by exact prefixLift 2198937
  have htrace : WordTrace (prefixWord ++ tailWord_2198937) baseStart_2198937 baseEnd_2198937 := by
    simpa [prefixWord, tailWord_2198937, baseEnd_2198937] using wordTrace_append hprefix tailTrace_2198937
  have hstable : (prefixWord ++ tailWord_2198937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198937).length < 2 ^ (prefixWord ++ tailWord_2198937).sum := by decide
  have hdescent : baseEnd_2198937 < baseStart_2198937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198967 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 2, 4]
def baseStart_2198967 : Nat := 118140960795 + 2198967 * 2 ^ 59
def prefixEnd_2198967 : Nat := 4983230072969 + 3 ^ 40 * 2198967 * 2
def baseEnd_2198967 : Nat := 376375671458467755066547

theorem tailTrace_2198967 : CollatzResearch.WordTrace tailWord_2198967 prefixEnd_2198967 376375671458467755066547 := by
  unfold tailWord_2198967
  simp only [CollatzResearch.WordTrace]
  refine ⟨80202915424525587509355155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53468610283017058339570103 80202915424525587509355155)
  ·
    refine ⟨120304373136788381264032733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80202915424525587509355155 120304373136788381264032733)
    ·
      refine ⟨45114139926295642974012275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120304373136788381264032733 45114139926295642974012275)
      ·
        refine ⟨67671209889443464461018413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45114139926295642974012275 67671209889443464461018413)
        ·
          refine ⟨25376703708541299172881905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67671209889443464461018413 25376703708541299172881905)
          ·
            refine ⟨19032527781405974379661429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25376703708541299172881905 19032527781405974379661429)
            ·
              refine ⟨1784299479506810098093259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19032527781405974379661429 1784299479506810098093259)
              ·
                refine ⟨2676449219260215147139889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784299479506810098093259 2676449219260215147139889)
                ·
                  refine ⟨2007336914445161360354917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676449219260215147139889 2007336914445161360354917)
                  ·
                    refine ⟨376375671458467755066547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2007336914445161360354917 376375671458467755066547)
                    ·
                      rfl

theorem cell23_2198967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_2198967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198967 prefixEnd_2198967 := by exact prefixLift 2198967
  have htrace : WordTrace (prefixWord ++ tailWord_2198967) baseStart_2198967 baseEnd_2198967 := by
    simpa [prefixWord, tailWord_2198967, baseEnd_2198967] using wordTrace_append hprefix tailTrace_2198967
  have hstable : (prefixWord ++ tailWord_2198967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198967).length < 2 ^ (prefixWord ++ tailWord_2198967).sum := by decide
  have hdescent : baseEnd_2198967 < baseStart_2198967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198980 : List Nat := [2, 3, 3, 2, 1, 2, 1, 9]
def baseStart_2198980 : Nat := 118140960795 + 2198980 * 2 ^ 59
def prefixEnd_2198980 : Nat := 4983230072969 + 3 ^ 40 * 2198980 * 2
def baseEnd_2198980 : Nat := 41819766282367100531003

theorem tailTrace_2198980 : CollatzResearch.WordTrace tailWord_2198980 prefixEnd_2198980 41819766282367100531003 := by
  unfold tailWord_2198980
  simp only [CollatzResearch.WordTrace]
  refine ⟨40101694786739245364789197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53468926382318993819718929 40101694786739245364789197)
  ·
    refine ⟨15038135545027217011795949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40101694786739245364789197 15038135545027217011795949)
    ·
      refine ⟨5639300829385206379423481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15038135545027217011795949 5639300829385206379423481)
      ·
        refine ⟨4229475622038904784567611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5639300829385206379423481 4229475622038904784567611)
        ·
          refine ⟨6344213433058357176851417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4229475622038904784567611 6344213433058357176851417)
          ·
            refine ⟨4758160074793767882638563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6344213433058357176851417 4758160074793767882638563)
            ·
              refine ⟨7137240112190651823957845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758160074793767882638563 7137240112190651823957845)
              ·
                refine ⟨41819766282367100531003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7137240112190651823957845 41819766282367100531003)
                ·
                  rfl

theorem cell23_2198980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 9].length) (baseStart_2198980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198980 prefixEnd_2198980 := by exact prefixLift 2198980
  have htrace : WordTrace (prefixWord ++ tailWord_2198980) baseStart_2198980 baseEnd_2198980 := by
    simpa [prefixWord, tailWord_2198980, baseEnd_2198980] using wordTrace_append hprefix tailTrace_2198980
  have hstable : (prefixWord ++ tailWord_2198980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198980).length < 2 ^ (prefixWord ++ tailWord_2198980).sum := by decide
  have hdescent : baseEnd_2198980 < baseStart_2198980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2198990 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_2198990 : Nat := 118140960795 + 2198990 * 2 ^ 59
def prefixEnd_2198990 : Nat := 4983230072969 + 3 ^ 40 * 2198990 * 2
def baseEnd_2198990 : Nat := 1129138824430456675212035

theorem tailTrace_2198990 : CollatzResearch.WordTrace tailWord_2198990 prefixEnd_2198990 1129138824430456675212035 := by
  unfold tailWord_2198990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10025469287930282804680303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53469169535628174958294949 10025469287930282804680303)
  ·
    refine ⟨15038203931895424207020455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10025469287930282804680303 15038203931895424207020455)
    ·
      refine ⟨22557305897843136310530683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15038203931895424207020455 22557305897843136310530683)
      ·
        refine ⟨33835958846764704465796025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22557305897843136310530683 33835958846764704465796025)
        ·
          refine ⟨25376969135073528349347019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33835958846764704465796025 25376969135073528349347019)
          ·
            refine ⟨38065453702610292524020529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25376969135073528349347019 38065453702610292524020529)
            ·
              refine ⟨28549090276957719393015397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38065453702610292524020529 28549090276957719393015397)
              ·
                refine ⟨5352954426929572386190387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28549090276957719393015397 5352954426929572386190387)
                ·
                  refine ⟨8029431640394358579285581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5352954426929572386190387 8029431640394358579285581)
                  ·
                    refine ⟨3011036865147884467232093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8029431640394358579285581 3011036865147884467232093)
                    ·
                      refine ⟨1129138824430456675212035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3011036865147884467232093 1129138824430456675212035)
                      ·
                        rfl

theorem cell23_2198990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_2198990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2198990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2198990 prefixEnd_2198990 := by exact prefixLift 2198990
  have htrace : WordTrace (prefixWord ++ tailWord_2198990) baseStart_2198990 baseEnd_2198990 := by
    simpa [prefixWord, tailWord_2198990, baseEnd_2198990] using wordTrace_append hprefix tailTrace_2198990
  have hstable : (prefixWord ++ tailWord_2198990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2198990).length < 2 ^ (prefixWord ++ tailWord_2198990).sum := by decide
  have hdescent : baseEnd_2198990 < baseStart_2198990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2198990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199007 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 3]
def baseStart_2199007 : Nat := 118140960795 + 2199007 * 2 ^ 59
def prefixEnd_2199007 : Nat := 4983230072969 + 3 ^ 40 * 2199007 * 2
def baseEnd_2199007 : Nat := 1129147553601583108699457

theorem tailTrace_2199007 : CollatzResearch.WordTrace tailWord_2199007 prefixEnd_2199007 1129147553601583108699457 := by
  unfold tailWord_2199007
  simp only [CollatzResearch.WordTrace]
  refine ⟨80204374344380674340811275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53469582896253782893874183 80204374344380674340811275)
  ·
    refine ⟨120306561516571011511216913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80204374344380674340811275 120306561516571011511216913)
    ·
      refine ⟨90229921137428258633412685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120306561516571011511216913 90229921137428258633412685)
      ·
        refine ⟨33836220426535596987529757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90229921137428258633412685 33836220426535596987529757)
        ·
          refine ⟨12688582659950848870323659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33836220426535596987529757 12688582659950848870323659)
          ·
            refine ⟨19032873989926273305485489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12688582659950848870323659 19032873989926273305485489)
            ·
              refine ⟨14274655492444704979114117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19032873989926273305485489 14274655492444704979114117)
              ·
                refine ⟨2676497904833382183583897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14274655492444704979114117 2676497904833382183583897)
                ·
                  refine ⟨2007373428625036637687923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676497904833382183583897 2007373428625036637687923)
                  ·
                    refine ⟨3011060142937554956531885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2007373428625036637687923 3011060142937554956531885)
                    ·
                      refine ⟨1129147553601583108699457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3011060142937554956531885 1129147553601583108699457)
                      ·
                        rfl

theorem cell23_2199007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_2199007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199007 prefixEnd_2199007 := by exact prefixLift 2199007
  have htrace : WordTrace (prefixWord ++ tailWord_2199007) baseStart_2199007 baseEnd_2199007 := by
    simpa [prefixWord, tailWord_2199007, baseEnd_2199007] using wordTrace_append hprefix tailTrace_2199007
  have hstable : (prefixWord ++ tailWord_2199007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199007).length < 2 ^ (prefixWord ++ tailWord_2199007).sum := by decide
  have hdescent : baseEnd_2199007 < baseStart_2199007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199023 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 2, 6]
def baseStart_2199023 : Nat := 118140960795 + 2199023 * 2 ^ 59
def prefixEnd_2199023 : Nat := 4983230072969 + 3 ^ 40 * 2199023 * 2
def baseEnd_2199023 : Nat := 376385256430685015366461

theorem tailTrace_2199023 : CollatzResearch.WordTrace tailWord_2199023 prefixEnd_2199023 376385256430685015366461 := by
  unfold tailWord_2199023
  simp only [CollatzResearch.WordTrace]
  refine ⟨80204957912322709073393723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53469971941548472715595815 80204957912322709073393723)
  ·
    refine ⟨120307436868484063610090585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80204957912322709073393723 120307436868484063610090585)
    ·
      refine ⟨90230577651363047707567939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120307436868484063610090585 90230577651363047707567939)
      ·
        refine ⟨135345866477044571561351909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90230577651363047707567939 135345866477044571561351909)
        ·
          refine ⟨25377349964445857167753483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135345866477044571561351909 25377349964445857167753483)
          ·
            refine ⟨38066024946668785751630225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25377349964445857167753483 38066024946668785751630225)
            ·
              refine ⟨28549518710001589313722669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38066024946668785751630225 28549518710001589313722669)
              ·
                refine ⟨10706069516250595992646001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28549518710001589313722669 10706069516250595992646001)
                ·
                  refine ⟨8029552137187946994484501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10706069516250595992646001 8029552137187946994484501)
                  ·
                    refine ⟨376385256430685015366461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8029552137187946994484501 376385256430685015366461)
                    ·
                      rfl

theorem cell23_2199023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_2199023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199023 prefixEnd_2199023 := by exact prefixLift 2199023
  have htrace : WordTrace (prefixWord ++ tailWord_2199023) baseStart_2199023 baseEnd_2199023 := by
    simpa [prefixWord, tailWord_2199023, baseEnd_2199023] using wordTrace_append hprefix tailTrace_2199023
  have hstable : (prefixWord ++ tailWord_2199023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199023).length < 2 ^ (prefixWord ++ tailWord_2199023).sum := by decide
  have hdescent : baseEnd_2199023 < baseStart_2199023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199024 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 2, 1, 3]
def baseStart_2199024 : Nat := 118140960795 + 2199024 * 2 ^ 59
def prefixEnd_2199024 : Nat := 4983230072969 + 3 ^ 40 * 2199024 * 2
def baseEnd_2199024 : Nat := 1129156282772709542186879

theorem tailTrace_2199024 : CollatzResearch.WordTrace tailWord_2199024 prefixEnd_2199024 1129156282772709542186879 := by
  unfold tailWord_2199024
  simp only [CollatzResearch.WordTrace]
  refine ⟨40102497192659543122090063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53469996256879390829453417 40102497192659543122090063)
  ·
    refine ⟨60153745788989314683135095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40102497192659543122090063 60153745788989314683135095)
    ·
      refine ⟨90230618683483972024702643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60153745788989314683135095 90230618683483972024702643)
      ·
        refine ⟨135345928025225958037053965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90230618683483972024702643 135345928025225958037053965)
        ·
          refine ⟨50754723009459734263895237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135345928025225958037053965 50754723009459734263895237)
          ·
            refine ⟨9516510564273700174480357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50754723009459734263895237 9516510564273700174480357)
            ·
              refine ⟨1784345730801318782715067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9516510564273700174480357 1784345730801318782715067)
              ·
                refine ⟨2676518596201978174072601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784345730801318782715067 2676518596201978174072601)
                ·
                  refine ⟨2007388947151483630554451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676518596201978174072601 2007388947151483630554451)
                  ·
                    refine ⟨3011083420727225445831677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2007388947151483630554451 3011083420727225445831677)
                    ·
                      refine ⟨1129156282772709542186879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3011083420727225445831677 1129156282772709542186879)
                      ·
                        rfl

theorem cell23_2199024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 1, 3].length) (baseStart_2199024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199024 prefixEnd_2199024 := by exact prefixLift 2199024
  have htrace : WordTrace (prefixWord ++ tailWord_2199024) baseStart_2199024 baseEnd_2199024 := by
    simpa [prefixWord, tailWord_2199024, baseEnd_2199024] using wordTrace_append hprefix tailTrace_2199024
  have hstable : (prefixWord ++ tailWord_2199024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199024).length < 2 ^ (prefixWord ++ tailWord_2199024).sum := by decide
  have hdescent : baseEnd_2199024 < baseStart_2199024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199043 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4]
def baseStart_2199043 : Nat := 118140960795 + 2199043 * 2 ^ 59
def prefixEnd_2199043 : Nat := 4983230072969 + 3 ^ 40 * 2199043 * 2
def baseEnd_2199043 : Nat := 1129166038905144967849291

theorem tailTrace_2199043 : CollatzResearch.WordTrace tailWord_2199043 prefixEnd_2199043 1129166038905144967849291 := by
  unfold tailWord_2199043
  simp only [CollatzResearch.WordTrace]
  refine ⟨80205687372250252489121783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53470458248166834992747855 80205687372250252489121783)
  ·
    refine ⟨120308531058375378733682675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80205687372250252489121783 120308531058375378733682675)
    ·
      refine ⟨180462796587563068100524013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120308531058375378733682675 180462796587563068100524013)
      ·
        refine ⟨67673548720336150537696505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 180462796587563068100524013 67673548720336150537696505)
        ·
          refine ⟨50755161540252112903272379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67673548720336150537696505 50755161540252112903272379)
          ·
            refine ⟨76132742310378169354908569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50755161540252112903272379 76132742310378169354908569)
            ·
              refine ⟨57099556732783627016181427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76132742310378169354908569 57099556732783627016181427)
              ·
                refine ⟨85649335099175440524272141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57099556732783627016181427 85649335099175440524272141)
                ·
                  refine ⟨32118500662190790196602053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85649335099175440524272141 32118500662190790196602053)
                  ·
                    refine ⟨6022218874160773161862885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32118500662190790196602053 6022218874160773161862885)
                    ·
                      refine ⟨1129166038905144967849291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6022218874160773161862885 1129166038905144967849291)
                      ·
                        rfl

theorem cell23_2199043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_2199043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199043 prefixEnd_2199043 := by exact prefixLift 2199043
  have htrace : WordTrace (prefixWord ++ tailWord_2199043) baseStart_2199043 baseEnd_2199043 := by
    simpa [prefixWord, tailWord_2199043, baseEnd_2199043] using wordTrace_append hprefix tailTrace_2199043
  have hstable : (prefixWord ++ tailWord_2199043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199043).length < 2 ^ (prefixWord ++ tailWord_2199043).sum := by decide
  have hdescent : baseEnd_2199043 < baseStart_2199043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199047 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 3, 4, 2]
def baseStart_2199047 : Nat := 118140960795 + 2199047 * 2 ^ 59
def prefixEnd_2199047 : Nat := 4983230072969 + 3 ^ 40 * 2199047 * 2
def baseEnd_2199047 : Nat := 1129168092827762952199273

theorem tailTrace_2199047 : CollatzResearch.WordTrace tailWord_2199047 prefixEnd_2199047 1129168092827762952199273 := by
  unfold tailWord_2199047
  simp only [CollatzResearch.WordTrace]
  refine ⟨80205833264235761172267395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53470555509490507448178263 80205833264235761172267395)
  ·
    refine ⟨120308749896353641758401093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80205833264235761172267395 120308749896353641758401093)
    ·
      refine ⟨22557890605566307829700205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120308749896353641758401093 22557890605566307829700205)
      ·
        refine ⟨8459208977087365436137577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22557890605566307829700205 8459208977087365436137577)
        ·
          refine ⟨6344406732815524077103183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8459208977087365436137577 6344406732815524077103183)
          ·
            refine ⟨9516610099223286115654775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6344406732815524077103183 9516610099223286115654775)
            ·
              refine ⟨14274915148834929173482163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9516610099223286115654775 14274915148834929173482163)
              ·
                refine ⟨21412372723252393760223245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14274915148834929173482163 21412372723252393760223245)
                ·
                  refine ⟨8029639771219647660083717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21412372723252393760223245 8029639771219647660083717)
                  ·
                    refine ⟨1505557457103683936265697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8029639771219647660083717 1505557457103683936265697)
                    ·
                      refine ⟨1129168092827762952199273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505557457103683936265697 1129168092827762952199273)
                      ·
                        rfl

theorem cell23_2199047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_2199047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199047 prefixEnd_2199047 := by exact prefixLift 2199047
  have htrace : WordTrace (prefixWord ++ tailWord_2199047) baseStart_2199047 baseEnd_2199047 := by
    simpa [prefixWord, tailWord_2199047, baseEnd_2199047] using wordTrace_append hprefix tailTrace_2199047
  have hstable : (prefixWord ++ tailWord_2199047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199047).length < 2 ^ (prefixWord ++ tailWord_2199047).sum := by decide
  have hdescent : baseEnd_2199047 < baseStart_2199047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199050 : List Nat := [3, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_2199050 : Nat := 118140960795 + 2199050 * 2 ^ 59
def prefixEnd_2199050 : Nat := 4983230072969 + 3 ^ 40 * 2199050 * 2
def baseEnd_2199050 : Nat := 1129169633269726440461759

theorem tailTrace_2199050 : CollatzResearch.WordTrace tailWord_2199050 prefixEnd_2199050 1129169633269726440461759 := by
  unfold tailWord_2199050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20051485670806223171156651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53470628455483261789751069 20051485670806223171156651)
  ·
    refine ⟨30077228506209334756734977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20051485670806223171156651 30077228506209334756734977)
    ·
      refine ⟨22557921379657001067551233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30077228506209334756734977 22557921379657001067551233)
      ·
        refine ⟨16918441034742750800663425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22557921379657001067551233 16918441034742750800663425)
        ·
          refine ⟨12688830776057063100497569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16918441034742750800663425 12688830776057063100497569)
          ·
            refine ⟨9516623082042797325373177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12688830776057063100497569 9516623082042797325373177)
            ·
              refine ⟨7137467311532097994029883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9516623082042797325373177 7137467311532097994029883)
              ·
                refine ⟨10706200967298146991044825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7137467311532097994029883 10706200967298146991044825)
                ·
                  refine ⟨8029650725473610243283619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10706200967298146991044825 8029650725473610243283619)
                  ·
                    refine ⟨12044476088210415364925429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8029650725473610243283619 12044476088210415364925429)
                    ·
                      refine ⟨1129169633269726440461759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12044476088210415364925429 1129169633269726440461759)
                      ·
                        rfl

theorem cell23_2199050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_2199050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199050 prefixEnd_2199050 := by exact prefixLift 2199050
  have htrace : WordTrace (prefixWord ++ tailWord_2199050) baseStart_2199050 baseEnd_2199050 := by
    simpa [prefixWord, tailWord_2199050, baseEnd_2199050] using wordTrace_append hprefix tailTrace_2199050
  have hstable : (prefixWord ++ tailWord_2199050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199050).length < 2 ^ (prefixWord ++ tailWord_2199050).sum := by decide
  have hdescent : baseEnd_2199050 < baseStart_2199050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199051 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 1, 3, 2]
def baseStart_2199051 : Nat := 118140960795 + 2199051 * 2 ^ 59
def prefixEnd_2199051 : Nat := 4983230072969 + 3 ^ 40 * 2199051 * 2
def baseEnd_2199051 : Nat := 1129170146750380936549255

theorem tailTrace_2199051 : CollatzResearch.WordTrace tailWord_2199051 prefixEnd_2199051 1129170146750380936549255 := by
  unfold tailWord_2199051
  simp only [CollatzResearch.WordTrace]
  refine ⟨80205979156221269855413007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53470652770814179903608671 80205979156221269855413007)
  ·
    refine ⟨120308968734331904783119511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80205979156221269855413007 120308968734331904783119511)
    ·
      refine ⟨180463453101497857174679267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120308968734331904783119511 180463453101497857174679267)
      ·
        refine ⟨270695179652246785762018901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180463453101497857174679267 270695179652246785762018901)
        ·
          refine ⟨3172209136549767020648659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 270695179652246785762018901 3172209136549767020648659)
          ·
            refine ⟨4758313704824650530972989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3172209136549767020648659 4758313704824650530972989)
            ·
              refine ⟨1784367639309243949114871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4758313704824650530972989 1784367639309243949114871)
              ·
                refine ⟨2676551458963865923672307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784367639309243949114871 2676551458963865923672307)
                ·
                  refine ⟨4014827188445798885508461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676551458963865923672307 4014827188445798885508461)
                  ·
                    refine ⟨1505560195667174582065673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4014827188445798885508461 1505560195667174582065673)
                    ·
                      refine ⟨1129170146750380936549255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505560195667174582065673 1129170146750380936549255)
                      ·
                        rfl

theorem cell23_2199051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 3, 2].length) (baseStart_2199051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199051 prefixEnd_2199051 := by exact prefixLift 2199051
  have htrace : WordTrace (prefixWord ++ tailWord_2199051) baseStart_2199051 baseEnd_2199051 := by
    simpa [prefixWord, tailWord_2199051, baseEnd_2199051] using wordTrace_append hprefix tailTrace_2199051
  have hstable : (prefixWord ++ tailWord_2199051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199051).length < 2 ^ (prefixWord ++ tailWord_2199051).sum := by decide
  have hdescent : baseEnd_2199051 < baseStart_2199051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199113 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 10]
def baseStart_2199113 : Nat := 118140960795 + 2199113 * 2 ^ 59
def prefixEnd_2199113 : Nat := 4983230072969 + 3 ^ 40 * 2199113 * 2
def baseEnd_2199113 : Nat := 376400660850319897991323

theorem tailTrace_2199113 : CollatzResearch.WordTrace tailWord_2199113 prefixEnd_2199113 376400660850319897991323 := by
  unfold tailWord_2199113
  simp only [CollatzResearch.WordTrace]
  refine ⟨80208240481996654444169993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53472160321331102962779995 80208240481996654444169993)
  ·
    refine ⟨60156180361497490833127495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80208240481996654444169993 60156180361497490833127495)
    ·
      refine ⟨90234270542246236249691243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60156180361497490833127495 90234270542246236249691243)
      ·
        refine ⟨135351405813369354374536865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90234270542246236249691243 135351405813369354374536865)
        ·
          refine ⟨101513554360027015780902649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135351405813369354374536865 101513554360027015780902649)
          ·
            refine ⟨76135165770020261835676987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101513554360027015780902649 76135165770020261835676987)
            ·
              refine ⟨114202748655030392753515481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76135165770020261835676987 114202748655030392753515481)
              ·
                refine ⟨85652061491272794565136611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114202748655030392753515481 85652061491272794565136611)
                ·
                  refine ⟨128478092236909191847704917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85652061491272794565136611 128478092236909191847704917)
                  ·
                    refine ⟨376400660850319897991323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 128478092236909191847704917 376400660850319897991323)
                    ·
                      rfl

theorem cell23_2199113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 10].length) (baseStart_2199113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199113 prefixEnd_2199113 := by exact prefixLift 2199113
  have htrace : WordTrace (prefixWord ++ tailWord_2199113) baseStart_2199113 baseEnd_2199113 := by
    simpa [prefixWord, tailWord_2199113, baseEnd_2199113] using wordTrace_append hprefix tailTrace_2199113
  have hstable : (prefixWord ++ tailWord_2199113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199113).length < 2 ^ (prefixWord ++ tailWord_2199113).sum := by decide
  have hdescent : baseEnd_2199113 < baseStart_2199113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199120 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4]
def baseStart_2199120 : Nat := 118140960795 + 2199120 * 2 ^ 59
def prefixEnd_2199120 : Nat := 4983230072969 + 3 ^ 40 * 2199120 * 2
def baseEnd_2199120 : Nat := 1129205576915541166586437

theorem tailTrace_2199120 : CollatzResearch.WordTrace tailWord_2199120 prefixEnd_2199120 1129205576915541166586437 := by
  unfold tailWord_2199120
  simp only [CollatzResearch.WordTrace]
  refine ⟨40104247896485647319837407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53472330528647529759783209 40104247896485647319837407)
  ·
    refine ⟨60156371844728470979756111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40104247896485647319837407 60156371844728470979756111)
    ·
      refine ⟨90234557767092706469634167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60156371844728470979756111 90234557767092706469634167)
      ·
        refine ⟨135351836650639059704451251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90234557767092706469634167 135351836650639059704451251)
        ·
          refine ⟨203027754975958589556676877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135351836650639059704451251 203027754975958589556676877)
          ·
            refine ⟨76135408115984471083753829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203027754975958589556676877 76135408115984471083753829)
            ·
              refine ⟨14275389021747088328203843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76135408115984471083753829 14275389021747088328203843)
              ·
                refine ⟨21413083532620632492305765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14275389021747088328203843 21413083532620632492305765)
                ·
                  refine ⟨4014953162366368592307331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21413083532620632492305765 4014953162366368592307331)
                  ·
                    refine ⟨6022429743549552888460997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4014953162366368592307331 6022429743549552888460997)
                    ·
                      refine ⟨1129205576915541166586437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6022429743549552888460997 1129205576915541166586437)
                      ·
                        rfl

theorem cell23_2199120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 1, 4].length) (baseStart_2199120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199120 prefixEnd_2199120 := by exact prefixLift 2199120
  have htrace : WordTrace (prefixWord ++ tailWord_2199120) baseStart_2199120 baseEnd_2199120 := by
    simpa [prefixWord, tailWord_2199120, baseEnd_2199120] using wordTrace_append hprefix tailTrace_2199120
  have hstable : (prefixWord ++ tailWord_2199120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199120).length < 2 ^ (prefixWord ++ tailWord_2199120).sum := by decide
  have hdescent : baseEnd_2199120 < baseStart_2199120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199137 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_2199137 : Nat := 118140960795 + 2199137 * 2 ^ 59
def prefixEnd_2199137 : Nat := 4983230072969 + 3 ^ 40 * 2199137 * 2
def baseEnd_2199137 : Nat := 1129214306086667600073859

theorem tailTrace_2199137 : CollatzResearch.WordTrace tailWord_2199137 prefixEnd_2199137 1129214306086667600073859 := by
  unfold tailWord_2199137
  simp only [CollatzResearch.WordTrace]
  refine ⟨80209115833909706543043665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53472743889273137695362443 80209115833909706543043665)
  ·
    refine ⟨60156836875432279907282749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80209115833909706543043665 60156836875432279907282749)
    ·
      refine ⟨22558813828287104965231031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60156836875432279907282749 22558813828287104965231031)
      ·
        refine ⟨33838220742430657447846547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22558813828287104965231031 33838220742430657447846547)
        ·
          refine ⟨50757331113645986171769821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33838220742430657447846547 50757331113645986171769821)
          ·
            refine ⟨19033999167617244814413683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50757331113645986171769821 19033999167617244814413683)
            ·
              refine ⟨28550998751425867221620525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19033999167617244814413683 28550998751425867221620525)
              ·
                refine ⟨10706624531784700208107697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28550998751425867221620525 10706624531784700208107697)
                ·
                  refine ⟨8029968398838525156080773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10706624531784700208107697 8029968398838525156080773)
                  ·
                    refine ⟨1505619074782223466765145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8029968398838525156080773 1505619074782223466765145)
                    ·
                      refine ⟨1129214306086667600073859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505619074782223466765145 1129214306086667600073859)
                      ·
                        rfl

theorem cell23_2199137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_2199137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199137 prefixEnd_2199137 := by exact prefixLift 2199137
  have htrace : WordTrace (prefixWord ++ tailWord_2199137) baseStart_2199137 baseEnd_2199137 := by
    simpa [prefixWord, tailWord_2199137, baseEnd_2199137] using wordTrace_append hprefix tailTrace_2199137
  have hstable : (prefixWord ++ tailWord_2199137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199137).length < 2 ^ (prefixWord ++ tailWord_2199137).sum := by decide
  have hdescent : baseEnd_2199137 < baseStart_2199137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199227 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 4]
def baseStart_2199227 : Nat := 118140960795 + 2199227 * 2 ^ 59
def prefixEnd_2199227 : Nat := 4983230072969 + 3 ^ 40 * 2199227 * 2
def baseEnd_2199227 : Nat := 1129260519345572247948445

theorem tailTrace_2199227 : CollatzResearch.WordTrace tailWord_2199227 prefixEnd_2199227 1129260519345572247948445 := by
  unfold tailWord_2199227
  simp only [CollatzResearch.WordTrace]
  refine ⟨80212398403583651913819935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53474932269055767942546623 80212398403583651913819935)
  ·
    refine ⟨120318597605375477870729903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80212398403583651913819935 120318597605375477870729903)
    ·
      refine ⟨180477896408063216806094855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120318597605375477870729903 180477896408063216806094855)
      ·
        refine ⟨270716844612094825209142283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180477896408063216806094855 270716844612094825209142283)
        ·
          refine ⟨406075266918142237813713425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270716844612094825209142283 406075266918142237813713425)
          ·
            refine ⟨304556450188606678360285069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406075266918142237813713425 304556450188606678360285069)
            ·
              refine ⟨114208668820727504385106901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 304556450188606678360285069 114208668820727504385106901)
              ·
                refine ⟨2676765675485800884025943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114208668820727504385106901 2676765675485800884025943)
                ·
                  refine ⟨4015148513228701326038915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676765675485800884025943 4015148513228701326038915)
                  ·
                    refine ⟨6022722769843051989058373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4015148513228701326038915 6022722769843051989058373)
                    ·
                      refine ⟨1129260519345572247948445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6022722769843051989058373 1129260519345572247948445)
                      ·
                        rfl

theorem cell23_2199227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 1, 4].length) (baseStart_2199227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199227 prefixEnd_2199227 := by exact prefixLift 2199227
  have htrace : WordTrace (prefixWord ++ tailWord_2199227) baseStart_2199227 baseEnd_2199227 := by
    simpa [prefixWord, tailWord_2199227, baseEnd_2199227] using wordTrace_append hprefix tailTrace_2199227
  have hstable : (prefixWord ++ tailWord_2199227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199227).length < 2 ^ (prefixWord ++ tailWord_2199227).sum := by decide
  have hdescent : baseEnd_2199227 < baseStart_2199227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199257 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 4]
def baseStart_2199257 : Nat := 118140960795 + 2199257 * 2 ^ 59
def prefixEnd_2199257 : Nat := 4983230072969 + 3 ^ 40 * 2199257 * 2
def baseEnd_2199257 : Nat := 1129275923765207130573307

theorem tailTrace_2199257 : CollatzResearch.WordTrace tailWord_2199257 prefixEnd_2199257 1129275923765207130573307 := by
  unfold tailWord_2199257
  simp only [CollatzResearch.WordTrace]
  refine ⟨80213492593474967037412025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53475661728983311358274683 80213492593474967037412025)
  ·
    refine ⟨60160119445106225278059019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80213492593474967037412025 60160119445106225278059019)
    ·
      refine ⟨90240179167659337917088529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60160119445106225278059019 90240179167659337917088529)
      ·
        refine ⟨67680134375744503437816397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90240179167659337917088529 67680134375744503437816397)
        ·
          refine ⟨25380050390904188789181149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67680134375744503437816397 25380050390904188789181149)
          ·
            refine ⟨9517518896589070795942931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25380050390904188789181149 9517518896589070795942931)
            ·
              refine ⟨14276278344883606193914397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9517518896589070795942931 14276278344883606193914397)
              ·
                refine ⟨5353604379331352322717899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14276278344883606193914397 5353604379331352322717899)
                ·
                  refine ⟨8030406568997028484076849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5353604379331352322717899 8030406568997028484076849)
                  ·
                    refine ⟨6022804926747771363057637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8030406568997028484076849 6022804926747771363057637)
                    ·
                      refine ⟨1129275923765207130573307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6022804926747771363057637 1129275923765207130573307)
                      ·
                        rfl

theorem cell23_2199257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_2199257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199257 prefixEnd_2199257 := by exact prefixLift 2199257
  have htrace : WordTrace (prefixWord ++ tailWord_2199257) baseStart_2199257 baseEnd_2199257 := by
    simpa [prefixWord, tailWord_2199257, baseEnd_2199257] using wordTrace_append hprefix tailTrace_2199257
  have hstable : (prefixWord ++ tailWord_2199257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199257).length < 2 ^ (prefixWord ++ tailWord_2199257).sum := by decide
  have hdescent : baseEnd_2199257 < baseStart_2199257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199280 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 9]
def baseStart_2199280 : Nat := 118140960795 + 2199280 * 2 ^ 59
def prefixEnd_2199280 : Nat := 4983230072969 + 3 ^ 40 * 2199280 * 2
def baseEnd_2199280 : Nat := 376429244606753513528567

theorem tailTrace_2199280 : CollatzResearch.WordTrace tailWord_2199280 prefixEnd_2199280 376429244606753513528567 := by
  unfold tailWord_2199280
  simp only [CollatzResearch.WordTrace]
  refine ⟨40107165736195820982749647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53476220981594427976999529 40107165736195820982749647)
  ·
    refine ⟨60160748604293731474124471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40107165736195820982749647 60160748604293731474124471)
    ·
      refine ⟨90241122906440597211186707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60160748604293731474124471 90241122906440597211186707)
      ·
        refine ⟨135361684359660895816780061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90241122906440597211186707 135361684359660895816780061)
        ·
          refine ⟨50760631634872835931292523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135361684359660895816780061 50760631634872835931292523)
          ·
            refine ⟨76140947452309253896938785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50760631634872835931292523 76140947452309253896938785)
            ·
              refine ⟨57105710589231940422704089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76140947452309253896938785 57105710589231940422704089)
              ·
                refine ⟨42829282941923955317028067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57105710589231940422704089 42829282941923955317028067)
                ·
                  refine ⟨64243924412885932975542101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42829282941923955317028067 64243924412885932975542101)
                  ·
                    refine ⟨376429244606753513528567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 64243924412885932975542101 376429244606753513528567)
                    ·
                      rfl

theorem cell23_2199280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 9].length) (baseStart_2199280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199280 prefixEnd_2199280 := by exact prefixLift 2199280
  have htrace : WordTrace (prefixWord ++ tailWord_2199280) baseStart_2199280 baseEnd_2199280 := by
    simpa [prefixWord, tailWord_2199280, baseEnd_2199280] using wordTrace_append hprefix tailTrace_2199280
  have hstable : (prefixWord ++ tailWord_2199280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199280).length < 2 ^ (prefixWord ++ tailWord_2199280).sum := by decide
  have hdescent : baseEnd_2199280 < baseStart_2199280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199281 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 1, 2, 3]
def baseStart_2199281 : Nat := 118140960795 + 2199281 * 2 ^ 59
def prefixEnd_2199281 : Nat := 4983230072969 + 3 ^ 40 * 2199281 * 2
def baseEnd_2199281 : Nat := 1129288247300915036673197

theorem tailTrace_2199281 : CollatzResearch.WordTrace tailWord_2199281 prefixEnd_2199281 1129288247300915036673197 := by
  unfold tailWord_2199281
  simp only [CollatzResearch.WordTrace]
  refine ⟨80214367945388019136285697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53476245296925346090857131 80214367945388019136285697)
  ·
    refine ⟨60160775959041014352214273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80214367945388019136285697 60160775959041014352214273)
    ·
      refine ⟨45120581969280760764160705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60160775959041014352214273 45120581969280760764160705)
      ·
        refine ⟨33840436476960570573120529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45120581969280760764160705 33840436476960570573120529)
        ·
          refine ⟨25380327357720427929840397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33840436476960570573120529 25380327357720427929840397)
          ·
            refine ⟨9517622759145160473690149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25380327357720427929840397 9517622759145160473690149)
            ·
              refine ⟨1784554267339717588816903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9517622759145160473690149 1784554267339717588816903)
              ·
                refine ⟨2676831401009576383225355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784554267339717588816903 2676831401009576383225355)
                ·
                  refine ⟨4015247101514364574838033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2676831401009576383225355 4015247101514364574838033)
                  ·
                    refine ⟨3011435326135773431128525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4015247101514364574838033 3011435326135773431128525)
                    ·
                      refine ⟨1129288247300915036673197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3011435326135773431128525 1129288247300915036673197)
                      ·
                        rfl

theorem cell23_2199281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 2, 3].length) (baseStart_2199281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199281 prefixEnd_2199281 := by exact prefixLift 2199281
  have htrace : WordTrace (prefixWord ++ tailWord_2199281) baseStart_2199281 baseEnd_2199281 := by
    simpa [prefixWord, tailWord_2199281, baseEnd_2199281] using wordTrace_append hprefix tailTrace_2199281
  have hstable : (prefixWord ++ tailWord_2199281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199281).length < 2 ^ (prefixWord ++ tailWord_2199281).sum := by decide
  have hdescent : baseEnd_2199281 < baseStart_2199281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199368 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_2199368 : Nat := 118140960795 + 2199368 * 2 ^ 59
def prefixEnd_2199368 : Nat := 4983230072969 + 3 ^ 40 * 2199368 * 2
def baseEnd_2199368 : Nat := 1129332920117856196285297

theorem tailTrace_2199368 : CollatzResearch.WordTrace tailWord_2199368 prefixEnd_2199368 1129332920117856196285297 := by
  unfold tailWord_2199368
  simp only [CollatzResearch.WordTrace]
  refine ⟨40108770548036416497351379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53478360730715221996468505 40108770548036416497351379)
  ·
    refine ⟨60163155822054624746027069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40108770548036416497351379 60163155822054624746027069)
    ·
      refine ⟨22561183433270484279760151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60163155822054624746027069 22561183433270484279760151)
      ·
        refine ⟨33841775149905726419640227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22561183433270484279760151 33841775149905726419640227)
        ·
          refine ⟨50762662724858589629460341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33841775149905726419640227 50762662724858589629460341)
          ·
            refine ⟨4758999630455492777761907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50762662724858589629460341 4758999630455492777761907)
            ·
              refine ⟨7138499445683239166642861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4758999630455492777761907 7138499445683239166642861)
              ·
                refine ⟨2676937292131214687491073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7138499445683239166642861 2676937292131214687491073)
                ·
                  refine ⟨2007702969098411015618305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676937292131214687491073 2007702969098411015618305)
                  ·
                    refine ⟨1505777226823808261713729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2007702969098411015618305 1505777226823808261713729)
                    ·
                      refine ⟨1129332920117856196285297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505777226823808261713729 1129332920117856196285297)
                      ·
                        rfl

theorem cell23_2199368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_2199368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199368 prefixEnd_2199368 := by exact prefixLift 2199368
  have htrace : WordTrace (prefixWord ++ tailWord_2199368) baseStart_2199368 baseEnd_2199368 := by
    simpa [prefixWord, tailWord_2199368, baseEnd_2199368] using wordTrace_append hprefix tailTrace_2199368
  have hstable : (prefixWord ++ tailWord_2199368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199368).length < 2 ^ (prefixWord ++ tailWord_2199368).sum := by decide
  have hdescent : baseEnd_2199368 < baseStart_2199368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199402 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2199402 : Nat := 118140960795 + 2199402 * 2 ^ 59
def prefixEnd_2199402 : Nat := 4983230072969 + 3 ^ 40 * 2199402 * 2
def baseEnd_2199402 : Nat := 1129350378460109063260141

theorem tailTrace_2199402 : CollatzResearch.WordTrace tailWord_2199402 prefixEnd_2199402 1129350378460109063260141 := by
  unfold tailWord_2199402
  simp only [CollatzResearch.WordTrace]
  refine ⟨20054695294487414200360115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53479187451966437867626973 20054695294487414200360115)
  ·
    refine ⟨30082042941731121300540173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20054695294487414200360115 30082042941731121300540173)
    ·
      refine ⟨11280766103149170487702565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30082042941731121300540173 11280766103149170487702565)
      ·
        refine ⟨2115143644340469466444231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11280766103149170487702565 2115143644340469466444231)
        ·
          refine ⟨3172715466510704199666347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2115143644340469466444231 3172715466510704199666347)
          ·
            refine ⟨4759073199766056299499521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3172715466510704199666347 4759073199766056299499521)
            ·
              refine ⟨3569304899824542224624641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759073199766056299499521 3569304899824542224624641)
              ·
                refine ⟨2676978674868406668468481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3569304899824542224624641 2676978674868406668468481)
                ·
                  refine ⟨2007734006151305001351361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2676978674868406668468481 2007734006151305001351361)
                  ·
                    refine ⟨1505800504613478751013521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2007734006151305001351361 1505800504613478751013521)
                    ·
                      refine ⟨1129350378460109063260141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505800504613478751013521 1129350378460109063260141)
                      ·
                        rfl

theorem cell23_2199402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2199402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199402 prefixEnd_2199402 := by exact prefixLift 2199402
  have htrace : WordTrace (prefixWord ++ tailWord_2199402) baseStart_2199402 baseEnd_2199402 := by
    simpa [prefixWord, tailWord_2199402, baseEnd_2199402] using wordTrace_append hprefix tailTrace_2199402
  have hstable : (prefixWord ++ tailWord_2199402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199402).length < 2 ^ (prefixWord ++ tailWord_2199402).sum := by decide
  have hdescent : baseEnd_2199402 < baseStart_2199402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199404 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_2199404 : Nat := 118140960795 + 2199404 * 2 ^ 59
def prefixEnd_2199404 : Nat := 4983230072969 + 3 ^ 40 * 2199404 * 2
def baseEnd_2199404 : Nat := 376450468473806018478377

theorem tailTrace_2199404 : CollatzResearch.WordTrace tailWord_2199404 prefixEnd_2199404 376450468473806018478377 := by
  unfold tailWord_2199404
  simp only [CollatzResearch.WordTrace]
  refine ⟨40109427061971205571506633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53479236082628274095342177 40109427061971205571506633)
  ·
    refine ⟨30082070296478404178629975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40109427061971205571506633 30082070296478404178629975)
    ·
      refine ⟨45123105444717606267944963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30082070296478404178629975 45123105444717606267944963)
      ·
        refine ⟨67684658167076409401917445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45123105444717606267944963 67684658167076409401917445)
        ·
          refine ⟨12690873406326826762859521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67684658167076409401917445 12690873406326826762859521)
          ·
            refine ⟨9518155054745120072144641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12690873406326826762859521 9518155054745120072144641)
            ·
              refine ⟨7138616291058840054108481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9518155054745120072144641 7138616291058840054108481)
              ·
                refine ⟨5353962218294130040581361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7138616291058840054108481 5353962218294130040581361)
                ·
                  refine ⟨4015471663720597530436021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5353962218294130040581361 4015471663720597530436021)
                  ·
                    refine ⟨376450468473806018478377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4015471663720597530436021 376450468473806018478377)
                    ·
                      rfl

theorem cell23_2199404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_2199404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199404 prefixEnd_2199404 := by exact prefixLift 2199404
  have htrace : WordTrace (prefixWord ++ tailWord_2199404) baseStart_2199404 baseEnd_2199404 := by
    simpa [prefixWord, tailWord_2199404, baseEnd_2199404] using wordTrace_append hprefix tailTrace_2199404
  have hstable : (prefixWord ++ tailWord_2199404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199404).length < 2 ^ (prefixWord ++ tailWord_2199404).sum := by decide
  have hdescent : baseEnd_2199404 < baseStart_2199404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199407 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 4]
def baseStart_2199407 : Nat := 118140960795 + 2199407 * 2 ^ 59
def prefixEnd_2199407 : Nat := 4983230072969 + 3 ^ 40 * 2199407 * 2
def baseEnd_2199407 : Nat := 1129352945863381543697617

theorem tailTrace_2199407 : CollatzResearch.WordTrace tailWord_2199407 prefixEnd_2199407 1129352945863381543697617 := by
  unfold tailWord_2199407
  simp only [CollatzResearch.WordTrace]
  refine ⟨80218963542931542655372475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53479309028621028436914983 80218963542931542655372475)
  ·
    refine ⟨120328445314397313983058713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80218963542931542655372475 120328445314397313983058713)
    ·
      refine ⟨90246333985797985487294035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120328445314397313983058713 90246333985797985487294035)
      ·
        refine ⟨135369500978696978230941053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90246333985797985487294035 135369500978696978230941053)
        ·
          refine ⟨50763562867011366836602895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135369500978696978230941053 50763562867011366836602895)
          ·
            refine ⟨76145344300517050254904343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50763562867011366836602895 76145344300517050254904343)
            ·
              refine ⟨114218016450775575382356515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76145344300517050254904343 114218016450775575382356515)
              ·
                refine ⟨171327024676163363073534773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114218016450775575382356515 171327024676163363073534773)
                ·
                  refine ⟨16061908563390315288143885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 171327024676163363073534773 16061908563390315288143885)
                  ·
                    refine ⟨6023215711271368233053957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16061908563390315288143885 6023215711271368233053957)
                    ·
                      refine ⟨1129352945863381543697617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6023215711271368233053957 1129352945863381543697617)
                      ·
                        rfl

theorem cell23_2199407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 3, 4].length) (baseStart_2199407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199407 prefixEnd_2199407 := by exact prefixLift 2199407
  have htrace : WordTrace (prefixWord ++ tailWord_2199407) baseStart_2199407 baseEnd_2199407 := by
    simpa [prefixWord, tailWord_2199407, baseEnd_2199407] using wordTrace_append hprefix tailTrace_2199407
  have hstable : (prefixWord ++ tailWord_2199407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199407).length < 2 ^ (prefixWord ++ tailWord_2199407).sum := by decide
  have hdescent : baseEnd_2199407 < baseStart_2199407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199481 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 6]
def baseStart_2199481 : Nat := 118140960795 + 2199481 * 2 ^ 59
def prefixEnd_2199481 : Nat := 4983230072969 + 3 ^ 40 * 2199481 * 2
def baseEnd_2199481 : Nat := 125487882603534917130253

theorem tailTrace_2199481 : CollatzResearch.WordTrace tailWord_2199481 prefixEnd_2199481 125487882603534917130253 := by
  unfold tailWord_2199481
  simp only [CollatzResearch.WordTrace]
  refine ⟨80221662544663453293566297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53481108363108968862377531 80221662544663453293566297)
  ·
    refine ⟨60166246908497589970174723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80221662544663453293566297 60166246908497589970174723)
    ·
      refine ⟨90249370362746384955262085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60166246908497589970174723 90249370362746384955262085)
      ·
        refine ⟨16921756943014947179111641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90249370362746384955262085 16921756943014947179111641)
        ·
          refine ⟨12691317707261210384333731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16921756943014947179111641 12691317707261210384333731)
          ·
            refine ⟨19036976560891815576500597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12691317707261210384333731 19036976560891815576500597)
            ·
              refine ⟨1784716552583607710296931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19036976560891815576500597 1784716552583607710296931)
              ·
                refine ⟨2677074828875411565445397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784716552583607710296931 2677074828875411565445397)
                ·
                  refine ⟨125487882603534917130253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2677074828875411565445397 125487882603534917130253)
                  ·
                    rfl

theorem cell23_2199481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 6].length) (baseStart_2199481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199481 prefixEnd_2199481 := by exact prefixLift 2199481
  have htrace : WordTrace (prefixWord ++ tailWord_2199481) baseStart_2199481 baseEnd_2199481 := by
    simpa [prefixWord, tailWord_2199481, baseEnd_2199481] using wordTrace_append hprefix tailTrace_2199481
  have hstable : (prefixWord ++ tailWord_2199481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199481).length < 2 ^ (prefixWord ++ tailWord_2199481).sum := by decide
  have hdescent : baseEnd_2199481 < baseStart_2199481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199544 : List Nat := [2, 1, 2, 1, 1, 3, 4, 1, 1, 1, 6]
def baseStart_2199544 : Nat := 118140960795 + 2199544 * 2 ^ 59
def prefixEnd_2199544 : Nat := 4983230072969 + 3 ^ 40 * 2199544 * 2
def baseEnd_2199544 : Nat := 1129423292713047507684487

theorem tailTrace_2199544 : CollatzResearch.WordTrace tailWord_2199544 prefixEnd_2199544 1129423292713047507684487 := by
  unfold tailWord_2199544
  simp only [CollatzResearch.WordTrace]
  refine ⟨40111980171717607526554843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53482640228956810035406457 40111980171717607526554843)
  ·
    refine ⟨60167970257576411289832265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40111980171717607526554843 60167970257576411289832265)
    ·
      refine ⟨45125977693182308467374199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60167970257576411289832265 45125977693182308467374199)
      ·
        refine ⟨67688966539773462701061299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45125977693182308467374199 67688966539773462701061299)
        ·
          refine ⟨101533449809660194051591949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67688966539773462701061299 101533449809660194051591949)
          ·
            refine ⟨38075043678622572769346981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101533449809660194051591949 38075043678622572769346981)
            ·
              refine ⟨7139070689741732394252559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38075043678622572769346981 7139070689741732394252559)
              ·
                refine ⟨10708606034612598591378839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139070689741732394252559 10708606034612598591378839)
                ·
                  refine ⟨16062909051918897887068259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10708606034612598591378839 16062909051918897887068259)
                  ·
                    refine ⟨24094363577878346830602389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16062909051918897887068259 24094363577878346830602389)
                    ·
                      refine ⟨1129423292713047507684487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24094363577878346830602389 1129423292713047507684487)
                      ·
                        rfl

theorem cell23_2199544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_2199544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199544 prefixEnd_2199544 := by exact prefixLift 2199544
  have htrace : WordTrace (prefixWord ++ tailWord_2199544) baseStart_2199544 baseEnd_2199544 := by
    simpa [prefixWord, tailWord_2199544, baseEnd_2199544] using wordTrace_append hprefix tailTrace_2199544
  have hstable : (prefixWord ++ tailWord_2199544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199544).length < 2 ^ (prefixWord ++ tailWord_2199544).sum := by decide
  have hdescent : baseEnd_2199544 < baseStart_2199544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199548 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 5, 2, 2]
def baseStart_2199548 : Nat := 118140960795 + 2199548 * 2 ^ 59
def prefixEnd_2199548 : Nat := 4983230072969 + 3 ^ 40 * 2199548 * 2
def baseEnd_2199548 : Nat := 1129425346635665492034469

theorem tailTrace_2199548 : CollatzResearch.WordTrace tailWord_2199548 prefixEnd_2199548 1129425346635665492034469 := by
  unfold tailWord_2199548
  simp only [CollatzResearch.WordTrace]
  refine ⟨40112053117710361868127649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53482737490280482490836865 40112053117710361868127649)
  ·
    refine ⟨30084039838282771401095737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40112053117710361868127649 30084039838282771401095737)
    ·
      refine ⟨22563029878712078550821803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30084039838282771401095737 22563029878712078550821803)
      ·
        refine ⟨33844544818068117826232705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22563029878712078550821803 33844544818068117826232705)
        ·
          refine ⟨25383408613551088369674529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33844544818068117826232705 25383408613551088369674529)
          ·
            refine ⟨19037556460163316277255897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25383408613551088369674529 19037556460163316277255897)
            ·
              refine ⟨14278167345122487207941923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19037556460163316277255897 14278167345122487207941923)
              ·
                refine ⟨21417251017683730811912885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14278167345122487207941923 21417251017683730811912885)
                ·
                  refine ⟨2007867282907849763616833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21417251017683730811912885 2007867282907849763616833)
                  ·
                    refine ⟨1505900462180887322712625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2007867282907849763616833 1505900462180887322712625)
                    ·
                      refine ⟨1129425346635665492034469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1505900462180887322712625 1129425346635665492034469)
                      ·
                        rfl

theorem cell23_2199548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_2199548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199548 prefixEnd_2199548 := by exact prefixLift 2199548
  have htrace : WordTrace (prefixWord ++ tailWord_2199548) baseStart_2199548 baseEnd_2199548 := by
    simpa [prefixWord, tailWord_2199548, baseEnd_2199548] using wordTrace_append hprefix tailTrace_2199548
  have hstable : (prefixWord ++ tailWord_2199548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199548).length < 2 ^ (prefixWord ++ tailWord_2199548).sum := by decide
  have hdescent : baseEnd_2199548 < baseStart_2199548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199575 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 2, 4]
def baseStart_2199575 : Nat := 118140960795 + 2199575 * 2 ^ 59
def prefixEnd_2199575 : Nat := 4983230072969 + 3 ^ 40 * 2199575 * 2
def baseEnd_2199575 : Nat := 376479736871112295465615

theorem tailTrace_2199575 : CollatzResearch.WordTrace tailWord_2199575 prefixEnd_2199575 376479736871112295465615 := by
  unfold tailWord_2199575
  simp only [CollatzResearch.WordTrace]
  refine ⟨80225091006322907347488179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53483394004215271564992119 80225091006322907347488179)
  ·
    refine ⟨120337636509484361021232269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80225091006322907347488179 120337636509484361021232269)
    ·
      refine ⟨45126613691056635382962101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120337636509484361021232269 45126613691056635382962101)
      ·
        refine ⟨4230620033536559567152697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45126613691056635382962101 4230620033536559567152697)
        ·
          refine ⟨3172965025152419675364523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230620033536559567152697 3172965025152419675364523)
          ·
            refine ⟨4759447537728629513046785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3172965025152419675364523 4759447537728629513046785)
            ·
              refine ⟨3569585653296472134785089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759447537728629513046785 3569585653296472134785089)
              ·
                refine ⟨2677189239972354101088817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3569585653296472134785089 2677189239972354101088817)
                ·
                  refine ⟨2007891929979265575816613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677189239972354101088817 2007891929979265575816613)
                  ·
                    refine ⟨376479736871112295465615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2007891929979265575816613 376479736871112295465615)
                    ·
                      rfl

theorem cell23_2199575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_2199575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199575 prefixEnd_2199575 := by exact prefixLift 2199575
  have htrace : WordTrace (prefixWord ++ tailWord_2199575) baseStart_2199575 baseEnd_2199575 := by
    simpa [prefixWord, tailWord_2199575, baseEnd_2199575] using wordTrace_append hprefix tailTrace_2199575
  have hstable : (prefixWord ++ tailWord_2199575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199575).length < 2 ^ (prefixWord ++ tailWord_2199575).sum := by decide
  have hdescent : baseEnd_2199575 < baseStart_2199575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199588 : List Nat := [2, 3, 1, 4, 2, 2, 1, 8]
def baseStart_2199588 : Nat := 118140960795 + 2199588 * 2 ^ 59
def prefixEnd_2199588 : Nat := 4983230072969 + 3 ^ 40 * 2199588 * 2
def baseEnd_2199588 : Nat := 41831329105994271686455

theorem tailTrace_2199588 : CollatzResearch.WordTrace tailWord_2199588 prefixEnd_2199588 41831329105994271686455 := by
  unfold tailWord_2199588
  simp only [CollatzResearch.WordTrace]
  refine ⟨40112782577637905283855709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53483710103517207045140945 40112782577637905283855709)
  ·
    refine ⟨15042293466614214481445891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40112782577637905283855709 15042293466614214481445891)
    ·
      refine ⟨22563440199921321722168837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15042293466614214481445891 22563440199921321722168837)
      ·
        refine ⟨4230645037485247822906657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22563440199921321722168837 4230645037485247822906657)
        ·
          refine ⟨3172983778113935867179993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230645037485247822906657 3172983778113935867179993)
          ·
            refine ⟨2379737833585451900384995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3172983778113935867179993 2379737833585451900384995)
            ·
              refine ⟨3569606750378177850577493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379737833585451900384995 3569606750378177850577493)
              ·
                refine ⟨41831329105994271686455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3569606750378177850577493 41831329105994271686455)
                ·
                  rfl

theorem cell23_2199588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 8].length) (baseStart_2199588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199588 prefixEnd_2199588 := by exact prefixLift 2199588
  have htrace : WordTrace (prefixWord ++ tailWord_2199588) baseStart_2199588 baseEnd_2199588 := by
    simpa [prefixWord, tailWord_2199588, baseEnd_2199588] using wordTrace_append hprefix tailTrace_2199588
  have hstable : (prefixWord ++ tailWord_2199588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199588).length < 2 ^ (prefixWord ++ tailWord_2199588).sum := by decide
  have hdescent : baseEnd_2199588 < baseStart_2199588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199598 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3]
def baseStart_2199598 : Nat := 118140960795 + 2199598 * 2 ^ 59
def prefixEnd_2199598 : Nat := 4983230072969 + 3 ^ 40 * 2199598 * 2
def baseEnd_2199598 : Nat := 1129451020668390296409239

theorem tailTrace_2199598 : CollatzResearch.WordTrace tailWord_2199598 prefixEnd_2199598 1129451020668390296409239 := by
  unfold tailWord_2199598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10028241235654947784446931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 53483953256826388183716965 10028241235654947784446931)
  ·
    refine ⟨15042361853482421676670397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10028241235654947784446931 15042361853482421676670397)
    ·
      refine ⟨5640885695055908128751399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15042361853482421676670397 5640885695055908128751399)
      ·
        refine ⟨8461328542583862193127099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5640885695055908128751399 8461328542583862193127099)
        ·
          refine ⟨12691992813875793289690649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8461328542583862193127099 12691992813875793289690649)
          ·
            refine ⟨9518994610406844967267987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12691992813875793289690649 9518994610406844967267987)
            ·
              refine ⟨14278491915610267450901981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9518994610406844967267987 14278491915610267450901981)
              ·
                refine ⟨5354434468353850294088243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14278491915610267450901981 5354434468353850294088243)
                ·
                  refine ⟨8031651702530775441132365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5354434468353850294088243 8031651702530775441132365)
                  ·
                    refine ⟨3011869388449040790424637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8031651702530775441132365 3011869388449040790424637)
                    ·
                      refine ⟨1129451020668390296409239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3011869388449040790424637 1129451020668390296409239)
                      ·
                        rfl

theorem cell23_2199598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_2199598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199598 prefixEnd_2199598 := by exact prefixLift 2199598
  have htrace : WordTrace (prefixWord ++ tailWord_2199598) baseStart_2199598 baseEnd_2199598 := by
    simpa [prefixWord, tailWord_2199598, baseEnd_2199598] using wordTrace_append hprefix tailTrace_2199598
  have hstable : (prefixWord ++ tailWord_2199598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199598).length < 2 ^ (prefixWord ++ tailWord_2199598).sum := by decide
  have hdescent : baseEnd_2199598 < baseStart_2199598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199651 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4]
def baseStart_2199651 : Nat := 118140960795 + 2199651 * 2 ^ 59
def prefixEnd_2199651 : Nat := 4983230072969 + 3 ^ 40 * 2199651 * 2
def baseEnd_2199651 : Nat := 1129478235143078589046495

theorem tailTrace_2199651 : CollatzResearch.WordTrace tailWord_2199651 prefixEnd_2199651 1129478235143078589046495 := by
  unfold tailWord_2199651
  simp only [CollatzResearch.WordTrace]
  refine ⟨80227862954047572327254807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53485241969365048218169871 80227862954047572327254807)
  ·
    refine ⟨120341794431071358490882211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80227862954047572327254807 120341794431071358490882211)
    ·
      refine ⟨180512691646607037736323317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120341794431071358490882211 180512691646607037736323317)
      ·
        refine ⟨16923064841869409787780311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 180512691646607037736323317 16923064841869409787780311)
        ·
          refine ⟨25384597262804114681670467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16923064841869409787780311 25384597262804114681670467)
          ·
            refine ⟨38076895894206172022505701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25384597262804114681670467 38076895894206172022505701)
            ·
              refine ⟨7139417980163657254219819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38076895894206172022505701 7139417980163657254219819)
              ·
                refine ⟨10709126970245485881329729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139417980163657254219819 10709126970245485881329729)
                ·
                  refine ⟨8031845227684114410997297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10709126970245485881329729 8031845227684114410997297)
                  ·
                    refine ⟨6023883920763085808247973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8031845227684114410997297 6023883920763085808247973)
                    ·
                      refine ⟨1129478235143078589046495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6023883920763085808247973 1129478235143078589046495)
                      ·
                        rfl

theorem cell23_2199651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_2199651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199651 prefixEnd_2199651 := by exact prefixLift 2199651
  have htrace : WordTrace (prefixWord ++ tailWord_2199651) baseStart_2199651 baseEnd_2199651 := by
    simpa [prefixWord, tailWord_2199651, baseEnd_2199651] using wordTrace_append hprefix tailTrace_2199651
  have hstable : (prefixWord ++ tailWord_2199651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199651).length < 2 ^ (prefixWord ++ tailWord_2199651).sum := by decide
  have hdescent : baseEnd_2199651 < baseStart_2199651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199661 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 7]
def baseStart_2199661 : Nat := 118140960795 + 2199661 * 2 ^ 59
def prefixEnd_2199661 : Nat := 4983230072969 + 3 ^ 40 * 2199661 * 2
def baseEnd_2199661 : Nat := 125498152216624838880161

theorem tailTrace_2199661 : CollatzResearch.WordTrace tailWord_2199661 prefixEnd_2199661 125498152216624838880161 := by
  unfold tailWord_2199661
  simp only [CollatzResearch.WordTrace]
  refine ⟨80228227684011344035118837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53485485122674229356745891 80228227684011344035118837)
  ·
    refine ⟨7521396345376063503292391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80228227684011344035118837 7521396345376063503292391)
    ·
      refine ⟨11282094518064095254938587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521396345376063503292391 11282094518064095254938587)
      ·
        refine ⟨16923141777096142882407881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11282094518064095254938587 16923141777096142882407881)
        ·
          refine ⟨12692356332822107161805911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16923141777096142882407881 12692356332822107161805911)
          ·
            refine ⟨19038534499233160742708867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12692356332822107161805911 19038534499233160742708867)
            ·
              refine ⟨28557801748849741114063301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19038534499233160742708867 28557801748849741114063301)
              ·
                refine ⟨5354587827909326458886869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28557801748849741114063301 5354587827909326458886869)
                ·
                  refine ⟨125498152216624838880161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5354587827909326458886869 125498152216624838880161)
                  ·
                    rfl

theorem cell23_2199661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_2199661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199661 prefixEnd_2199661 := by exact prefixLift 2199661
  have htrace : WordTrace (prefixWord ++ tailWord_2199661) baseStart_2199661 baseEnd_2199661 := by
    simpa [prefixWord, tailWord_2199661, baseEnd_2199661] using wordTrace_append hprefix tailTrace_2199661
  have hstable : (prefixWord ++ tailWord_2199661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199661).length < 2 ^ (prefixWord ++ tailWord_2199661).sum := by decide
  have hdescent : baseEnd_2199661 < baseStart_2199661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199701 : List Nat := [1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_2199701 : Nat := 118140960795 + 2199701 * 2 ^ 59
def prefixEnd_2199701 : Nat := 4983230072969 + 3 ^ 40 * 2199701 * 2
def baseEnd_2199701 : Nat := 1129503909175803393421265

theorem tailTrace_2199701 : CollatzResearch.WordTrace tailWord_2199701 prefixEnd_2199701 1129503909175803393421265 := by
  unfold tailWord_2199701
  simp only [CollatzResearch.WordTrace]
  refine ⟨80229686603866430866574957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53486457735910953911049971 80229686603866430866574957)
  ·
    refine ⟨30086132476449911574965609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80229686603866430866574957 30086132476449911574965609)
    ·
      refine ⟨22564599357337433681224207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30086132476449911574965609 22564599357337433681224207)
      ·
        refine ⟨33846899036006150521836311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22564599357337433681224207 33846899036006150521836311)
        ·
          refine ⟨50770348554009225782754467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33846899036006150521836311 50770348554009225782754467)
          ·
            refine ⟨76155522831013838674131701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50770348554009225782754467 76155522831013838674131701)
            ·
              refine ⟨7139580265407547375699847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76155522831013838674131701 7139580265407547375699847)
              ·
                refine ⟨10709370398111321063549771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7139580265407547375699847 10709370398111321063549771)
                ·
                  refine ⟨16064055597166981595324657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10709370398111321063549771 16064055597166981595324657)
                  ·
                    refine ⟨12048041697875236196493493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16064055597166981595324657 12048041697875236196493493)
                    ·
                      refine ⟨1129503909175803393421265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12048041697875236196493493 1129503909175803393421265)
                      ·
                        rfl

theorem cell23_2199701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_2199701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199701 prefixEnd_2199701 := by exact prefixLift 2199701
  have htrace : WordTrace (prefixWord ++ tailWord_2199701) baseStart_2199701 baseEnd_2199701 := by
    simpa [prefixWord, tailWord_2199701, baseEnd_2199701] using wordTrace_append hprefix tailTrace_2199701
  have hstable : (prefixWord ++ tailWord_2199701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199701).length < 2 ^ (prefixWord ++ tailWord_2199701).sum := by decide
  have hdescent : baseEnd_2199701 < baseStart_2199701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199706 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2]
def baseStart_2199706 : Nat := 118140960795 + 2199706 * 2 ^ 59
def prefixEnd_2199706 : Nat := 4983230072969 + 3 ^ 40 * 2199706 * 2
def baseEnd_2199706 : Nat := 1129506476579075873858743

theorem tailTrace_2199706 : CollatzResearch.WordTrace tailWord_2199706 prefixEnd_2199706 1129506476579075873858743 := by
  unfold tailWord_2199706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057467242212079180126743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53486579312565544480337981 20057467242212079180126743)
  ·
    refine ⟨30086200863318118770190115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20057467242212079180126743 30086200863318118770190115)
    ·
      refine ⟨45129301294977178155285173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30086200863318118770190115 45129301294977178155285173)
      ·
        refine ⟨4230871996404110452057985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45129301294977178155285173 4230871996404110452057985)
        ·
          refine ⟨3173153997303082839043489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4230871996404110452057985 3173153997303082839043489)
          ·
            refine ⟨2379865497977312129282617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3173153997303082839043489 2379865497977312129282617)
            ·
              refine ⟨1784899123482984096961963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379865497977312129282617 1784899123482984096961963)
              ·
                refine ⟨2677348685224476145442945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1784899123482984096961963 2677348685224476145442945)
                ·
                  refine ⟨2008011513918357109082209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2677348685224476145442945 2008011513918357109082209)
                  ·
                    refine ⟨1506008635438767831811657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2008011513918357109082209 1506008635438767831811657)
                    ·
                      refine ⟨1129506476579075873858743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506008635438767831811657 1129506476579075873858743)
                      ·
                        rfl

theorem cell23_2199706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_2199706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199706 prefixEnd_2199706 := by exact prefixLift 2199706
  have htrace : WordTrace (prefixWord ++ tailWord_2199706) baseStart_2199706 baseEnd_2199706 := by
    simpa [prefixWord, tailWord_2199706, baseEnd_2199706] using wordTrace_append hprefix tailTrace_2199706
  have hstable : (prefixWord ++ tailWord_2199706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199706).length < 2 ^ (prefixWord ++ tailWord_2199706).sum := by decide
  have hdescent : baseEnd_2199706 < baseStart_2199706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199725 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 2, 5]
def baseStart_2199725 : Nat := 118140960795 + 2199725 * 2 ^ 59
def prefixEnd_2199725 : Nat := 4983230072969 + 3 ^ 40 * 2199725 * 2
def baseEnd_2199725 : Nat := 376505410903837099840385

theorem tailTrace_2199725 : CollatzResearch.WordTrace tailWord_2199725 prefixEnd_2199725 376505410903837099840385 := by
  unfold tailWord_2199725
  simp only [CollatzResearch.WordTrace]
  refine ⟨80230561955779482965448629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53487041303852988643632419 80230561955779482965448629)
  ·
    refine ⟨7521615183354326528010809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80230561955779482965448629 7521615183354326528010809)
    ·
      refine ⟨5641211387515744896008107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7521615183354326528010809 5641211387515744896008107)
      ·
        refine ⟨8461817081273617344012161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641211387515744896008107 8461817081273617344012161)
        ·
          refine ⟨6346362810955213008009121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8461817081273617344012161 6346362810955213008009121)
          ·
            refine ⟨4759772108216409756006841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6346362810955213008009121 4759772108216409756006841)
            ·
              refine ⟨3569829081162307317005131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759772108216409756006841 3569829081162307317005131)
              ·
                refine ⟨5354743621743460975507697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569829081162307317005131 5354743621743460975507697)
                ·
                  refine ⟨4016057716307595731630773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354743621743460975507697 4016057716307595731630773)
                  ·
                    refine ⟨376505410903837099840385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4016057716307595731630773 376505410903837099840385)
                    ·
                      rfl

theorem cell23_2199725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_2199725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199725 prefixEnd_2199725 := by exact prefixLift 2199725
  have htrace : WordTrace (prefixWord ++ tailWord_2199725) baseStart_2199725 baseEnd_2199725 := by
    simpa [prefixWord, tailWord_2199725, baseEnd_2199725] using wordTrace_append hprefix tailTrace_2199725
  have hstable : (prefixWord ++ tailWord_2199725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199725).length < 2 ^ (prefixWord ++ tailWord_2199725).sum := by decide
  have hdescent : baseEnd_2199725 < baseStart_2199725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199741 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2199741 : Nat := 118140960795 + 2199741 * 2 ^ 59
def prefixEnd_2199741 : Nat := 4983230072969 + 3 ^ 40 * 2199741 * 2
def baseEnd_2199741 : Nat := 1129524448401983236921081

theorem tailTrace_2199741 : CollatzResearch.WordTrace tailWord_2199741 prefixEnd_2199741 1129524448401983236921081 := by
  unfold tailWord_2199741
  simp only [CollatzResearch.WordTrace]
  refine ⟨80231145523721517698031077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53487430349147678465354051 80231145523721517698031077)
  ·
    refine ⟨15043339785697784568380827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80231145523721517698031077 15043339785697784568380827)
    ·
      refine ⟨22565009678546676852571241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15043339785697784568380827 22565009678546676852571241)
      ·
        refine ⟨16923757258910007639428431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22565009678546676852571241 16923757258910007639428431)
        ·
          refine ⟨25385635888365011459142647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16923757258910007639428431 25385635888365011459142647)
          ·
            refine ⟨38078453832547517188713971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25385635888365011459142647 38078453832547517188713971)
            ·
              refine ⟨57117680748821275783070957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38078453832547517188713971 57117680748821275783070957)
              ·
                refine ⟨21419130280807978418651609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57117680748821275783070957 21419130280807978418651609)
                ·
                  refine ⟨16064347710605983813988707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21419130280807978418651609 16064347710605983813988707)
                  ·
                    refine ⟨24096521565908975720983061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16064347710605983813988707 24096521565908975720983061)
                    ·
                      refine ⟨1129524448401983236921081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24096521565908975720983061 1129524448401983236921081)
                      ·
                        rfl

theorem cell23_2199741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2199741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199741 prefixEnd_2199741 := by exact prefixLift 2199741
  have htrace : WordTrace (prefixWord ++ tailWord_2199741) baseStart_2199741 baseEnd_2199741 := by
    simpa [prefixWord, tailWord_2199741, baseEnd_2199741] using wordTrace_append hprefix tailTrace_2199741
  have hstable : (prefixWord ++ tailWord_2199741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199741).length < 2 ^ (prefixWord ++ tailWord_2199741).sum := by decide
  have hdescent : baseEnd_2199741 < baseStart_2199741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199746 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2199746 : Nat := 118140960795 + 2199746 * 2 ^ 59
def prefixEnd_2199746 : Nat := 4983230072969 + 3 ^ 40 * 2199746 * 2
def baseEnd_2199746 : Nat := 125503001756139524150951

theorem tailTrace_2199746 : CollatzResearch.WordTrace tailWord_2199746 prefixEnd_2199746 125503001756139524150951 := by
  unfold tailWord_2199746
  simp only [CollatzResearch.WordTrace]
  refine ⟨20057831972175850887990773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53487551925802269034642061 20057831972175850887990773)
  ·
    refine ⟨1880421747391486020749135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20057831972175850887990773 1880421747391486020749135)
    ·
      refine ⟨2820632621087229031123703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1880421747391486020749135 2820632621087229031123703)
      ·
        refine ⟨4230948931630843546685555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820632621087229031123703 4230948931630843546685555)
        ·
          refine ⟨6346423397446265320028333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4230948931630843546685555 6346423397446265320028333)
          ·
            refine ⟨2379908774042349495010625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6346423397446265320028333 2379908774042349495010625)
            ·
              refine ⟨1784931580531762121257969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2379908774042349495010625 1784931580531762121257969)
              ·
                refine ⟨1338698685398821590943477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1784931580531762121257969 1338698685398821590943477)
                ·
                  refine ⟨125503001756139524150951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1338698685398821590943477 125503001756139524150951)
                  ·
                    rfl

theorem cell23_2199746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2199746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199746 prefixEnd_2199746 := by exact prefixLift 2199746
  have htrace : WordTrace (prefixWord ++ tailWord_2199746) baseStart_2199746 baseEnd_2199746 := by
    simpa [prefixWord, tailWord_2199746, baseEnd_2199746] using wordTrace_append hprefix tailTrace_2199746
  have hstable : (prefixWord ++ tailWord_2199746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199746).length < 2 ^ (prefixWord ++ tailWord_2199746).sum := by decide
  have hdescent : baseEnd_2199746 < baseStart_2199746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199755 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 1, 4]
def baseStart_2199755 : Nat := 118140960795 + 2199755 * 2 ^ 59
def prefixEnd_2199755 : Nat := 4983230072969 + 3 ^ 40 * 2199755 * 2
def baseEnd_2199755 : Nat := 376510545710382060715339

theorem tailTrace_2199755 : CollatzResearch.WordTrace tailWord_2199755 prefixEnd_2199755 376510545710382060715339 := by
  unfold tailWord_2199755
  simp only [CollatzResearch.WordTrace]
  refine ⟨80231656145670798089040719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53487770763780532059360479 80231656145670798089040719)
  ·
    refine ⟨120347484218506197133561079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80231656145670798089040719 120347484218506197133561079)
    ·
      refine ⟨180521226327759295700341619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120347484218506197133561079 180521226327759295700341619)
      ·
        refine ⟨270781839491638943550512429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180521226327759295700341619 270781839491638943550512429)
        ·
          refine ⟨101543189809364603831442161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 270781839491638943550512429 101543189809364603831442161)
          ·
            refine ⟨76157392357023452873581621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101543189809364603831442161 76157392357023452873581621)
            ·
              refine ⟨7139755533470948706898277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76157392357023452873581621 7139755533470948706898277)
              ·
                refine ⟨1338704162525802882543427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7139755533470948706898277 1338704162525802882543427)
                ·
                  refine ⟨2008056243788704323815141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338704162525802882543427 2008056243788704323815141)
                  ·
                    refine ⟨376510545710382060715339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008056243788704323815141 376510545710382060715339)
                    ·
                      rfl

theorem cell23_2199755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 4].length) (baseStart_2199755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199755 prefixEnd_2199755 := by exact prefixLift 2199755
  have htrace : WordTrace (prefixWord ++ tailWord_2199755) baseStart_2199755 baseEnd_2199755 := by
    simpa [prefixWord, tailWord_2199755, baseEnd_2199755] using wordTrace_append hprefix tailTrace_2199755
  have hstable : (prefixWord ++ tailWord_2199755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199755).length < 2 ^ (prefixWord ++ tailWord_2199755).sum := by decide
  have hdescent : baseEnd_2199755 < baseStart_2199755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199768 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 6]
def baseStart_2199768 : Nat := 118140960795 + 2199768 * 2 ^ 59
def prefixEnd_2199768 : Nat := 4983230072969 + 3 ^ 40 * 2199768 * 2
def baseEnd_2199768 : Nat := 125504256931072736809273

theorem tailTrace_2199768 : CollatzResearch.WordTrace tailWord_2199768 prefixEnd_2199768 125504256931072736809273 := by
  unfold tailWord_2199768
  simp only [CollatzResearch.WordTrace]
  refine ⟨40116065147311850654631979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53488086863082467539509305 40116065147311850654631979)
  ·
    refine ⟨60174097720967775981947969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40116065147311850654631979 60174097720967775981947969)
    ·
      refine ⟨45130573290725831986460977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60174097720967775981947969 45130573290725831986460977)
      ·
        refine ⟨33847929968044373989845733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45130573290725831986460977 33847929968044373989845733)
        ·
          refine ⟨6346486869008320123096075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33847929968044373989845733 6346486869008320123096075)
          ·
            refine ⟨9519730303512480184644113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6346486869008320123096075 9519730303512480184644113)
            ·
              refine ⟨7139797727634360138483085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9519730303512480184644113 7139797727634360138483085)
              ·
                refine ⟨2677424147862885051931157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7139797727634360138483085 2677424147862885051931157)
                ·
                  refine ⟨125504256931072736809273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2677424147862885051931157 125504256931072736809273)
                  ·
                    rfl

theorem cell23_2199768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 6].length) (baseStart_2199768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199768 prefixEnd_2199768 := by exact prefixLift 2199768
  have htrace : WordTrace (prefixWord ++ tailWord_2199768) baseStart_2199768 baseEnd_2199768 := by
    simpa [prefixWord, tailWord_2199768, baseEnd_2199768] using wordTrace_append hprefix tailTrace_2199768
  have hstable : (prefixWord ++ tailWord_2199768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199768).length < 2 ^ (prefixWord ++ tailWord_2199768).sum := by decide
  have hdescent : baseEnd_2199768 < baseStart_2199768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199779 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2199779 : Nat := 118140960795 + 2199779 * 2 ^ 59
def prefixEnd_2199779 : Nat := 4983230072969 + 3 ^ 40 * 2199779 * 2
def baseEnd_2199779 : Nat := 1129543960666854088245907

theorem tailTrace_2199779 : CollatzResearch.WordTrace tailWord_2199779 prefixEnd_2199779 1129543960666854088245907 := by
  unfold tailWord_2199779
  simp only [CollatzResearch.WordTrace]
  refine ⟨80232531497583850187914391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53488354331722566791942927 80232531497583850187914391)
  ·
    refine ⟨120348797246375775281871587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80232531497583850187914391 120348797246375775281871587)
    ·
      refine ⟨180523195869563662922807381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120348797246375775281871587 180523195869563662922807381)
      ·
        refine ⟨2115506201596449174876649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 180523195869563662922807381 2115506201596449174876649)
        ·
          refine ⟨1586629651197336881157487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2115506201596449174876649 1586629651197336881157487)
          ·
            refine ⟨2379944476796005321736231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586629651197336881157487 2379944476796005321736231)
            ·
              refine ⟨3569916715194007982604347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2379944476796005321736231 3569916715194007982604347)
              ·
                refine ⟨5354875072791011973906521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3569916715194007982604347 5354875072791011973906521)
                ·
                  refine ⟨4016156304593258980429891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354875072791011973906521 4016156304593258980429891)
                  ·
                    refine ⟨6024234456889888470644837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016156304593258980429891 6024234456889888470644837)
                    ·
                      refine ⟨1129543960666854088245907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6024234456889888470644837 1129543960666854088245907)
                      ·
                        rfl

theorem cell23_2199779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2199779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199779 prefixEnd_2199779 := by exact prefixLift 2199779
  have htrace : WordTrace (prefixWord ++ tailWord_2199779) baseStart_2199779 baseEnd_2199779 := by
    simpa [prefixWord, tailWord_2199779, baseEnd_2199779] using wordTrace_append hprefix tailTrace_2199779
  have hstable : (prefixWord ++ tailWord_2199779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199779).length < 2 ^ (prefixWord ++ tailWord_2199779).sum := by decide
  have hdescent : baseEnd_2199779 < baseStart_2199779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199789 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_2199789 : Nat := 118140960795 + 2199789 * 2 ^ 59
def prefixEnd_2199789 : Nat := 4983230072969 + 3 ^ 40 * 2199789 * 2
def baseEnd_2199789 : Nat := 376516365157799683040287

theorem tailTrace_2199789 : CollatzResearch.WordTrace tailWord_2199789 prefixEnd_2199789 376516365157799683040287 := by
  unfold tailWord_2199789
  simp only [CollatzResearch.WordTrace]
  refine ⟨80232896227547621895778421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53488597485031747930518947 80232896227547621895778421)
  ·
    refine ⟨7521834021332589552729227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 80232896227547621895778421 7521834021332589552729227)
    ·
      refine ⟨11282751031998884329093841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7521834021332589552729227 11282751031998884329093841)
      ·
        refine ⟨8462063273999163246820381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11282751031998884329093841 8462063273999163246820381)
        ·
          refine ⟨3173273727749686217557643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8462063273999163246820381 3173273727749686217557643)
          ·
            refine ⟨4759910591624529326336465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173273727749686217557643 4759910591624529326336465)
            ·
              refine ⟨3569932943718396994752349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4759910591624529326336465 3569932943718396994752349)
              ·
                refine ⟨1338724853894398873032131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3569932943718396994752349 1338724853894398873032131)
                ·
                  refine ⟨2008087280841598309548197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338724853894398873032131 2008087280841598309548197)
                  ·
                    refine ⟨376516365157799683040287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008087280841598309548197 376516365157799683040287)
                    ·
                      rfl

theorem cell23_2199789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_2199789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199789 prefixEnd_2199789 := by exact prefixLift 2199789
  have htrace : WordTrace (prefixWord ++ tailWord_2199789) baseStart_2199789 baseEnd_2199789 := by
    simpa [prefixWord, tailWord_2199789, baseEnd_2199789] using wordTrace_append hprefix tailTrace_2199789
  have hstable : (prefixWord ++ tailWord_2199789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199789).length < 2 ^ (prefixWord ++ tailWord_2199789).sum := by decide
  have hdescent : baseEnd_2199789 < baseStart_2199789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199805 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 2, 3, 2]
def baseStart_2199805 : Nat := 118140960795 + 2199805 * 2 ^ 59
def prefixEnd_2199805 : Nat := 4983230072969 + 3 ^ 40 * 2199805 * 2
def baseEnd_2199805 : Nat := 1129557311163870986520787

theorem tailTrace_2199805 : CollatzResearch.WordTrace tailWord_2199805 prefixEnd_2199805 1129557311163870986520787 := by
  unfold tailWord_2199805
  simp only [CollatzResearch.WordTrace]
  refine ⟨80233479795489656628360869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53488986530326437752240579 80233479795489656628360869)
  ·
    refine ⟨15043777461654310617817663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80233479795489656628360869 15043777461654310617817663)
    ·
      refine ⟨22565666192481465926726495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15043777461654310617817663 22565666192481465926726495)
      ·
        refine ⟨33848499288722198890089743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22565666192481465926726495 33848499288722198890089743)
        ·
          refine ⟨50772748933083298335134615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33848499288722198890089743 50772748933083298335134615)
          ·
            refine ⟨76159123399624947502701923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50772748933083298335134615 76159123399624947502701923)
            ·
              refine ⟨114238685099437421254052885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76159123399624947502701923 114238685099437421254052885)
              ·
                refine ⟨5354938364036129121283729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 114238685099437421254052885 5354938364036129121283729)
                ·
                  refine ⟨4016203773027096840962797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5354938364036129121283729 4016203773027096840962797)
                  ·
                    refine ⟨1506076414885161315361049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4016203773027096840962797 1506076414885161315361049)
                    ·
                      refine ⟨1129557311163870986520787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506076414885161315361049 1129557311163870986520787)
                      ·
                        rfl

theorem cell23_2199805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_2199805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199805 prefixEnd_2199805 := by exact prefixLift 2199805
  have htrace : WordTrace (prefixWord ++ tailWord_2199805) baseStart_2199805 baseEnd_2199805 := by
    simpa [prefixWord, tailWord_2199805, baseEnd_2199805] using wordTrace_append hprefix tailTrace_2199805
  have hstable : (prefixWord ++ tailWord_2199805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199805).length < 2 ^ (prefixWord ++ tailWord_2199805).sum := by decide
  have hdescent : baseEnd_2199805 < baseStart_2199805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199818 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4]
def baseStart_2199818 : Nat := 118140960795 + 2199818 * 2 ^ 59
def prefixEnd_2199818 : Nat := 4983230072969 + 3 ^ 40 * 2199818 * 2
def baseEnd_2199818 : Nat := 1129563986412379435658227

theorem tailTrace_2199818 : CollatzResearch.WordTrace tailWord_2199818 prefixEnd_2199818 1129563986412379435658227 := by
  unfold tailWord_2199818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20058488486110639962146027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53489302629628373232389405 20058488486110639962146027)
  ·
    refine ⟨30087732729165959943219041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20058488486110639962146027 30087732729165959943219041)
    ·
      refine ⟨22565799546874469957414281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30087732729165959943219041 22565799546874469957414281)
      ·
        refine ⟨16924349660155852468060711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22565799546874469957414281 16924349660155852468060711)
        ·
          refine ⟨25386524490233778702091067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16924349660155852468060711 25386524490233778702091067)
          ·
            refine ⟨38079786735350668053136601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25386524490233778702091067 38079786735350668053136601)
            ·
              refine ⟨28559840051513001039852451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38079786735350668053136601 28559840051513001039852451)
              ·
                refine ⟨42839760077269501559778677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28559840051513001039852451 42839760077269501559778677)
                ·
                  refine ⟨4016227507244015771229251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42839760077269501559778677 4016227507244015771229251)
                  ·
                    refine ⟨6024341260866023656843877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016227507244015771229251 6024341260866023656843877)
                    ·
                      refine ⟨1129563986412379435658227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6024341260866023656843877 1129563986412379435658227)
                      ·
                        rfl

theorem cell23_2199818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_2199818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199818 prefixEnd_2199818 := by exact prefixLift 2199818
  have htrace : WordTrace (prefixWord ++ tailWord_2199818) baseStart_2199818 baseEnd_2199818 := by
    simpa [prefixWord, tailWord_2199818, baseEnd_2199818] using wordTrace_append hprefix tailTrace_2199818
  have hstable : (prefixWord ++ tailWord_2199818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199818).length < 2 ^ (prefixWord ++ tailWord_2199818).sum := by decide
  have hdescent : baseEnd_2199818 < baseStart_2199818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199855 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 3]
def baseStart_2199855 : Nat := 118140960795 + 2199855 * 2 ^ 59
def prefixEnd_2199855 : Nat := 4983230072969 + 3 ^ 40 * 2199855 * 2
def baseEnd_2199855 : Nat := 1129582985196595790895557

theorem tailTrace_2199855 : CollatzResearch.WordTrace tailWord_2199855 prefixEnd_2199855 1129582985196595790895557 := by
  unfold tailWord_2199855
  simp only [CollatzResearch.WordTrace]
  refine ⟨80235303445308515167681019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53490202296872343445120679 80235303445308515167681019)
  ·
    refine ⟨120352955167962772751521529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80235303445308515167681019 120352955167962772751521529)
    ·
      refine ⟨90264716375972079563641147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120352955167962772751521529 90264716375972079563641147)
      ·
        refine ⟨135397074563958119345461721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90264716375972079563641147 135397074563958119345461721)
        ·
          refine ⟨101547805922968589509096291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135397074563958119345461721 101547805922968589509096291)
          ·
            refine ⟨152321708884452884263644437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101547805922968589509096291 152321708884452884263644437)
            ·
              refine ⟨7140080103958728949858333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 152321708884452884263644437 7140080103958728949858333)
              ·
                refine ⟨2677530038984523356196875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7140080103958728949858333 2677530038984523356196875)
                ·
                  refine ⟨4016295058476785034295313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2677530038984523356196875 4016295058476785034295313)
                  ·
                    refine ⟨3012221293857588775721485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4016295058476785034295313 3012221293857588775721485)
                    ·
                      refine ⟨1129582985196595790895557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3012221293857588775721485 1129582985196595790895557)
                      ·
                        rfl

theorem cell23_2199855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 2, 3].length) (baseStart_2199855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199855 prefixEnd_2199855 := by exact prefixLift 2199855
  have htrace : WordTrace (prefixWord ++ tailWord_2199855) baseStart_2199855 baseEnd_2199855 := by
    simpa [prefixWord, tailWord_2199855, baseEnd_2199855] using wordTrace_append hprefix tailTrace_2199855
  have hstable : (prefixWord ++ tailWord_2199855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199855).length < 2 ^ (prefixWord ++ tailWord_2199855).sum := by decide
  have hdescent : baseEnd_2199855 < baseStart_2199855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199925 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_2199925 : Nat := 118140960795 + 2199925 * 2 ^ 59
def prefixEnd_2199925 : Nat := 4983230072969 + 3 ^ 40 * 2199925 * 2
def baseEnd_2199925 : Nat := 1129618928842410517020235

theorem tailTrace_2199925 : CollatzResearch.WordTrace tailWord_2199925 prefixEnd_2199925 1129618928842410517020235 := by
  unfold tailWord_2199925
  simp only [CollatzResearch.WordTrace]
  refine ⟨80237856555054917122729229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53491904370036611415152819 80237856555054917122729229)
  ·
    refine ⟨30089196208145593921023461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80237856555054917122729229 30089196208145593921023461)
    ·
      refine ⟨5641724289027298860191899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30089196208145593921023461 5641724289027298860191899)
      ·
        refine ⟨8462586433540948290287849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641724289027298860191899 8462586433540948290287849)
        ·
          refine ⟨6346939825155711217715887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8462586433540948290287849 6346939825155711217715887)
          ·
            refine ⟨9520409737733566826573831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6346939825155711217715887 9520409737733566826573831)
            ·
              refine ⟨14280614606600350239860747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9520409737733566826573831 14280614606600350239860747)
              ·
                refine ⟨21420921909900525359791121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14280614606600350239860747 21420921909900525359791121)
                ·
                  refine ⟨16065691432425394019843341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21420921909900525359791121 16065691432425394019843341)
                  ·
                    refine ⟨6024634287159522757441253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16065691432425394019843341 6024634287159522757441253)
                    ·
                      refine ⟨1129618928842410517020235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6024634287159522757441253 1129618928842410517020235)
                      ·
                        rfl

theorem cell23_2199925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_2199925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199925 prefixEnd_2199925 := by exact prefixLift 2199925
  have htrace : WordTrace (prefixWord ++ tailWord_2199925) baseStart_2199925 baseEnd_2199925 := by
    simpa [prefixWord, tailWord_2199925, baseEnd_2199925] using wordTrace_append hprefix tailTrace_2199925
  have hstable : (prefixWord ++ tailWord_2199925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199925).length < 2 ^ (prefixWord ++ tailWord_2199925).sum := by decide
  have hdescent : baseEnd_2199925 < baseStart_2199925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199948 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 9]
def baseStart_2199948 : Nat := 118140960795 + 2199948 * 2 ^ 59
def prefixEnd_2199948 : Nat := 4983230072969 + 3 ^ 40 * 2199948 * 2
def baseEnd_2199948 : Nat := 125514526544162658559181

theorem tailTrace_2199948 : CollatzResearch.WordTrace tailWord_2199948 prefixEnd_2199948 125514526544162658559181 := by
  unfold tailWord_2199948
  simp only [CollatzResearch.WordTrace]
  refine ⟨40119347716985796025408249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53492463622647728033877665 40119347716985796025408249)
  ·
    refine ⟨30089510787739347019056187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40119347716985796025408249 30089510787739347019056187)
    ·
      refine ⟨45134266181609020528584281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30089510787739347019056187 45134266181609020528584281)
      ·
        refine ⟨33850699636206765396438211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45134266181609020528584281 33850699636206765396438211)
        ·
          refine ⟨50776049454310148094657317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33850699636206765396438211 50776049454310148094657317)
          ·
            refine ⟨9520509272683152767748247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50776049454310148094657317 9520509272683152767748247)
            ·
              refine ⟨14280763909024729151622371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9520509272683152767748247 14280763909024729151622371)
              ·
                refine ⟨21421145863537093727433557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14280763909024729151622371 21421145863537093727433557)
                ·
                  refine ⟨125514526544162658559181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 21421145863537093727433557 125514526544162658559181)
                  ·
                    rfl

theorem cell23_2199948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 9].length) (baseStart_2199948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199948 prefixEnd_2199948 := by exact prefixLift 2199948
  have htrace : WordTrace (prefixWord ++ tailWord_2199948) baseStart_2199948 baseEnd_2199948 := by
    simpa [prefixWord, tailWord_2199948, baseEnd_2199948] using wordTrace_append hprefix tailTrace_2199948
  have hstable : (prefixWord ++ tailWord_2199948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199948).length < 2 ^ (prefixWord ++ tailWord_2199948).sum := by decide
  have hdescent : baseEnd_2199948 < baseStart_2199948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2199976 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2199976 : Nat := 118140960795 + 2199976 * 2 ^ 59
def prefixEnd_2199976 : Nat := 4983230072969 + 3 ^ 40 * 2199976 * 2
def baseEnd_2199976 : Nat := 1129645116355789817482501

theorem tailTrace_2199976 : CollatzResearch.WordTrace tailWord_2199976 prefixEnd_2199976 1129645116355789817482501 := by
  unfold tailWord_2199976
  simp only [CollatzResearch.WordTrace]
  refine ⟨40119858338935076416417891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 53493144451913435221890521 40119858338935076416417891)
  ·
    refine ⟨60179787508402614624626837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40119858338935076416417891 60179787508402614624626837)
    ·
      refine ⟨2820927539456372560529383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60179787508402614624626837 2820927539456372560529383)
      ·
        refine ⟨4231391309184558840794075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2820927539456372560529383 4231391309184558840794075)
        ·
          refine ⟨6347086963776838261191113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4231391309184558840794075 6347086963776838261191113)
          ·
            refine ⟨4760315222832628695893335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6347086963776838261191113 4760315222832628695893335)
            ·
              refine ⟨7140472834248943043840003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4760315222832628695893335 7140472834248943043840003)
              ·
                refine ⟨10710709251373414565760005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7140472834248943043840003 10710709251373414565760005)
                ·
                  refine ⟨2008257984632515231080001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10710709251373414565760005 2008257984632515231080001)
                  ·
                    refine ⟨1506193488474386423310001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2008257984632515231080001 1506193488474386423310001)
                    ·
                      refine ⟨1129645116355789817482501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1506193488474386423310001 1129645116355789817482501)
                      ·
                        rfl

theorem cell23_2199976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2199976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2199976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2199976 prefixEnd_2199976 := by exact prefixLift 2199976
  have htrace : WordTrace (prefixWord ++ tailWord_2199976) baseStart_2199976 baseEnd_2199976 := by
    simpa [prefixWord, tailWord_2199976, baseEnd_2199976] using wordTrace_append hprefix tailTrace_2199976
  have hstable : (prefixWord ++ tailWord_2199976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2199976).length < 2 ^ (prefixWord ++ tailWord_2199976).sum := by decide
  have hdescent : baseEnd_2199976 < baseStart_2199976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2199976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200015 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 4]
def baseStart_2200015 : Nat := 118140960795 + 2200015 * 2 ^ 59
def prefixEnd_2200015 : Nat := 4983230072969 + 3 ^ 40 * 2200015 * 2
def baseEnd_2200015 : Nat := 1129665142101315164894821

theorem tailTrace_2200015 : CollatzResearch.WordTrace tailWord_2200015 prefixEnd_2200015 1129665142101315164894821 := by
  unfold tailWord_2200015
  simp only [CollatzResearch.WordTrace]
  refine ⟨80241139124728862493505499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53494092749819241662336999 80241139124728862493505499)
  ·
    refine ⟨120361708687093293740258249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80241139124728862493505499 120361708687093293740258249)
    ·
      refine ⟨90271281515319970305193687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120361708687093293740258249 90271281515319970305193687)
      ·
        refine ⟨135406922272979955457790531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90271281515319970305193687 135406922272979955457790531)
        ·
          refine ⟨203110383409469933186685797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135406922272979955457790531 203110383409469933186685797)
          ·
            refine ⟨38083196889275612472503587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203110383409469933186685797 38083196889275612472503587)
            ·
              refine ⟨57124795333913418708755381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38083196889275612472503587 57124795333913418708755381)
              ·
                refine ⟨5355449562554383003945817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57124795333913418708755381 5355449562554383003945817)
                ·
                  refine ⟨4016587171915787252959363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5355449562554383003945817 4016587171915787252959363)
                  ·
                    refine ⟨6024880757873680879439045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016587171915787252959363 6024880757873680879439045)
                    ·
                      refine ⟨1129665142101315164894821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6024880757873680879439045 1129665142101315164894821)
                      ·
                        rfl

theorem cell23_2200015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 1, 4].length) (baseStart_2200015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200015 prefixEnd_2200015 := by exact prefixLift 2200015
  have htrace : WordTrace (prefixWord ++ tailWord_2200015) baseStart_2200015 baseEnd_2200015 := by
    simpa [prefixWord, tailWord_2200015, baseEnd_2200015] using wordTrace_append hprefix tailTrace_2200015
  have hstable : (prefixWord ++ tailWord_2200015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200015).length < 2 ^ (prefixWord ++ tailWord_2200015).sum := by decide
  have hdescent : baseEnd_2200015 < baseStart_2200015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200022 : List Nat := [5, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2200022 : Nat := 118140960795 + 2200022 * 2 ^ 59
def prefixEnd_2200022 : Nat := 4983230072969 + 3 ^ 40 * 2200022 * 2
def baseEnd_2200022 : Nat := 1129668736465896637507289

theorem tailTrace_2200022 : CollatzResearch.WordTrace tailWord_2200022 prefixEnd_2200022 1129668736465896637507289 := by
  unfold tailWord_2200022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015087152231468918063145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 53494262957135668459340213 5015087152231468918063145)
  ·
    refine ⟨3761315364173601688547359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5015087152231468918063145 3761315364173601688547359)
    ·
      refine ⟨5641973046260402532821039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761315364173601688547359 5641973046260402532821039)
      ·
        refine ⟨8462959569390603799231559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5641973046260402532821039 8462959569390603799231559)
        ·
          refine ⟨12694439354085905698847339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8462959569390603799231559 12694439354085905698847339)
          ·
            refine ⟨19041659031128858548271009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12694439354085905698847339 19041659031128858548271009)
            ·
              refine ⟨14281244273346643911203257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19041659031128858548271009 14281244273346643911203257)
              ·
                refine ⟨10710933205009982933402443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14281244273346643911203257 10710933205009982933402443)
                ·
                  refine ⟨16066399807514974400103665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10710933205009982933402443 16066399807514974400103665)
                  ·
                    refine ⟨12049799855636230800077749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16066399807514974400103665 12049799855636230800077749)
                    ·
                      refine ⟨1129668736465896637507289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12049799855636230800077749 1129668736465896637507289)
                      ·
                        rfl

theorem cell23_2200022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2200022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200022 prefixEnd_2200022 := by exact prefixLift 2200022
  have htrace : WordTrace (prefixWord ++ tailWord_2200022) baseStart_2200022 baseEnd_2200022 := by
    simpa [prefixWord, tailWord_2200022, baseEnd_2200022] using wordTrace_append hprefix tailTrace_2200022
  have hstable : (prefixWord ++ tailWord_2200022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200022).length < 2 ^ (prefixWord ++ tailWord_2200022).sum := by decide
  have hdescent : baseEnd_2200022 < baseStart_2200022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200066 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2200066 : Nat := 118140960795 + 2200066 * 2 ^ 59
def prefixEnd_2200066 : Nat := 4983230072969 + 3 ^ 40 * 2200066 * 2
def baseEnd_2200066 : Nat := 1129691329614694465357087

theorem tailTrace_2200066 : CollatzResearch.WordTrace tailWord_2200066 prefixEnd_2200066 1129691329614694465357087 := by
  unfold tailWord_2200066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20060749811886024550903013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 53495332831696065469074701 20060749811886024550903013)
  ·
    refine ⟨3761390589728629603294315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20060749811886024550903013 3761390589728629603294315)
    ·
      refine ⟨5642085884592944404941473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3761390589728629603294315 5642085884592944404941473)
      ·
        refine ⟨4231564413444708303706105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5642085884592944404941473 4231564413444708303706105)
        ·
          refine ⟨3173673310083531227779579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4231564413444708303706105 3173673310083531227779579)
          ·
            refine ⟨4760509965125296841669369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3173673310083531227779579 4760509965125296841669369)
            ·
              refine ⟨3570382473843972631252027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4760509965125296841669369 3570382473843972631252027)
              ·
                refine ⟨5355573710765958946878041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3570382473843972631252027 5355573710765958946878041)
                ·
                  refine ⟨4016680283074469210158531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5355573710765958946878041 4016680283074469210158531)
                  ·
                    refine ⟨6025020424611703815237797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4016680283074469210158531 6025020424611703815237797)
                    ·
                      refine ⟨1129691329614694465357087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6025020424611703815237797 1129691329614694465357087)
                      ·
                        rfl

theorem cell23_2200066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2200066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200066 prefixEnd_2200066 := by exact prefixLift 2200066
  have htrace : WordTrace (prefixWord ++ tailWord_2200066) baseStart_2200066 baseEnd_2200066 := by
    simpa [prefixWord, tailWord_2200066, baseEnd_2200066] using wordTrace_append hprefix tailTrace_2200066
  have hstable : (prefixWord ++ tailWord_2200066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200066).length < 2 ^ (prefixWord ++ tailWord_2200066).sum := by decide
  have hdescent : baseEnd_2200066 < baseStart_2200066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2200093 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 1, 4]
def baseStart_2200093 : Nat := 118140960795 + 2200093 * 2 ^ 59
def prefixEnd_2200093 : Nat := 4983230072969 + 3 ^ 40 * 2200093 * 2
def baseEnd_2200093 : Nat := 376568397864121953239821

theorem tailTrace_2200093 : CollatzResearch.WordTrace tailWord_2200093 prefixEnd_2200093 376568397864121953239821 := by
  unfold tailWord_2200093
  simp only [CollatzResearch.WordTrace]
  refine ⟨80243984018446281814844933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 53495989345630854543229955 80243984018446281814844933)
  ·
    refine ⟨15045747003458677840283425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80243984018446281814844933 15045747003458677840283425)
    ·
      refine ⟨11284310252594008380212569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15045747003458677840283425 11284310252594008380212569)
      ·
        refine ⟨8463232689445506285159427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11284310252594008380212569 8463232689445506285159427)
        ·
          refine ⟨12694849034168259427739141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8463232689445506285159427 12694849034168259427739141)
          ·
            refine ⟨2380284193906548642701089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12694849034168259427739141 2380284193906548642701089)
            ·
              refine ⟨1785213145429911482025817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2380284193906548642701089 1785213145429911482025817)
              ·
                refine ⟨1338909859072433611519363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1785213145429911482025817 1338909859072433611519363)
                ·
                  refine ⟨2008364788608650417279045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338909859072433611519363 2008364788608650417279045)
                  ·
                    refine ⟨376568397864121953239821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2008364788608650417279045 376568397864121953239821)
                    ·
                      rfl

theorem cell23_2200093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_2200093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2200093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2200093 prefixEnd_2200093 := by exact prefixLift 2200093
  have htrace : WordTrace (prefixWord ++ tailWord_2200093) baseStart_2200093 baseEnd_2200093 := by
    simpa [prefixWord, tailWord_2200093, baseEnd_2200093] using wordTrace_append hprefix tailTrace_2200093
  have hstable : (prefixWord ++ tailWord_2200093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2200093).length < 2 ^ (prefixWord ++ tailWord_2200093).sum := by decide
  have hdescent : baseEnd_2200093 < baseStart_2200093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2200093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
