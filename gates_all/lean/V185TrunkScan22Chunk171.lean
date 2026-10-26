import V185TrunkScan22Chunk170

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1526321 : List Nat := [1, 2, 2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_1526321 : Nat := 118140960795 + 1526321 * 2 ^ 59
def prefixEnd_1526321 : Nat := 4983230072969 + 3 ^ 40 * 1526321 * 2
def baseEnd_1526321 : Nat := 522490870700818663845389

theorem tailTrace_1526321 : CollatzResearch.WordTrace tailWord_1526321 prefixEnd_1526321 522490870700818663845389 := by
  unfold tailWord_1526321
  simp only [CollatzResearch.WordTrace]
  refine ⟨55669500303407166718522817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37113000202271444479015211 55669500303407166718522817)
  ·
    refine ⟨41752125227555375038892113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55669500303407166718522817 41752125227555375038892113)
    ·
      refine ⟨31314093920666531279169085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41752125227555375038892113 31314093920666531279169085)
      ·
        refine ⟨11742785220249949229688407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31314093920666531279169085 11742785220249949229688407)
        ·
          refine ⟨17614177830374923844532611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11742785220249949229688407 17614177830374923844532611)
          ·
            refine ⟨26421266745562385766798917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17614177830374923844532611 26421266745562385766798917)
            ·
              refine ⟨4953987514792947331274797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26421266745562385766798917 4953987514792947331274797)
              ·
                refine ⟨1857745318047355249228049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4953987514792947331274797 1857745318047355249228049)
                ·
                  refine ⟨1393308988535516436921037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1857745318047355249228049 1393308988535516436921037)
                  ·
                    refine ⟨522490870700818663845389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393308988535516436921037 522490870700818663845389)
                    ·
                      rfl

theorem cell22_1526321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_1526321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526321 prefixEnd_1526321 := by exact prefixLift 1526321
  have htrace : WordTrace (prefixWord ++ tailWord_1526321) baseStart_1526321 baseEnd_1526321 := by
    simpa [prefixWord, tailWord_1526321, baseEnd_1526321] using wordTrace_append hprefix tailTrace_1526321
  have hstable : (prefixWord ++ tailWord_1526321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526321).length < 2 ^ (prefixWord ++ tailWord_1526321).sum := by decide
  have hdescent : baseEnd_1526321 < baseStart_1526321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526342 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_1526342 : Nat := 118140960795 + 1526342 * 2 ^ 59
def prefixEnd_1526342 : Nat := 4983230072969 + 3 ^ 40 * 1526342 * 2
def baseEnd_1526342 : Nat := 522498059429981609070325

theorem tailTrace_1526342 : CollatzResearch.WordTrace tailWord_1526342 prefixEnd_1526342 522498059429981609070325 := by
  unfold tailWord_1526342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1739695819885346478282415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37113510824220724870024853 1739695819885346478282415)
  ·
    refine ⟨2609543729828019717423623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1739695819885346478282415 2609543729828019717423623)
    ·
      refine ⟨3914315594742029576135435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2609543729828019717423623 3914315594742029576135435)
      ·
        refine ⟨5871473392113044364203153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914315594742029576135435 5871473392113044364203153)
        ·
          refine ⟨4403605044084783273152365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5871473392113044364203153 4403605044084783273152365)
          ·
            refine ⟨1651351891531793727432137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4403605044084783273152365 1651351891531793727432137)
            ·
              refine ⟨1238513918648845295574103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1651351891531793727432137 1238513918648845295574103)
              ·
                refine ⟨1857770877973267943361155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238513918648845295574103 1857770877973267943361155)
                ·
                  refine ⟨2786656316959901915041733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1857770877973267943361155 2786656316959901915041733)
                  ·
                    refine ⟨522498059429981609070325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786656316959901915041733 522498059429981609070325)
                    ·
                      rfl

theorem cell22_1526342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_1526342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526342 prefixEnd_1526342 := by exact prefixLift 1526342
  have htrace : WordTrace (prefixWord ++ tailWord_1526342) baseStart_1526342 baseEnd_1526342 := by
    simpa [prefixWord, tailWord_1526342, baseEnd_1526342] using wordTrace_append hprefix tailTrace_1526342
  have hstable : (prefixWord ++ tailWord_1526342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526342).length < 2 ^ (prefixWord ++ tailWord_1526342).sum := by decide
  have hdescent : baseEnd_1526342 < baseStart_1526342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526400 : List Nat := [2, 1, 1, 2, 1, 7, 1, 3, 1, 3]
def baseStart_1526400 : Nat := 118140960795 + 1526400 * 2 ^ 59
def prefixEnd_1526400 : Nat := 4983230072969 + 3 ^ 40 * 1526400 * 2
def baseEnd_1526400 : Nat := 522517914015288791120147

theorem tailTrace_1526400 : CollatzResearch.WordTrace tailWord_1526400 prefixEnd_1526400 522517914015288791120147 := by
  unfold tailWord_1526400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836190835060481605324327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37114921113413975473765769 27836190835060481605324327)
  ·
    refine ⟨41754286252590722407986491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27836190835060481605324327 41754286252590722407986491)
    ·
      refine ⟨62631429378886083611979737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41754286252590722407986491 62631429378886083611979737)
      ·
        refine ⟨46973572034164562708984803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62631429378886083611979737 46973572034164562708984803)
        ·
          refine ⟨70460358051246844063477205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46973572034164562708984803 70460358051246844063477205)
          ·
            refine ⟨1651414641826097907737747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70460358051246844063477205 1651414641826097907737747)
            ·
              refine ⟨2477121962739146861606621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651414641826097907737747 2477121962739146861606621)
              ·
                refine ⟨928920736027180073102483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2477121962739146861606621 928920736027180073102483)
                ·
                  refine ⟨1393381104040770109653725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 928920736027180073102483 1393381104040770109653725)
                  ·
                    refine ⟨522517914015288791120147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393381104040770109653725 522517914015288791120147)
                    ·
                      rfl

theorem cell22_1526400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 3, 1, 3].length) (baseStart_1526400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526400 prefixEnd_1526400 := by exact prefixLift 1526400
  have htrace : WordTrace (prefixWord ++ tailWord_1526400) baseStart_1526400 baseEnd_1526400 := by
    simpa [prefixWord, tailWord_1526400, baseEnd_1526400] using wordTrace_append hprefix tailTrace_1526400
  have hstable : (prefixWord ++ tailWord_1526400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526400).length < 2 ^ (prefixWord ++ tailWord_1526400).sum := by decide
  have hdescent : baseEnd_1526400 < baseStart_1526400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526402 : List Nat := [3, 4, 3, 1, 2, 1, 8]
def baseStart_1526402 : Nat := 118140960795 + 1526402 * 2 ^ 59
def prefixEnd_1526402 : Nat := 4983230072969 + 3 ^ 40 * 1526402 * 2
def baseEnd_1526402 : Nat := 19352540690968942687783

theorem tailTrace_1526402 : CollatzResearch.WordTrace tailWord_1526402 prefixEnd_1526402 19352540690968942687783 := by
  unfold tailWord_1526402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13918113654028429388055365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37114969744075811701480973 13918113654028429388055365)
  ·
    refine ⟨2609646310130330510260381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13918113654028429388055365 2609646310130330510260381)
    ·
      refine ⟨978617366298873941347643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2609646310130330510260381 978617366298873941347643)
      ·
        refine ⟨1467926049448310912021465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978617366298873941347643 1467926049448310912021465)
        ·
          refine ⟨1100944537086233184016099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1467926049448310912021465 1100944537086233184016099)
          ·
            refine ⟨1651416805629349776024149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1100944537086233184016099 1651416805629349776024149)
            ·
              refine ⟨19352540690968942687783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1651416805629349776024149 19352540690968942687783)
              ·
                rfl

theorem cell22_1526402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 8].length) (baseStart_1526402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526402 prefixEnd_1526402 := by exact prefixLift 1526402
  have htrace : WordTrace (prefixWord ++ tailWord_1526402) baseStart_1526402 baseEnd_1526402 := by
    simpa [prefixWord, tailWord_1526402, baseEnd_1526402] using wordTrace_append hprefix tailTrace_1526402
  have hstable : (prefixWord ++ tailWord_1526402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526402).length < 2 ^ (prefixWord ++ tailWord_1526402).sum := by decide
  have hdescent : baseEnd_1526402 < baseStart_1526402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526409 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 5, 4]
def baseStart_1526409 : Nat := 118140960795 + 1526409 * 2 ^ 59
def prefixEnd_1526409 : Nat := 4983230072969 + 3 ^ 40 * 1526409 * 2
def baseEnd_1526409 : Nat := 522520994899215767645119

theorem tailTrace_1526409 : CollatzResearch.WordTrace tailWord_1526409 prefixEnd_1526409 522520994899215767645119 := by
  unfold tailWord_1526409
  simp only [CollatzResearch.WordTrace]
  refine ⟨55672709927088357747726281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37115139951392238498484187 55672709927088357747726281)
  ·
    refine ⟨41754532445316268310794711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55672709927088357747726281 41754532445316268310794711)
    ·
      refine ⟨62631798667974402466192067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41754532445316268310794711 62631798667974402466192067)
      ·
        refine ⟨93947698001961603699288101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62631798667974402466192067 93947698001961603699288101)
        ·
          refine ⟨17615193375367800693616519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93947698001961603699288101 17615193375367800693616519)
          ·
            refine ⟨26422790063051701040424779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17615193375367800693616519 26422790063051701040424779)
            ·
              refine ⟨39634185094577551560637169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26422790063051701040424779 39634185094577551560637169)
              ·
                refine ⟨29725638820933163670477877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39634185094577551560637169 29725638820933163670477877)
                ·
                  refine ⟨2786778639462484094107301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29725638820933163670477877 2786778639462484094107301)
                  ·
                    refine ⟨522520994899215767645119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2786778639462484094107301 522520994899215767645119)
                    ·
                      rfl

theorem cell22_1526409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 5, 4].length) (baseStart_1526409 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526409 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526409 prefixEnd_1526409 := by exact prefixLift 1526409
  have htrace : WordTrace (prefixWord ++ tailWord_1526409) baseStart_1526409 baseEnd_1526409 := by
    simpa [prefixWord, tailWord_1526409, baseEnd_1526409] using wordTrace_append hprefix tailTrace_1526409
  have hstable : (prefixWord ++ tailWord_1526409).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526409).length < 2 ^ (prefixWord ++ tailWord_1526409).sum := by decide
  have hdescent : baseEnd_1526409 < baseStart_1526409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526518 : List Nat := [5, 1, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_1526518 : Nat := 118140960795 + 1526518 * 2 ^ 59
def prefixEnd_1526518 : Nat := 4983230072969 + 3 ^ 40 * 1526518 * 2
def baseEnd_1526518 : Nat := 522558307826775816669785

theorem tailTrace_1526518 : CollatzResearch.WordTrace tailWord_1526518 prefixEnd_1526518 522558307826775816669785 := by
  unfold tailWord_1526518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479792842730841835215263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37117790322462312908962805 3479792842730841835215263)
  ·
    refine ⟨5219689264096262752822895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3479792842730841835215263 5219689264096262752822895)
    ·
      refine ⟨7829533896144394129234343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219689264096262752822895 7829533896144394129234343)
      ·
        refine ⟨11744300844216591193851515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829533896144394129234343 11744300844216591193851515)
        ·
          refine ⟨17616451266324886790777273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11744300844216591193851515 17616451266324886790777273)
          ·
            refine ⟨13212338449743665093082955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17616451266324886790777273 13212338449743665093082955)
            ·
              refine ⟨19818507674615497639624433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13212338449743665093082955 19818507674615497639624433)
              ·
                refine ⟨14863880755961623229718325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19818507674615497639624433 14863880755961623229718325)
                ·
                  refine ⟨1393488820871402177786093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14863880755961623229718325 1393488820871402177786093)
                  ·
                    refine ⟨522558307826775816669785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393488820871402177786093 522558307826775816669785)
                    ·
                      rfl

theorem cell22_1526518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_1526518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526518 prefixEnd_1526518 := by exact prefixLift 1526518
  have htrace : WordTrace (prefixWord ++ tailWord_1526518) baseStart_1526518 baseEnd_1526518 := by
    simpa [prefixWord, tailWord_1526518, baseEnd_1526518] using wordTrace_append hprefix tailTrace_1526518
  have hstable : (prefixWord ++ tailWord_1526518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526518).length < 2 ^ (prefixWord ++ tailWord_1526518).sum := by decide
  have hdescent : baseEnd_1526518 < baseStart_1526518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526535 : List Nat := [1, 1, 4, 4, 1, 2, 2, 1, 3, 3]
def baseStart_1526535 : Nat := 118140960795 + 1526535 * 2 ^ 59
def prefixEnd_1526535 : Nat := 4983230072969 + 3 ^ 40 * 1526535 * 2
def baseEnd_1526535 : Nat := 522564127274193438994733

theorem tailTrace_1526535 : CollatzResearch.WordTrace tailWord_1526535 prefixEnd_1526535 522564127274193438994733 := by
  unfold tailWord_1526535
  simp only [CollatzResearch.WordTrace]
  refine ⟨55677305524631881266813059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37118203683087920844542039 55677305524631881266813059)
  ·
    refine ⟨83515958286947821900219589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55677305524631881266813059 83515958286947821900219589)
    ·
      refine ⟨15659242178802716606291173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83515958286947821900219589 15659242178802716606291173)
      ·
        refine ⟨2936107908525509363679595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15659242178802716606291173 2936107908525509363679595)
        ·
          refine ⟨4404161862788264045519393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936107908525509363679595 4404161862788264045519393)
          ·
            refine ⟨3303121397091198034139545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4404161862788264045519393 3303121397091198034139545)
            ·
              refine ⟨2477341047818398525604659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3303121397091198034139545 2477341047818398525604659)
              ·
                refine ⟨3716011571727597788406989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477341047818398525604659 3716011571727597788406989)
                ·
                  refine ⟨1393504339397849170652621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3716011571727597788406989 1393504339397849170652621)
                  ·
                    refine ⟨522564127274193438994733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393504339397849170652621 522564127274193438994733)
                    ·
                      rfl

theorem cell22_1526535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_1526535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526535 prefixEnd_1526535 := by exact prefixLift 1526535
  have htrace : WordTrace (prefixWord ++ tailWord_1526535) baseStart_1526535 baseEnd_1526535 := by
    simpa [prefixWord, tailWord_1526535, baseEnd_1526535] using wordTrace_append hprefix tailTrace_1526535
  have hstable : (prefixWord ++ tailWord_1526535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526535).length < 2 ^ (prefixWord ++ tailWord_1526535).sum := by decide
  have hdescent : baseEnd_1526535 < baseStart_1526535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526578 : List Nat := [3, 2, 1, 1, 3, 1, 1, 5, 1, 4]
def baseStart_1526578 : Nat := 118140960795 + 1526578 * 2 ^ 59
def prefixEnd_1526578 : Nat := 4983230072969 + 3 ^ 40 * 1526578 * 2
def baseEnd_1526578 : Nat := 522578847052955660169601

theorem tailTrace_1526578 : CollatzResearch.WordTrace tailWord_1526578 prefixEnd_1526578 522578847052955660169601 := by
  unfold tailWord_1526578
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919718465869024902657097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37119249242317399740418925 13919718465869024902657097)
  ·
    refine ⟨10439788849401768676992823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13919718465869024902657097 10439788849401768676992823)
    ·
      refine ⟨15659683274102653015489235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439788849401768676992823 15659683274102653015489235)
      ·
        refine ⟨23489524911153979523233853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15659683274102653015489235 23489524911153979523233853)
        ·
          refine ⟨8808571841682742321212695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23489524911153979523233853 8808571841682742321212695)
          ·
            refine ⟨13212857762524113481819043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8808571841682742321212695 13212857762524113481819043)
            ·
              refine ⟨19819286643786170222728565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13212857762524113481819043 19819286643786170222728565)
              ·
                refine ⟨1858058122854953458380803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19819286643786170222728565 1858058122854953458380803)
                ·
                  refine ⟨2787087184282430187571205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858058122854953458380803 2787087184282430187571205)
                  ·
                    refine ⟨522578847052955660169601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787087184282430187571205 522578847052955660169601)
                    ·
                      rfl

theorem cell22_1526578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_1526578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526578 prefixEnd_1526578 := by exact prefixLift 1526578
  have htrace : WordTrace (prefixWord ++ tailWord_1526578) baseStart_1526578 baseEnd_1526578 := by
    simpa [prefixWord, tailWord_1526578, baseEnd_1526578] using wordTrace_append hprefix tailTrace_1526578
  have hstable : (prefixWord ++ tailWord_1526578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526578).length < 2 ^ (prefixWord ++ tailWord_1526578).sum := by decide
  have hdescent : baseEnd_1526578 < baseStart_1526578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526606 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1526606 : Nat := 118140960795 + 1526606 * 2 ^ 59
def prefixEnd_1526606 : Nat := 4983230072969 + 3 ^ 40 * 1526606 * 2
def baseEnd_1526606 : Nat := 522588432025172920469515

theorem tailTrace_1526606 : CollatzResearch.WordTrace tailWord_1526606 prefixEnd_1526606 522588432025172920469515 := by
  unfold tailWord_1526606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959986888421832549080959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37119930071583106928431781 6959986888421832549080959)
  ·
    refine ⟨10439980332632748823621439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6959986888421832549080959 10439980332632748823621439)
    ·
      refine ⟨15659970498949123235432159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10439980332632748823621439 15659970498949123235432159)
      ·
        refine ⟨23489955748423684853148239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15659970498949123235432159 23489955748423684853148239)
        ·
          refine ⟨35234933622635527279722359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23489955748423684853148239 35234933622635527279722359)
          ·
            refine ⟨52852400433953290919583539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35234933622635527279722359 52852400433953290919583539)
            ·
              refine ⟨79278600650929936379375309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52852400433953290919583539 79278600650929936379375309)
              ·
                refine ⟨29729475244098726142265741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79278600650929936379375309 29729475244098726142265741)
                ·
                  refine ⟨11148553216537022303349653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29729475244098726142265741 11148553216537022303349653)
                  ·
                    refine ⟨522588432025172920469515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11148553216537022303349653 522588432025172920469515)
                    ·
                      rfl

theorem cell22_1526606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1526606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526606 prefixEnd_1526606 := by exact prefixLift 1526606
  have htrace : WordTrace (prefixWord ++ tailWord_1526606) baseStart_1526606 baseEnd_1526606 := by
    simpa [prefixWord, tailWord_1526606, baseEnd_1526606] using wordTrace_append hprefix tailTrace_1526606
  have hstable : (prefixWord ++ tailWord_1526606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526606).length < 2 ^ (prefixWord ++ tailWord_1526606).sum := by decide
  have hdescent : baseEnd_1526606 < baseStart_1526606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526612 : List Nat := [2, 4, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_1526612 : Nat := 118140960795 + 1526612 * 2 ^ 59
def prefixEnd_1526612 : Nat := 4983230072969 + 3 ^ 40 * 1526612 * 2
def baseEnd_1526612 : Nat := 522590485947790904819497

theorem tailTrace_1526612 : CollatzResearch.WordTrace tailWord_1526612 prefixEnd_1526612 522590485947790904819497 := by
  unfold tailWord_1526612
  simp only [CollatzResearch.WordTrace]
  refine ⟨27840056972676461708683045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37120075963568615611577393 27840056972676461708683045)
  ·
    refine ⟨5220010682376836570378071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27840056972676461708683045 5220010682376836570378071)
    ·
      refine ⟨7830016023565254855567107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5220010682376836570378071 7830016023565254855567107)
      ·
        refine ⟨11745024035347882283350661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830016023565254855567107 11745024035347882283350661)
        ·
          refine ⟨2202192006627727928128249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11745024035347882283350661 2202192006627727928128249)
          ·
            refine ⟨1651644004970795946096187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202192006627727928128249 1651644004970795946096187)
            ·
              refine ⟨2477466007456193919144281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651644004970795946096187 2477466007456193919144281)
              ·
                refine ⟨1858099505592145439358211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477466007456193919144281 1858099505592145439358211)
                ·
                  refine ⟨2787149258388218159037317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858099505592145439358211 2787149258388218159037317)
                  ·
                    refine ⟨522590485947790904819497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787149258388218159037317 522590485947790904819497)
                    ·
                      rfl

theorem cell22_1526612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_1526612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526612 prefixEnd_1526612 := by exact prefixLift 1526612
  have htrace : WordTrace (prefixWord ++ tailWord_1526612) baseStart_1526612 baseEnd_1526612 := by
    simpa [prefixWord, tailWord_1526612, baseEnd_1526612] using wordTrace_append hprefix tailTrace_1526612
  have hstable : (prefixWord ++ tailWord_1526612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526612).length < 2 ^ (prefixWord ++ tailWord_1526612).sum := by decide
  have hdescent : baseEnd_1526612 < baseStart_1526612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526623 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 2, 4]
def baseStart_1526623 : Nat := 118140960795 + 1526623 * 2 ^ 59
def prefixEnd_1526623 : Nat := 4983230072969 + 3 ^ 40 * 1526623 * 2
def baseEnd_1526623 : Nat := 522594251472590542794463

theorem tailTrace_1526623 : CollatzResearch.WordTrace tailWord_1526623 prefixEnd_1526623 522594251472590542794463 := by
  unfold tailWord_1526623
  simp only [CollatzResearch.WordTrace]
  refine ⟨55680515148313072296016523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37120343432208714864011015 55680515148313072296016523)
  ·
    refine ⟨83520772722469608444024785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55680515148313072296016523 83520772722469608444024785)
    ·
      refine ⟨62640579541852206333018589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83520772722469608444024785 62640579541852206333018589)
      ·
        refine ⟨23490217328194577374881971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62640579541852206333018589 23490217328194577374881971)
        ·
          refine ⟨35235325992291866062322957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23490217328194577374881971 35235325992291866062322957)
          ·
            refine ⟨13213247247109449773371109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35235325992291866062322957 13213247247109449773371109)
            ·
              refine ⟨2477483858833021832507083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13213247247109449773371109 2477483858833021832507083)
              ·
                refine ⟨3716225788249532748760625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477483858833021832507083 3716225788249532748760625)
                ·
                  refine ⟨2787169341187149561570469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3716225788249532748760625 2787169341187149561570469)
                  ·
                    refine ⟨522594251472590542794463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787169341187149561570469 522594251472590542794463)
                    ·
                      rfl

theorem cell22_1526623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 2, 4].length) (baseStart_1526623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526623 prefixEnd_1526623 := by exact prefixLift 1526623
  have htrace : WordTrace (prefixWord ++ tailWord_1526623) baseStart_1526623 baseEnd_1526623 := by
    simpa [prefixWord, tailWord_1526623, baseEnd_1526623] using wordTrace_append hprefix tailTrace_1526623
  have hstable : (prefixWord ++ tailWord_1526623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526623).length < 2 ^ (prefixWord ++ tailWord_1526623).sum := by decide
  have hdescent : baseEnd_1526623 < baseStart_1526623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526638 : List Nat := [4, 1, 2, 3, 2, 10]
def baseStart_1526638 : Nat := 118140960795 + 1526638 * 2 ^ 59
def prefixEnd_1526638 : Nat := 4983230072969 + 3 ^ 40 * 1526638 * 2
def baseEnd_1526638 : Nat := 6451844275051055600857

theorem tailTrace_1526638 : CollatzResearch.WordTrace tailWord_1526638 prefixEnd_1526638 6451844275051055600857 := by
  unfold tailWord_1526638
  simp only [CollatzResearch.WordTrace]
  refine ⟨6960132780407341232226571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37120708162172486571875045 6960132780407341232226571)
  ·
    refine ⟨10440199170611011848339857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6960132780407341232226571 10440199170611011848339857)
    ·
      refine ⟨7830149377958258886254893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10440199170611011848339857 7830149377958258886254893)
      ·
        refine ⟨2936306016734347082345585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7830149377958258886254893 2936306016734347082345585)
        ·
          refine ⟨2202229512550760311759189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936306016734347082345585 2202229512550760311759189)
          ·
            refine ⟨6451844275051055600857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2202229512550760311759189 6451844275051055600857)
            ·
              rfl

theorem cell22_1526638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 10].length) (baseStart_1526638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526638 prefixEnd_1526638 := by exact prefixLift 1526638
  have htrace : WordTrace (prefixWord ++ tailWord_1526638) baseStart_1526638 baseEnd_1526638 := by
    simpa [prefixWord, tailWord_1526638, baseEnd_1526638] using wordTrace_append hprefix tailTrace_1526638
  have hstable : (prefixWord ++ tailWord_1526638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526638).length < 2 ^ (prefixWord ++ tailWord_1526638).sum := by decide
  have hdescent : baseEnd_1526638 < baseStart_1526638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526651 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 2, 6]
def baseStart_1526651 : Nat := 118140960795 + 1526651 * 2 ^ 59
def prefixEnd_1526651 : Nat := 4983230072969 + 3 ^ 40 * 1526651 * 2
def baseEnd_1526651 : Nat := 522603836444807803094377

theorem tailTrace_1526651 : CollatzResearch.WordTrace tailWord_1526651 prefixEnd_1526651 522603836444807803094377 := by
  unfold tailWord_1526651
  simp only [CollatzResearch.WordTrace]
  refine ⟨55681536392211633078035807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37121024261474422052023871 55681536392211633078035807)
  ·
    refine ⟨83522304588317449617053711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55681536392211633078035807 83522304588317449617053711)
    ·
      refine ⟨125283456882476174425580567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83522304588317449617053711 125283456882476174425580567)
      ·
        refine ⟨187925185323714261638370851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125283456882476174425580567 187925185323714261638370851)
        ·
          refine ⟨281887777985571392457556277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187925185323714261638370851 281887777985571392457556277)
          ·
            refine ⟨26426979186147318042895901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281887777985571392457556277 26426979186147318042895901)
            ·
              refine ⟨9910117194805244266085963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26426979186147318042895901 9910117194805244266085963)
              ·
                refine ⟨14865175792207866399128945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9910117194805244266085963 14865175792207866399128945)
                ·
                  refine ⟨11148881844155899799346709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14865175792207866399128945 11148881844155899799346709)
                  ·
                    refine ⟨522603836444807803094377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11148881844155899799346709 522603836444807803094377)
                    ·
                      rfl

theorem cell22_1526651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_1526651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526651 prefixEnd_1526651 := by exact prefixLift 1526651
  have htrace : WordTrace (prefixWord ++ tailWord_1526651) baseStart_1526651 baseEnd_1526651 := by
    simpa [prefixWord, tailWord_1526651, baseEnd_1526651] using wordTrace_append hprefix tailTrace_1526651
  have hstable : (prefixWord ++ tailWord_1526651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526651).length < 2 ^ (prefixWord ++ tailWord_1526651).sum := by decide
  have hdescent : baseEnd_1526651 < baseStart_1526651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526674 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 2, 4]
def baseStart_1526674 : Nat := 118140960795 + 1526674 * 2 ^ 59
def prefixEnd_1526674 : Nat := 4983230072969 + 3 ^ 40 * 1526674 * 2
def baseEnd_1526674 : Nat := 522611709814843409769307

theorem tailTrace_1526674 : CollatzResearch.WordTrace tailWord_1526674 prefixEnd_1526674 522611709814843409769307 := by
  unfold tailWord_1526674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13920593817782077001530769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37121583514085538670748717 13920593817782077001530769)
  ·
    refine ⟨10440445363336557751148077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13920593817782077001530769 10440445363336557751148077)
    ·
      refine ⟨3915167011251209156680529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10440445363336557751148077 3915167011251209156680529)
      ·
        refine ⟨2936375258438406867510397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3915167011251209156680529 2936375258438406867510397)
        ·
          refine ⟨1101140721914402575316399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2936375258438406867510397 1101140721914402575316399)
          ·
            refine ⟨1651711082871603862974599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101140721914402575316399 1651711082871603862974599)
            ·
              refine ⟨2477566624307405794461899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651711082871603862974599 2477566624307405794461899)
              ·
                refine ⟨3716349936461108691692849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477566624307405794461899 3716349936461108691692849)
                ·
                  refine ⟨2787262452345831518769637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3716349936461108691692849 2787262452345831518769637)
                  ·
                    refine ⟨522611709814843409769307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787262452345831518769637 522611709814843409769307)
                    ·
                      rfl

theorem cell22_1526674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_1526674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526674 prefixEnd_1526674 := by exact prefixLift 1526674
  have htrace : WordTrace (prefixWord ++ tailWord_1526674) baseStart_1526674 baseEnd_1526674 := by
    simpa [prefixWord, tailWord_1526674, baseEnd_1526674] using wordTrace_append hprefix tailTrace_1526674
  have hstable : (prefixWord ++ tailWord_1526674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526674).length < 2 ^ (prefixWord ++ tailWord_1526674).sum := by decide
  have hdescent : baseEnd_1526674 < baseStart_1526674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526681 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_1526681 : Nat := 118140960795 + 1526681 * 2 ^ 59
def prefixEnd_1526681 : Nat := 4983230072969 + 3 ^ 40 * 1526681 * 2
def baseEnd_1526681 : Nat := 522614106057897724844285

theorem tailTrace_1526681 : CollatzResearch.WordTrace tailWord_1526681 prefixEnd_1526681 522614106057897724844285 := by
  unfold tailWord_1526681
  simp only [CollatzResearch.WordTrace]
  refine ⟨55682630582102948201627897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37121753721401965467751931 55682630582102948201627897)
  ·
    refine ⟨41761972936577211151220923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55682630582102948201627897 41761972936577211151220923)
    ·
      refine ⟨62642959404865816726831385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41761972936577211151220923 62642959404865816726831385)
      ·
        refine ⟨46982219553649362545123539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62642959404865816726831385 46982219553649362545123539)
        ·
          refine ⟨70473329330474043817685309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46982219553649362545123539 70473329330474043817685309)
          ·
            refine ⟨26427498498927766431631991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70473329330474043817685309 26427498498927766431631991)
            ·
              refine ⟨39641247748391649647447987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26427498498927766431631991 39641247748391649647447987)
              ·
                refine ⟨59461871622587474471171981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39641247748391649647447987 59461871622587474471171981)
                ·
                  refine ⟨22298201858470302926689493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59461871622587474471171981 22298201858470302926689493)
                  ·
                    refine ⟨522614106057897724844285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22298201858470302926689493 522614106057897724844285)
                    ·
                      rfl

theorem cell22_1526681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_1526681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526681 prefixEnd_1526681 := by exact prefixLift 1526681
  have htrace : WordTrace (prefixWord ++ tailWord_1526681) baseStart_1526681 baseEnd_1526681 := by
    simpa [prefixWord, tailWord_1526681, baseEnd_1526681] using wordTrace_append hprefix tailTrace_1526681
  have hstable : (prefixWord ++ tailWord_1526681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526681).length < 2 ^ (prefixWord ++ tailWord_1526681).sum := by decide
  have hdescent : baseEnd_1526681 < baseStart_1526681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526687 : List Nat := [1, 1, 2, 5, 2, 1, 1, 5, 1, 3]
def baseStart_1526687 : Nat := 118140960795 + 1526687 * 2 ^ 59
def prefixEnd_1526687 : Nat := 4983230072969 + 3 ^ 40 * 1526687 * 2
def baseEnd_1526687 : Nat := 522616159980515709194267

theorem tailTrace_1526687 : CollatzResearch.WordTrace tailWord_1526687 prefixEnd_1526687 522616159980515709194267 := by
  unfold tailWord_1526687
  simp only [CollatzResearch.WordTrace]
  refine ⟨55682849420081211226346315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37121899613387474150897543 55682849420081211226346315)
  ·
    refine ⟨83524274130121816839519473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55682849420081211226346315 83524274130121816839519473)
    ·
      refine ⟨62643205597591362629639605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83524274130121816839519473 62643205597591362629639605)
      ·
        refine ⟨5872800524774190246528713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62643205597591362629639605 5872800524774190246528713)
        ·
          refine ⟨4404600393580642684896535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5872800524774190246528713 4404600393580642684896535)
          ·
            refine ⟨6606900590370964027344803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404600393580642684896535 6606900590370964027344803)
            ·
              refine ⟨9910350885556446041017205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606900590370964027344803 9910350885556446041017205)
              ·
                refine ⟨929095395520916816345363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9910350885556446041017205 929095395520916816345363)
                ·
                  refine ⟨1393643093281375224518045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929095395520916816345363 1393643093281375224518045)
                  ·
                    refine ⟨522616159980515709194267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393643093281375224518045 522616159980515709194267)
                    ·
                      rfl

theorem cell22_1526687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_1526687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526687 prefixEnd_1526687 := by exact prefixLift 1526687
  have htrace : WordTrace (prefixWord ++ tailWord_1526687) baseStart_1526687 baseEnd_1526687 := by
    simpa [prefixWord, tailWord_1526687, baseEnd_1526687] using wordTrace_append hprefix tailTrace_1526687
  have hstable : (prefixWord ++ tailWord_1526687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526687).length < 2 ^ (prefixWord ++ tailWord_1526687).sum := by decide
  have hdescent : baseEnd_1526687 < baseStart_1526687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526717 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 5]
def baseStart_1526717 : Nat := 118140960795 + 1526717 * 2 ^ 59
def prefixEnd_1526717 : Nat := 4983230072969 + 3 ^ 40 * 1526717 * 2
def baseEnd_1526717 : Nat := 174208809864535210314725

theorem tailTrace_1526717 : CollatzResearch.WordTrace tailWord_1526717 prefixEnd_1526717 174208809864535210314725 := by
  unfold tailWord_1526717
  simp only [CollatzResearch.WordTrace]
  refine ⟨55683943609972526349938405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37122629073315017566625603 55683943609972526349938405)
  ·
    refine ⟨10440739426869848690613451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55683943609972526349938405 10440739426869848690613451)
    ·
      refine ⟨15661109140304773035920177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10440739426869848690613451 15661109140304773035920177)
      ·
        refine ⟨11745831855228579776940133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15661109140304773035920177 11745831855228579776940133)
        ·
          refine ⟨2202343472855358708176275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11745831855228579776940133 2202343472855358708176275)
          ·
            refine ⟨3303515209283038062264413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202343472855358708176275 3303515209283038062264413)
            ·
              refine ⟨1238818203481139273349155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3303515209283038062264413 1238818203481139273349155)
              ·
                refine ⟨1858227305221708910023733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1238818203481139273349155 1858227305221708910023733)
                ·
                  refine ⟨174208809864535210314725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1858227305221708910023733 174208809864535210314725)
                  ·
                    rfl

theorem cell22_1526717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_1526717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526717 prefixEnd_1526717 := by exact prefixLift 1526717
  have htrace : WordTrace (prefixWord ++ tailWord_1526717) baseStart_1526717 baseEnd_1526717 := by
    simpa [prefixWord, tailWord_1526717, baseEnd_1526717] using wordTrace_append hprefix tailTrace_1526717
  have hstable : (prefixWord ++ tailWord_1526717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526717).length < 2 ^ (prefixWord ++ tailWord_1526717).sum := by decide
  have hdescent : baseEnd_1526717 < baseStart_1526717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526760 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1526760 : Nat := 118140960795 + 1526760 * 2 ^ 59
def prefixEnd_1526760 : Nat := 4983230072969 + 3 ^ 40 * 1526760 * 2
def baseEnd_1526760 : Nat := 522641149372367852119043

theorem tailTrace_1526760 : CollatzResearch.WordTrace tailWord_1526760 prefixEnd_1526760 522641149372367852119043 := by
  unfold tailWord_1526760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27842755974408372346876867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37123674632544496462502489 27842755974408372346876867)
  ·
    refine ⟨41764133961612558520315301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27842755974408372346876867 41764133961612558520315301)
    ·
      refine ⟨7830775117802354722559119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41764133961612558520315301 7830775117802354722559119)
      ·
        refine ⟨11746162676703532083838679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7830775117802354722559119 11746162676703532083838679)
        ·
          refine ⟨17619244015055298125758019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11746162676703532083838679 17619244015055298125758019)
          ·
            refine ⟨26428866022582947188637029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17619244015055298125758019 26428866022582947188637029)
            ·
              refine ⟨4955412379234302597869443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26428866022582947188637029 4955412379234302597869443)
              ·
                refine ⟨7433118568851453896804165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955412379234302597869443 7433118568851453896804165)
                ·
                  refine ⟨1393709731659647605650781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7433118568851453896804165 1393709731659647605650781)
                  ·
                    refine ⟨522641149372367852119043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393709731659647605650781 522641149372367852119043)
                    ·
                      rfl

theorem cell22_1526760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1526760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526760 prefixEnd_1526760 := by exact prefixLift 1526760
  have htrace : WordTrace (prefixWord ++ tailWord_1526760) baseStart_1526760 baseEnd_1526760 := by
    simpa [prefixWord, tailWord_1526760, baseEnd_1526760] using wordTrace_append hprefix tailTrace_1526760
  have hstable : (prefixWord ++ tailWord_1526760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526760).length < 2 ^ (prefixWord ++ tailWord_1526760).sum := by decide
  have hdescent : baseEnd_1526760 < baseStart_1526760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526820 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1526820 : Nat := 118140960795 + 1526820 * 2 ^ 59
def prefixEnd_1526820 : Nat := 4983230072969 + 3 ^ 40 * 1526820 * 2
def baseEnd_1526820 : Nat := 522661688598547695618859

theorem tailTrace_1526820 : CollatzResearch.WordTrace tailWord_1526820 prefixEnd_1526820 522661688598547695618859 := by
  unfold tailWord_1526820
  simp only [CollatzResearch.WordTrace]
  refine ⟨27843850164299687470468957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37125133552399583293958609 27843850164299687470468957)
  ·
    refine ⟨10441443811612382801425859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27843850164299687470468957 10441443811612382801425859)
    ·
      refine ⟨15662165717418574202138789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10441443811612382801425859 15662165717418574202138789)
      ·
        refine ⟨2936656072015982662901023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15662165717418574202138789 2936656072015982662901023)
        ·
          refine ⟨4404984108023973994351535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936656072015982662901023 4404984108023973994351535)
          ·
            refine ⟨6607476162035960991527303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404984108023973994351535 6607476162035960991527303)
            ·
              refine ⟨9911214243053941487290955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6607476162035960991527303 9911214243053941487290955)
              ·
                refine ⟨14866821364580912230936433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9911214243053941487290955 14866821364580912230936433)
                ·
                  refine ⟨11150116023435684173202325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14866821364580912230936433 11150116023435684173202325)
                  ·
                    refine ⟨522661688598547695618859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11150116023435684173202325 522661688598547695618859)
                    ·
                      rfl

theorem cell22_1526820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1526820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526820 prefixEnd_1526820 := by exact prefixLift 1526820
  have htrace : WordTrace (prefixWord ++ tailWord_1526820) baseStart_1526820 baseEnd_1526820 := by
    simpa [prefixWord, tailWord_1526820, baseEnd_1526820] using wordTrace_append hprefix tailTrace_1526820
  have hstable : (prefixWord ++ tailWord_1526820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526820).length < 2 ^ (prefixWord ++ tailWord_1526820).sum := by decide
  have hdescent : baseEnd_1526820 < baseStart_1526820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526880 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 6]
def baseStart_1526880 : Nat := 118140960795 + 1526880 * 2 ^ 59
def prefixEnd_1526880 : Nat := 4983230072969 + 3 ^ 40 * 1526880 * 2
def baseEnd_1526880 : Nat := 174227409274909179706225

theorem tailTrace_1526880 : CollatzResearch.WordTrace tailWord_1526880 prefixEnd_1526880 174227409274909179706225 := by
  unfold tailWord_1526880
  simp only [CollatzResearch.WordTrace]
  refine ⟨27844944354191002594061047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37126592472254670125414729 27844944354191002594061047)
  ·
    refine ⟨41767416531286503891091571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27844944354191002594061047 41767416531286503891091571)
    ·
      refine ⟨62651124796929755836637357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41767416531286503891091571 62651124796929755836637357)
      ·
        refine ⟨23494171798848658438739009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62651124796929755836637357 23494171798848658438739009)
        ·
          refine ⟨17620628849136493829054257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23494171798848658438739009 17620628849136493829054257)
          ·
            refine ⟨13215471636852370371790693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17620628849136493829054257 13215471636852370371790693)
            ·
              refine ⟨2477900931909819444710755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13215471636852370371790693 2477900931909819444710755)
              ·
                refine ⟨3716851397864729167066133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2477900931909819444710755 3716851397864729167066133)
                ·
                  refine ⟨174227409274909179706225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3716851397864729167066133 174227409274909179706225)
                  ·
                    rfl

theorem cell22_1526880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 6].length) (baseStart_1526880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526880 prefixEnd_1526880 := by exact prefixLift 1526880
  have htrace : WordTrace (prefixWord ++ tailWord_1526880) baseStart_1526880 baseEnd_1526880 := by
    simpa [prefixWord, tailWord_1526880, baseEnd_1526880] using wordTrace_append hprefix tailTrace_1526880
  have hstable : (prefixWord ++ tailWord_1526880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526880).length < 2 ^ (prefixWord ++ tailWord_1526880).sum := by decide
  have hdescent : baseEnd_1526880 < baseStart_1526880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526942 : List Nat := [4, 3, 1, 1, 2, 1, 1, 9]
def baseStart_1526942 : Nat := 118140960795 + 1526942 * 2 ^ 59
def prefixEnd_1526942 : Nat := 4983230072969 + 3 ^ 40 * 1526942 * 2
def baseEnd_1526942 : Nat := 58078161299086671563165

theorem tailTrace_1526942 : CollatzResearch.WordTrace tailWord_1526942 prefixEnd_1526942 58078161299086671563165 := by
  unfold tailWord_1526942
  simp only [CollatzResearch.WordTrace]
  refine ⟨6961518754269673722109885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37128100022771593184586053 6961518754269673722109885)
  ·
    refine ⟨2610569532851127645791207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6961518754269673722109885 2610569532851127645791207)
    ·
      refine ⟨3915854299276691468686811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2610569532851127645791207 3915854299276691468686811)
      ·
        refine ⟨5873781448915037203030217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3915854299276691468686811 5873781448915037203030217)
        ·
          refine ⟨4405336086686277902272663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5873781448915037203030217 4405336086686277902272663)
          ·
            refine ⟨6608004130029416853408995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4405336086686277902272663 6608004130029416853408995)
            ·
              refine ⟨9912006195044125280113493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6608004130029416853408995 9912006195044125280113493)
              ·
                refine ⟨58078161299086671563165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9912006195044125280113493 58078161299086671563165)
                ·
                  rfl

theorem cell22_1526942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_1526942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526942 prefixEnd_1526942 := by exact prefixLift 1526942
  have htrace : WordTrace (prefixWord ++ tailWord_1526942) baseStart_1526942 baseEnd_1526942 := by
    simpa [prefixWord, tailWord_1526942, baseEnd_1526942] using wordTrace_append hprefix tailTrace_1526942
  have hstable : (prefixWord ++ tailWord_1526942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526942).length < 2 ^ (prefixWord ++ tailWord_1526942).sum := by decide
  have hdescent : baseEnd_1526942 < baseStart_1526942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526946 : List Nat := [3, 3, 1, 3, 2, 1, 1, 3, 2, 3]
def baseStart_1526946 : Nat := 118140960795 + 1526946 * 2 ^ 59
def prefixEnd_1526946 : Nat := 4983230072969 + 3 ^ 40 * 1526946 * 2
def baseEnd_1526946 : Nat := 522704820973525366968473

theorem tailTrace_1526946 : CollatzResearch.WordTrace tailWord_1526946 prefixEnd_1526946 522704820973525366968473 := by
  unfold tailWord_1526946
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923073981535724615006173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37128197284095265640016461 13923073981535724615006173)
  ·
    refine ⟨5221152743075896730627315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13923073981535724615006173 5221152743075896730627315)
    ·
      refine ⟨7831729114613845095940973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5221152743075896730627315 7831729114613845095940973)
      ·
        refine ⟨2936898417980191910977865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7831729114613845095940973 2936898417980191910977865)
        ·
          refine ⟨2202673813485143933233399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936898417980191910977865 2202673813485143933233399)
          ·
            refine ⟨3304010720227715899850099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2202673813485143933233399 3304010720227715899850099)
            ·
              refine ⟨4956016080341573849775149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304010720227715899850099 4956016080341573849775149)
              ·
                refine ⟨1858506030128090193665681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4956016080341573849775149 1858506030128090193665681)
                ·
                  refine ⟨1393879522596067645249261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1858506030128090193665681 1393879522596067645249261)
                  ·
                    refine ⟨522704820973525366968473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1393879522596067645249261 522704820973525366968473)
                    ·
                      rfl

theorem cell22_1526946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 3, 2, 3].length) (baseStart_1526946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526946 prefixEnd_1526946 := by exact prefixLift 1526946
  have htrace : WordTrace (prefixWord ++ tailWord_1526946) baseStart_1526946 baseEnd_1526946 := by
    simpa [prefixWord, tailWord_1526946, baseEnd_1526946] using wordTrace_append hprefix tailTrace_1526946
  have hstable : (prefixWord ++ tailWord_1526946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526946).length < 2 ^ (prefixWord ++ tailWord_1526946).sum := by decide
  have hdescent : baseEnd_1526946 < baseStart_1526946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1526982 : List Nat := [6, 1, 2, 2, 1, 2, 2, 2, 4]
def baseStart_1526982 : Nat := 118140960795 + 1526982 * 2 ^ 59
def prefixEnd_1526982 : Nat := 4983230072969 + 3 ^ 40 * 1526982 * 2
def baseEnd_1526982 : Nat := 174239048169744424356121

theorem tailTrace_1526982 : CollatzResearch.WordTrace tailWord_1526982 prefixEnd_1526982 174239048169744424356121 := by
  unfold tailWord_1526982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740425279812889894010475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37129072636008317738890133 1740425279812889894010475)
  ·
    refine ⟨2610637919719334841015713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1740425279812889894010475 2610637919719334841015713)
    ·
      refine ⟨1957978439789501130761785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2610637919719334841015713 1957978439789501130761785)
      ·
        refine ⟨1468483829842125848071339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1957978439789501130761785 1468483829842125848071339)
        ·
          refine ⟨2202725744763188772107009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468483829842125848071339 2202725744763188772107009)
          ·
            refine ⟨1652044308572391579080257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202725744763188772107009 1652044308572391579080257)
            ·
              refine ⟨1239033231429293684310193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652044308572391579080257 1239033231429293684310193)
              ·
                refine ⟨929274923571970263232645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239033231429293684310193 929274923571970263232645)
                ·
                  refine ⟨174239048169744424356121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 929274923571970263232645 174239048169744424356121)
                  ·
                    rfl

theorem cell22_1526982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_1526982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1526982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1526982 prefixEnd_1526982 := by exact prefixLift 1526982
  have htrace : WordTrace (prefixWord ++ tailWord_1526982) baseStart_1526982 baseEnd_1526982 := by
    simpa [prefixWord, tailWord_1526982, baseEnd_1526982] using wordTrace_append hprefix tailTrace_1526982
  have hstable : (prefixWord ++ tailWord_1526982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1526982).length < 2 ^ (prefixWord ++ tailWord_1526982).sum := by decide
  have hdescent : baseEnd_1526982 < baseStart_1526982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1526982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527064 : List Nat := [2, 1, 2, 3, 1, 5, 1, 1, 1, 5]
def baseStart_1527064 : Nat := 118140960795 + 1527064 * 2 ^ 59
def prefixEnd_1527064 : Nat := 4983230072969 + 3 ^ 40 * 1527064 * 2
def baseEnd_1527064 : Nat := 522745214785012392518111

theorem tailTrace_1527064 : CollatzResearch.WordTrace tailWord_1527064 prefixEnd_1527064 522745214785012392518111 := by
  unfold tailWord_1527064
  simp only [CollatzResearch.WordTrace]
  refine ⟨27848299869857702306410123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37131066493143603075213497 27848299869857702306410123)
  ·
    refine ⟨41772449804786553459615185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27848299869857702306410123 41772449804786553459615185)
    ·
      refine ⟨31329337353589915094711389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41772449804786553459615185 31329337353589915094711389)
      ·
        refine ⟨11748501507596218160516771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31329337353589915094711389 11748501507596218160516771)
        ·
          refine ⟨17622752261394327240775157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11748501507596218160516771 17622752261394327240775157)
          ·
            refine ⟨1652133024505718178822671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17622752261394327240775157 1652133024505718178822671)
            ·
              refine ⟨2478199536758577268234007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652133024505718178822671 2478199536758577268234007)
              ·
                refine ⟨3717299305137865902351011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478199536758577268234007 3717299305137865902351011)
                ·
                  refine ⟨5575948957706798853526517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717299305137865902351011 5575948957706798853526517)
                  ·
                    refine ⟨522745214785012392518111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5575948957706798853526517 522745214785012392518111)
                    ·
                      rfl

theorem cell22_1527064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_1527064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527064 prefixEnd_1527064 := by exact prefixLift 1527064
  have htrace : WordTrace (prefixWord ++ tailWord_1527064) baseStart_1527064 baseEnd_1527064 := by
    simpa [prefixWord, tailWord_1527064, baseEnd_1527064] using wordTrace_append hprefix tailTrace_1527064
  have hstable : (prefixWord ++ tailWord_1527064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527064).length < 2 ^ (prefixWord ++ tailWord_1527064).sum := by decide
  have hdescent : baseEnd_1527064 < baseStart_1527064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527077 : List Nat := [1, 3, 1, 2, 4, 2, 1, 8]
def baseStart_1527077 : Nat := 118140960795 + 1527077 * 2 ^ 59
def prefixEnd_1527077 : Nat := 4983230072969 + 3 ^ 40 * 1527077 * 2
def baseEnd_1527077 : Nat := 58083296105631632438119

theorem tailTrace_1527077 : CollatzResearch.WordTrace tailWord_1527077 prefixEnd_1527077 58083296105631632438119 := by
  unfold tailWord_1527077
  simp only [CollatzResearch.WordTrace]
  refine ⟨55697073888668307833043485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37131382592445538555362323 55697073888668307833043485)
  ·
    refine ⟨20886402708250615437391307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55697073888668307833043485 20886402708250615437391307)
    ·
      refine ⟨31329604062375923156086961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20886402708250615437391307 31329604062375923156086961)
      ·
        refine ⟨23497203046781942367065221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31329604062375923156086961 23497203046781942367065221)
        ·
          refine ⟨4405725571271614193824729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23497203046781942367065221 4405725571271614193824729)
          ·
            refine ⟨3304294178453710645368547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4405725571271614193824729 3304294178453710645368547)
            ·
              refine ⟨4956441267680565968052821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304294178453710645368547 4956441267680565968052821)
              ·
                refine ⟨58083296105631632438119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4956441267680565968052821 58083296105631632438119)
                ·
                  rfl

theorem cell22_1527077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 8].length) (baseStart_1527077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527077 prefixEnd_1527077 := by exact prefixLift 1527077
  have htrace : WordTrace (prefixWord ++ tailWord_1527077) baseStart_1527077 baseEnd_1527077 := by
    simpa [prefixWord, tailWord_1527077, baseEnd_1527077] using wordTrace_append hprefix tailTrace_1527077
  have hstable : (prefixWord ++ tailWord_1527077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527077).length < 2 ^ (prefixWord ++ tailWord_1527077).sum := by decide
  have hdescent : baseEnd_1527077 < baseStart_1527077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527199 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 1, 5]
def baseStart_1527199 : Nat := 118140960795 + 1527199 * 2 ^ 59
def prefixEnd_1527199 : Nat := 4983230072969 + 3 ^ 40 * 1527199 * 2
def baseEnd_1527199 : Nat := 522791428043917040392697

theorem tailTrace_1527199 : CollatzResearch.WordTrace tailWord_1527199 prefixEnd_1527199 522791428043917040392697 := by
  unfold tailWord_1527199
  simp only [CollatzResearch.WordTrace]
  refine ⟨55701523594226322668984651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37134349062817548445989767 55701523594226322668984651)
  ·
    refine ⟨83552285391339484003476977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55701523594226322668984651 83552285391339484003476977)
    ·
      refine ⟨62664214043504613002607733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83552285391339484003476977 62664214043504613002607733)
      ·
        refine ⟨5874770066578557468994475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62664214043504613002607733 5874770066578557468994475)
        ·
          refine ⟨8812155099867836203491713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5874770066578557468994475 8812155099867836203491713)
          ·
            refine ⟨6609116324900877152618785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8812155099867836203491713 6609116324900877152618785)
            ·
              refine ⟨4956837243675657864464089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6609116324900877152618785 4956837243675657864464089)
              ·
                refine ⟨3717627932756743398348067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956837243675657864464089 3717627932756743398348067)
                ·
                  refine ⟨5576441899135115097522101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717627932756743398348067 5576441899135115097522101)
                  ·
                    refine ⟨522791428043917040392697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5576441899135115097522101 522791428043917040392697)
                    ·
                      rfl

theorem cell22_1527199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 5].length) (baseStart_1527199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527199 prefixEnd_1527199 := by exact prefixLift 1527199
  have htrace : WordTrace (prefixWord ++ tailWord_1527199) baseStart_1527199 baseEnd_1527199 := by
    simpa [prefixWord, tailWord_1527199, baseEnd_1527199] using wordTrace_append hprefix tailTrace_1527199
  have hstable : (prefixWord ++ tailWord_1527199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527199).length < 2 ^ (prefixWord ++ tailWord_1527199).sum := by decide
  have hdescent : baseEnd_1527199 < baseStart_1527199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527351 : List Nat := [1, 1, 3, 1, 2, 5, 2, 1, 1, 5]
def baseStart_1527351 : Nat := 118140960795 + 1527351 * 2 ^ 59
def prefixEnd_1527351 : Nat := 4983230072969 + 3 ^ 40 * 1527351 * 2
def baseEnd_1527351 : Nat := 522843460750239310592231

theorem tailTrace_1527351 : CollatzResearch.WordTrace tailWord_1527351 prefixEnd_1527351 522843460750239310592231 := by
  unfold tailWord_1527351
  simp only [CollatzResearch.WordTrace]
  refine ⟨55707067489675652628517907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37138044993117101752345271 55707067489675652628517907)
  ·
    refine ⟨83560601234513478942776861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55707067489675652628517907 83560601234513478942776861)
    ·
      refine ⟨31335225462942554603541323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83560601234513478942776861 31335225462942554603541323)
      ·
        refine ⟨47002838194413831905311985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31335225462942554603541323 47002838194413831905311985)
        ·
          refine ⟨35252128645810373928983989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47002838194413831905311985 35252128645810373928983989)
          ·
            refine ⟨3304887060544722555842249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35252128645810373928983989 3304887060544722555842249)
            ·
              refine ⟨2478665295408541916881687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3304887060544722555842249 2478665295408541916881687)
              ·
                refine ⟨3717997943112812875322531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2478665295408541916881687 3717997943112812875322531)
                ·
                  refine ⟨5576996914669219312983797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717997943112812875322531 5576996914669219312983797)
                  ·
                    refine ⟨522843460750239310592231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5576996914669219312983797 522843460750239310592231)
                    ·
                      rfl

theorem cell22_1527351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 5].length) (baseStart_1527351 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527351 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527351 prefixEnd_1527351 := by exact prefixLift 1527351
  have htrace : WordTrace (prefixWord ++ tailWord_1527351) baseStart_1527351 baseEnd_1527351 := by
    simpa [prefixWord, tailWord_1527351, baseEnd_1527351] using wordTrace_append hprefix tailTrace_1527351
  have hstable : (prefixWord ++ tailWord_1527351).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527351).length < 2 ^ (prefixWord ++ tailWord_1527351).sum := by decide
  have hdescent : baseEnd_1527351 < baseStart_1527351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527447 : List Nat := [1, 1, 3, 3, 2, 3, 3, 2, 1, 3]
def baseStart_1527447 : Nat := 118140960795 + 1527447 * 2 ^ 59
def prefixEnd_1527447 : Nat := 4983230072969 + 3 ^ 40 * 1527447 * 2
def baseEnd_1527447 : Nat := 522876323512127060191937

theorem tailTrace_1527447 : CollatzResearch.WordTrace tailWord_1527447 prefixEnd_1527447 522876323512127060191937 := by
  unfold tailWord_1527447
  simp only [CollatzResearch.WordTrace]
  refine ⟨55710568897327861024012595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37140379264885240682675063 55710568897327861024012595)
  ·
    refine ⟨83565853345991791536018893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55710568897327861024012595 83565853345991791536018893)
    ·
      refine ⟨31337195004746921826007085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83565853345991791536018893 31337195004746921826007085)
      ·
        refine ⟨11751448126780095684752657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31337195004746921826007085 11751448126780095684752657)
        ·
          refine ⟨8813586095085071763564493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11751448126780095684752657 8813586095085071763564493)
          ·
            refine ⟨3305094785656901911336685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8813586095085071763564493 3305094785656901911336685)
            ·
              refine ⟨1239410544621338216751257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3305094785656901911336685 1239410544621338216751257)
              ·
                refine ⟨929557908466003662563443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239410544621338216751257 929557908466003662563443)
                ·
                  refine ⟨1394336862699005493845165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929557908466003662563443 1394336862699005493845165)
                  ·
                    refine ⟨522876323512127060191937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394336862699005493845165 522876323512127060191937)
                    ·
                      rfl

theorem cell22_1527447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 2, 1, 3].length) (baseStart_1527447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527447 prefixEnd_1527447 := by exact prefixLift 1527447
  have htrace : WordTrace (prefixWord ++ tailWord_1527447) baseStart_1527447 baseEnd_1527447 := by
    simpa [prefixWord, tailWord_1527447, baseEnd_1527447] using wordTrace_append hprefix tailTrace_1527447
  have hstable : (prefixWord ++ tailWord_1527447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527447).length < 2 ^ (prefixWord ++ tailWord_1527447).sum := by decide
  have hdescent : baseEnd_1527447 < baseStart_1527447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527460 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 5]
def baseStart_1527460 : Nat := 118140960795 + 1527460 * 2 ^ 59
def prefixEnd_1527460 : Nat := 4983230072969 + 3 ^ 40 * 1527460 * 2
def baseEnd_1527460 : Nat := 174293591225933119872299

theorem tailTrace_1527460 : CollatzResearch.WordTrace tailWord_1527460 prefixEnd_1527460 174293591225933119872299 := by
  unfold tailWord_1527460
  simp only [CollatzResearch.WordTrace]
  refine ⟨27855521523140382122117917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37140695364187176162823889 27855521523140382122117917)
  ·
    refine ⟨10445820571177643295794219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27855521523140382122117917 10445820571177643295794219)
    ·
      refine ⟨15668730856766464943691329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10445820571177643295794219 15668730856766464943691329)
      ·
        refine ⟨11751548142574848707768497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15668730856766464943691329 11751548142574848707768497)
        ·
          refine ⟨8813661106931136530826373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11751548142574848707768497 8813661106931136530826373)
          ·
            refine ⟨1652561457549588099529945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8813661106931136530826373 1652561457549588099529945)
            ·
              refine ⟨1239421093162191074647459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652561457549588099529945 1239421093162191074647459)
              ·
                refine ⟨1859131639743286611971189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239421093162191074647459 1859131639743286611971189)
                ·
                  refine ⟨174293591225933119872299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859131639743286611971189 174293591225933119872299)
                  ·
                    rfl

theorem cell22_1527460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_1527460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527460 prefixEnd_1527460 := by exact prefixLift 1527460
  have htrace : WordTrace (prefixWord ++ tailWord_1527460) baseStart_1527460 baseEnd_1527460 := by
    simpa [prefixWord, tailWord_1527460, baseEnd_1527460] using wordTrace_append hprefix tailTrace_1527460
  have hstable : (prefixWord ++ tailWord_1527460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527460).length < 2 ^ (prefixWord ++ tailWord_1527460).sum := by decide
  have hdescent : baseEnd_1527460 < baseStart_1527460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527488 : List Nat := [2, 1, 1, 2, 4, 1, 2, 5, 4]
def baseStart_1527488 : Nat := 118140960795 + 1527488 * 2 ^ 59
def prefixEnd_1527488 : Nat := 4983230072969 + 3 ^ 40 * 1527488 * 2
def baseEnd_1527488 : Nat := 174296786216672206638937

theorem tailTrace_1527488 : CollatzResearch.WordTrace tailWord_1527488 prefixEnd_1527488 174296786216672206638937 := by
  unfold tailWord_1527488
  simp only [CollatzResearch.WordTrace]
  refine ⟨27856032145089662513127559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37141376193452883350836745 27856032145089662513127559)
  ·
    refine ⟨41784048217634493769691339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27856032145089662513127559 41784048217634493769691339)
    ·
      refine ⟨62676072326451740654537009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41784048217634493769691339 62676072326451740654537009)
      ·
        refine ⟨47007054244838805490902757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62676072326451740654537009 47007054244838805490902757)
        ·
          refine ⟨8813822670907276029544267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47007054244838805490902757 8813822670907276029544267)
          ·
            refine ⟨13220734006360914044316401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8813822670907276029544267 13220734006360914044316401)
            ·
              refine ⟨9915550504770685533237301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13220734006360914044316401 9915550504770685533237301)
              ·
                refine ⟨929582859822251768740997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9915550504770685533237301 929582859822251768740997)
                ·
                  refine ⟨174296786216672206638937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 929582859822251768740997 174296786216672206638937)
                  ·
                    rfl

theorem cell22_1527488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 4].length) (baseStart_1527488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527488 prefixEnd_1527488 := by exact prefixLift 1527488
  have htrace : WordTrace (prefixWord ++ tailWord_1527488) baseStart_1527488 baseEnd_1527488 := by
    simpa [prefixWord, tailWord_1527488, baseEnd_1527488] using wordTrace_append hprefix tailTrace_1527488
  have hstable : (prefixWord ++ tailWord_1527488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527488).length < 2 ^ (prefixWord ++ tailWord_1527488).sum := by decide
  have hdescent : baseEnd_1527488 < baseStart_1527488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527505 : List Nat := [1, 2, 2, 1, 2, 4, 4, 2, 4]
def baseStart_1527505 : Nat := 118140960795 + 1527505 * 2 ^ 59
def prefixEnd_1527505 : Nat := 4983230072969 + 3 ^ 40 * 1527505 * 2
def baseEnd_1527505 : Nat := 174298726032478080747253

theorem tailTrace_1527505 : CollatzResearch.WordTrace tailWord_1527505 prefixEnd_1527505 174298726032478080747253 := by
  unfold tailWord_1527505
  simp only [CollatzResearch.WordTrace]
  refine ⟨55712684331117736929623969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37141789554078491286415979 55712684331117736929623969)
  ·
    refine ⟨41784513248338302697217977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55712684331117736929623969 41784513248338302697217977)
    ·
      refine ⟨31338384936253727022913483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41784513248338302697217977 31338384936253727022913483)
      ·
        refine ⟨47007577404380590534370225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31338384936253727022913483 47007577404380590534370225)
        ·
          refine ⟨35255683053285442900777669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47007577404380590534370225 35255683053285442900777669)
          ·
            refine ⟨6610440572491020543895813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35255683053285442900777669 6610440572491020543895813)
            ·
              refine ⟨1239457607342066351980465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6610440572491020543895813 1239457607342066351980465)
              ·
                refine ⟨929593205506549763985349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239457607342066351980465 929593205506549763985349)
                ·
                  refine ⟨174298726032478080747253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 929593205506549763985349 174298726032478080747253)
                  ·
                    rfl

theorem cell22_1527505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 2, 4].length) (baseStart_1527505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527505 prefixEnd_1527505 := by exact prefixLift 1527505
  have htrace : WordTrace (prefixWord ++ tailWord_1527505) baseStart_1527505 baseEnd_1527505 := by
    simpa [prefixWord, tailWord_1527505, baseEnd_1527505] using wordTrace_append hprefix tailTrace_1527505
  have hstable : (prefixWord ++ tailWord_1527505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527505).length < 2 ^ (prefixWord ++ tailWord_1527505).sum := by decide
  have hdescent : baseEnd_1527505 < baseStart_1527505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527548 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 5, 3]
def baseStart_1527548 : Nat := 118140960795 + 1527548 * 2 ^ 59
def prefixEnd_1527548 : Nat := 4983230072969 + 3 ^ 40 * 1527548 * 2
def baseEnd_1527548 : Nat := 522910897876196463416627

theorem tailTrace_1527548 : CollatzResearch.WordTrace tailWord_1527548 prefixEnd_1527548 522910897876196463416627 := by
  unfold tailWord_1527548
  simp only [CollatzResearch.WordTrace]
  refine ⟨27857126334980977636719649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37142835113307970182292865 27857126334980977636719649)
  ·
    refine ⟨20892844751235733227539737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27857126334980977636719649 20892844751235733227539737)
    ·
      refine ⟨15669633563426799920654803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20892844751235733227539737 15669633563426799920654803)
      ·
        refine ⟨23504450345140199880982205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15669633563426799920654803 23504450345140199880982205)
        ·
          refine ⟨8814168879427574955368327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23504450345140199880982205 8814168879427574955368327)
          ·
            refine ⟨13221253319141362433052491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8814168879427574955368327 13221253319141362433052491)
            ·
              refine ⟨19831879978712043649578737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13221253319141362433052491 19831879978712043649578737)
              ·
                refine ⟨14873909984034032737184053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19831879978712043649578737 14873909984034032737184053)
                ·
                  refine ⟨1394429061003190569111005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14873909984034032737184053 1394429061003190569111005)
                  ·
                    refine ⟨522910897876196463416627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394429061003190569111005 522910897876196463416627)
                    ·
                      rfl

theorem cell22_1527548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_1527548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527548 prefixEnd_1527548 := by exact prefixLift 1527548
  have htrace : WordTrace (prefixWord ++ tailWord_1527548) baseStart_1527548 baseEnd_1527548 := by
    simpa [prefixWord, tailWord_1527548, baseEnd_1527548] using wordTrace_append hprefix tailTrace_1527548
  have hstable : (prefixWord ++ tailWord_1527548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527548).length < 2 ^ (prefixWord ++ tailWord_1527548).sum := by decide
  have hdescent : baseEnd_1527548 < baseStart_1527548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527623 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 6]
def baseStart_1527623 : Nat := 118140960795 + 1527623 * 2 ^ 59
def prefixEnd_1527623 : Nat := 4983230072969 + 3 ^ 40 * 1527623 * 2
def baseEnd_1527623 : Nat := 174312190636307089263799

theorem tailTrace_1527623 : CollatzResearch.WordTrace tailWord_1527623 prefixEnd_1527623 174312190636307089263799 := by
  unfold tailWord_1527623
  simp only [CollatzResearch.WordTrace]
  refine ⟨55716988144690243082419523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37144658763126828721613015 55716988144690243082419523)
  ·
    refine ⟨83575482217035364623629285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55716988144690243082419523 83575482217035364623629285)
    ·
      refine ⟨15670402915694130866930491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83575482217035364623629285 15670402915694130866930491)
      ·
        refine ⟨23505604373541196300395737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15670402915694130866930491 23505604373541196300395737)
        ·
          refine ⟨17629203280155897225296803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23505604373541196300395737 17629203280155897225296803)
          ·
            refine ⟨26443804920233845837945205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17629203280155897225296803 26443804920233845837945205)
            ·
              refine ⟨2479106711271923047307363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26443804920233845837945205 2479106711271923047307363)
              ·
                refine ⟨3718660066907884570961045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479106711271923047307363 3718660066907884570961045)
                ·
                  refine ⟨174312190636307089263799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3718660066907884570961045 174312190636307089263799)
                  ·
                    rfl

theorem cell22_1527623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 6].length) (baseStart_1527623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527623 prefixEnd_1527623 := by exact prefixLift 1527623
  have htrace : WordTrace (prefixWord ++ tailWord_1527623) baseStart_1527623 baseEnd_1527623 := by
    simpa [prefixWord, tailWord_1527623, baseEnd_1527623] using wordTrace_append hprefix tailTrace_1527623
  have hstable : (prefixWord ++ tailWord_1527623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527623).length < 2 ^ (prefixWord ++ tailWord_1527623).sum := by decide
  have hdescent : baseEnd_1527623 < baseStart_1527623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527629 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 5]
def baseStart_1527629 : Nat := 118140960795 + 1527629 * 2 ^ 59
def prefixEnd_1527629 : Nat := 4983230072969 + 3 ^ 40 * 1527629 * 2
def baseEnd_1527629 : Nat := 174312875277179750713793

theorem tailTrace_1527629 : CollatzResearch.WordTrace tailWord_1527629 prefixEnd_1527629 174312875277179750713793 := by
  unfold tailWord_1527629
  simp only [CollatzResearch.WordTrace]
  refine ⟨55717206982668506107137941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37144804655112337404758627 55717206982668506107137941)
  ·
    refine ⟨2611744077312586223772091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55717206982668506107137941 2611744077312586223772091)
    ·
      refine ⟨3917616115968879335658137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2611744077312586223772091 3917616115968879335658137)
      ·
        refine ⟨2938212086976659501743603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917616115968879335658137 2938212086976659501743603)
        ·
          refine ⟨4407318130464989252615405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2938212086976659501743603 4407318130464989252615405)
          ·
            refine ⟨1652744298924370969730777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4407318130464989252615405 1652744298924370969730777)
            ·
              refine ⟨1239558224193278227298083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1652744298924370969730777 1239558224193278227298083)
              ·
                refine ⟨1859337336289917340947125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239558224193278227298083 1859337336289917340947125)
                ·
                  refine ⟨174312875277179750713793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859337336289917340947125 174312875277179750713793)
                  ·
                    rfl

theorem cell22_1527629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_1527629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527629 prefixEnd_1527629 := by exact prefixLift 1527629
  have htrace : WordTrace (prefixWord ++ tailWord_1527629) baseStart_1527629 baseEnd_1527629 := by
    simpa [prefixWord, tailWord_1527629, baseEnd_1527629] using wordTrace_append hprefix tailTrace_1527629
  have hstable : (prefixWord ++ tailWord_1527629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527629).length < 2 ^ (prefixWord ++ tailWord_1527629).sum := by decide
  have hdescent : baseEnd_1527629 < baseStart_1527629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527704 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 2, 4]
def baseStart_1527704 : Nat := 118140960795 + 1527704 * 2 ^ 59
def prefixEnd_1527704 : Nat := 4983230072969 + 3 ^ 40 * 1527704 * 2
def baseEnd_1527704 : Nat := 522964299864264056516149

theorem tailTrace_1527704 : CollatzResearch.WordTrace tailWord_1527704 prefixEnd_1527704 522964299864264056516149 := by
  unfold tailWord_1527704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27859971228698396958059083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37146628304931195944078777 27859971228698396958059083)
  ·
    refine ⟨41789956843047595437088625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27859971228698396958059083 41789956843047595437088625)
    ·
      refine ⟨31342467632285696577816469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41789956843047595437088625 31342467632285696577816469)
      ·
        refine ⟨1469178170263392027085147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31342467632285696577816469 1469178170263392027085147)
        ·
          refine ⟨2203767255395088040627721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469178170263392027085147 2203767255395088040627721)
          ·
            refine ⟨1652825441546316030470791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2203767255395088040627721 1652825441546316030470791)
            ·
              refine ⟨2479238162319474045706187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652825441546316030470791 2479238162319474045706187)
              ·
                refine ⟨3718857243479211068559281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479238162319474045706187 3718857243479211068559281)
                ·
                  refine ⟨2789142932609408301419461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3718857243479211068559281 2789142932609408301419461)
                  ·
                    refine ⟨522964299864264056516149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789142932609408301419461 522964299864264056516149)
                    ·
                      rfl

theorem cell22_1527704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_1527704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527704 prefixEnd_1527704 := by exact prefixLift 1527704
  have htrace : WordTrace (prefixWord ++ tailWord_1527704) baseStart_1527704 baseEnd_1527704 := by
    simpa [prefixWord, tailWord_1527704, baseEnd_1527704] using wordTrace_append hprefix tailTrace_1527704
  have hstable : (prefixWord ++ tailWord_1527704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527704).length < 2 ^ (prefixWord ++ tailWord_1527704).sum := by decide
  have hdescent : baseEnd_1527704 < baseStart_1527704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527760 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 1, 4]
def baseStart_1527760 : Nat := 118140960795 + 1527760 * 2 ^ 59
def prefixEnd_1527760 : Nat := 4983230072969 + 3 ^ 40 * 1527760 * 2
def baseEnd_1527760 : Nat := 522983469808698577115977

theorem tailTrace_1527760 : CollatzResearch.WordTrace tailWord_1527760 prefixEnd_1527760 522983469808698577115977 := by
  unfold tailWord_1527760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27860992472596957740078367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37147989963462610320104489 27860992472596957740078367)
  ·
    refine ⟨41791488708895436610117551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27860992472596957740078367 41791488708895436610117551)
    ·
      refine ⟨62687233063343154915176327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41791488708895436610117551 62687233063343154915176327)
      ·
        refine ⟨94030849595014732372764491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62687233063343154915176327 94030849595014732372764491)
        ·
          refine ⟨141046274392522098559146737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94030849595014732372764491 141046274392522098559146737)
          ·
            refine ⟨105784705794391573919360053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141046274392522098559146737 105784705794391573919360053)
            ·
              refine ⟨9917316168224210054940005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105784705794391573919360053 9917316168224210054940005)
              ·
                refine ⟨1859496781542039385301251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9917316168224210054940005 1859496781542039385301251)
                ·
                  refine ⟨2789245172313059077951877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859496781542039385301251 2789245172313059077951877)
                  ·
                    refine ⟨522983469808698577115977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789245172313059077951877 522983469808698577115977)
                    ·
                      rfl

theorem cell22_1527760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_1527760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527760 prefixEnd_1527760 := by exact prefixLift 1527760
  have htrace : WordTrace (prefixWord ++ tailWord_1527760) baseStart_1527760 baseEnd_1527760 := by
    simpa [prefixWord, tailWord_1527760, baseEnd_1527760] using wordTrace_append hprefix tailTrace_1527760
  have hstable : (prefixWord ++ tailWord_1527760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527760).length < 2 ^ (prefixWord ++ tailWord_1527760).sum := by decide
  have hdescent : baseEnd_1527760 < baseStart_1527760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527803 : List Nat := [1, 1, 1, 1, 1, 3, 5, 9]
def baseStart_1527803 : Nat := 118140960795 + 1527803 * 2 ^ 59
def prefixEnd_1527803 : Nat := 4983230072969 + 3 ^ 40 * 1527803 * 2
def baseEnd_1527803 : Nat := 58110909954162310921205

theorem tailTrace_1527803 : CollatzResearch.WordTrace tailWord_1527803 prefixEnd_1527803 58110909954162310921205 := by
  unfold tailWord_1527803
  simp only [CollatzResearch.WordTrace]
  refine ⟨55723553284038133823972063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37149035522692089215981375 55723553284038133823972063)
  ·
    refine ⟨83585329926057200735958095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55723553284038133823972063 83585329926057200735958095)
    ·
      refine ⟨125377994889085801103937143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83585329926057200735958095 125377994889085801103937143)
      ·
        refine ⟨188066992333628701655905715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125377994889085801103937143 188066992333628701655905715)
        ·
          refine ⟨282100488500443052483858573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188066992333628701655905715 282100488500443052483858573)
          ·
            refine ⟨105787683187666144681446965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 282100488500443052483858573 105787683187666144681446965)
            ·
              refine ⟨9917595298843701063885653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105787683187666144681446965 9917595298843701063885653)
              ·
                refine ⟨58110909954162310921205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9917595298843701063885653 58110909954162310921205)
                ·
                  rfl

theorem cell22_1527803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 9].length) (baseStart_1527803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527803 prefixEnd_1527803 := by exact prefixLift 1527803
  have htrace : WordTrace (prefixWord ++ tailWord_1527803) baseStart_1527803 baseEnd_1527803 := by
    simpa [prefixWord, tailWord_1527803, baseEnd_1527803] using wordTrace_append hprefix tailTrace_1527803
  have hstable : (prefixWord ++ tailWord_1527803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527803).length < 2 ^ (prefixWord ++ tailWord_1527803).sum := by decide
  have hdescent : baseEnd_1527803 < baseStart_1527803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527822 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1527822 : Nat := 118140960795 + 1527822 * 2 ^ 59
def prefixEnd_1527822 : Nat := 4983230072969 + 3 ^ 40 * 1527822 * 2
def baseEnd_1527822 : Nat := 523004693675751082065787

theorem tailTrace_1527822 : CollatzResearch.WordTrace tailWord_1527822 prefixEnd_1527822 523004693675751082065787 := by
  unfold tailWord_1527822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965530783871162508614215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37149497513979533379275813 6965530783871162508614215)
  ·
    refine ⟨10448296175806743762921323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6965530783871162508614215 10448296175806743762921323)
    ·
      refine ⟨15672444263710115644381985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448296175806743762921323 15672444263710115644381985)
      ·
        refine ⟨11754333197782586733286489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15672444263710115644381985 11754333197782586733286489)
        ·
          refine ⟨8815749898336940049964867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11754333197782586733286489 8815749898336940049964867)
          ·
            refine ⟨13223624847505410074947301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8815749898336940049964867 13223624847505410074947301)
            ·
              refine ⟨2479429658907264389052619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13223624847505410074947301 2479429658907264389052619)
              ·
                refine ⟨3719144488360896583578929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2479429658907264389052619 3719144488360896583578929)
                ·
                  refine ⟨2789358366270672437684197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3719144488360896583578929 2789358366270672437684197)
                  ·
                    refine ⟨523004693675751082065787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789358366270672437684197 523004693675751082065787)
                    ·
                      rfl

theorem cell22_1527822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1527822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527822 prefixEnd_1527822 := by exact prefixLift 1527822
  have htrace : WordTrace (prefixWord ++ tailWord_1527822) baseStart_1527822 baseEnd_1527822 := by
    simpa [prefixWord, tailWord_1527822, baseEnd_1527822] using wordTrace_append hprefix tailTrace_1527822
  have hstable : (prefixWord ++ tailWord_1527822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527822).length < 2 ^ (prefixWord ++ tailWord_1527822).sum := by decide
  have hdescent : baseEnd_1527822 < baseStart_1527822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527828 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_1527828 : Nat := 118140960795 + 1527828 * 2 ^ 59
def prefixEnd_1527828 : Nat := 4983230072969 + 3 ^ 40 * 1527828 * 2
def baseEnd_1527828 : Nat := 523006747598369066415769

theorem tailTrace_1527828 : CollatzResearch.WordTrace tailWord_1527828 prefixEnd_1527828 523006747598369066415769 := by
  unfold tailWord_1527828
  simp only [CollatzResearch.WordTrace]
  refine ⟨27862232554473781546816069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37149643405965042062421425 27862232554473781546816069)
  ·
    refine ⟨5224168603963834040028013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27862232554473781546816069 5224168603963834040028013)
    ·
      refine ⟨1959063226486437765010505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5224168603963834040028013 1959063226486437765010505)
      ·
        refine ⟨1469297419864828323757879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959063226486437765010505 1469297419864828323757879)
        ·
          refine ⟨2203946129797242485636819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469297419864828323757879 2203946129797242485636819)
          ·
            refine ⟨3305919194695863728455229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203946129797242485636819 3305919194695863728455229)
            ·
              refine ⟨1239719698010948898170711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3305919194695863728455229 1239719698010948898170711)
              ·
                refine ⟨1859579547016423347256067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239719698010948898170711 1859579547016423347256067)
                ·
                  refine ⟨2789369320524635020884101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859579547016423347256067 2789369320524635020884101)
                  ·
                    refine ⟨523006747598369066415769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789369320524635020884101 523006747598369066415769)
                    ·
                      rfl

theorem cell22_1527828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_1527828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527828 prefixEnd_1527828 := by exact prefixLift 1527828
  have htrace : WordTrace (prefixWord ++ tailWord_1527828) baseStart_1527828 baseEnd_1527828 := by
    simpa [prefixWord, tailWord_1527828, baseEnd_1527828] using wordTrace_append hprefix tailTrace_1527828
  have hstable : (prefixWord ++ tailWord_1527828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527828).length < 2 ^ (prefixWord ++ tailWord_1527828).sum := by decide
  have hdescent : baseEnd_1527828 < baseStart_1527828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527835 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 7, 3]
def baseStart_1527835 : Nat := 118140960795 + 1527835 * 2 ^ 59
def prefixEnd_1527835 : Nat := 4983230072969 + 3 ^ 40 * 1527835 * 2
def baseEnd_1527835 : Nat := 523009143841423381490747

theorem tailTrace_1527835 : CollatzResearch.WordTrace tailWord_1527835 prefixEnd_1527835 523009143841423381490747 := by
  unfold tailWord_1527835
  simp only [CollatzResearch.WordTrace]
  refine ⟨55724720419922203289136959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37149813613281468859424639 55724720419922203289136959)
  ·
    refine ⟨83587080629883304933705439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55724720419922203289136959 83587080629883304933705439)
    ·
      refine ⟨125380620944824957400558159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83587080629883304933705439 125380620944824957400558159)
      ·
        refine ⟨188070931417237436100837239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125380620944824957400558159 188070931417237436100837239)
        ·
          refine ⟨282106397125856154151255859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188070931417237436100837239 282106397125856154151255859)
          ·
            refine ⟨423159595688784231226883789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282106397125856154151255859 423159595688784231226883789)
            ·
              refine ⟨158684848383294086710081421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 423159595688784231226883789 158684848383294086710081421)
              ·
                refine ⟨59506818143735282516280533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158684848383294086710081421 59506818143735282516280533)
                ·
                  refine ⟨1394691050243795683975325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 59506818143735282516280533 1394691050243795683975325)
                  ·
                    refine ⟨523009143841423381490747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394691050243795683975325 523009143841423381490747)
                    ·
                      rfl

theorem cell22_1527835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 7, 3].length) (baseStart_1527835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527835 prefixEnd_1527835 := by exact prefixLift 1527835
  have htrace : WordTrace (prefixWord ++ tailWord_1527835) baseStart_1527835 baseEnd_1527835 := by
    simpa [prefixWord, tailWord_1527835, baseEnd_1527835] using wordTrace_append hprefix tailTrace_1527835
  have hstable : (prefixWord ++ tailWord_1527835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527835).length < 2 ^ (prefixWord ++ tailWord_1527835).sum := by decide
  have hdescent : baseEnd_1527835 < baseStart_1527835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527886 : List Nat := [4, 1, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_1527886 : Nat := 118140960795 + 1527886 * 2 ^ 59
def prefixEnd_1527886 : Nat := 4983230072969 + 3 ^ 40 * 1527886 * 2
def baseEnd_1527886 : Nat := 523026602183676248465591

theorem tailTrace_1527886 : CollatzResearch.WordTrace tailWord_1527886 prefixEnd_1527886 523026602183676248465591 := by
  unfold tailWord_1527886
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965822567842179874905439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37151053695158292666162341 6965822567842179874905439)
  ·
    refine ⟨10448733851763269812358159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6965822567842179874905439 10448733851763269812358159)
    ·
      refine ⟨15673100777644904718537239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10448733851763269812358159 15673100777644904718537239)
      ·
        refine ⟨23509651166467357077805859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15673100777644904718537239 23509651166467357077805859)
        ·
          refine ⟨35264476749701035616708789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23509651166467357077805859 35264476749701035616708789)
          ·
            refine ⟨3306044695284472089066449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35264476749701035616708789 3306044695284472089066449)
            ·
              refine ⟨2479533521463354066799837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306044695284472089066449 2479533521463354066799837)
              ·
                refine ⟨929825070548757775049939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479533521463354066799837 929825070548757775049939)
                ·
                  refine ⟨1394737605823136662574909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929825070548757775049939 1394737605823136662574909)
                  ·
                    refine ⟨523026602183676248465591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394737605823136662574909 523026602183676248465591)
                    ·
                      rfl

theorem cell22_1527886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_1527886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527886 prefixEnd_1527886 := by exact prefixLift 1527886
  have htrace : WordTrace (prefixWord ++ tailWord_1527886) baseStart_1527886 baseEnd_1527886 := by
    simpa [prefixWord, tailWord_1527886, baseEnd_1527886] using wordTrace_append hprefix tailTrace_1527886
  have hstable : (prefixWord ++ tailWord_1527886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527886).length < 2 ^ (prefixWord ++ tailWord_1527886).sum := by decide
  have hdescent : baseEnd_1527886 < baseStart_1527886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527929 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 1, 4]
def baseStart_1527929 : Nat := 118140960795 + 1527929 * 2 ^ 59
def prefixEnd_1527929 : Nat := 4983230072969 + 3 ^ 40 * 1527929 * 2
def baseEnd_1527929 : Nat := 523041321962438469640459

theorem tailTrace_1527929 : CollatzResearch.WordTrace tailWord_1527929 prefixEnd_1527929 523041321962438469640459 := by
  unfold tailWord_1527929
  simp only [CollatzResearch.WordTrace]
  refine ⟨55728148881581657343058841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37152099254387771562039227 55728148881581657343058841)
  ·
    refine ⟨41796111661186243007294131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55728148881581657343058841 41796111661186243007294131)
    ·
      refine ⟨62694167491779364510941197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41796111661186243007294131 62694167491779364510941197)
      ·
        refine ⟨23510312809417261691602949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62694167491779364510941197 23510312809417261691602949)
        ·
          refine ⟨4408183651765736567175553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23510312809417261691602949 4408183651765736567175553)
          ·
            refine ⟨3306137738824302425381665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4408183651765736567175553 3306137738824302425381665)
            ·
              refine ⟨2479603304118226819036249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3306137738824302425381665 2479603304118226819036249)
              ·
                refine ⟨1859702478088670114277187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479603304118226819036249 1859702478088670114277187)
                ·
                  refine ⟨2789553717133005171415781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1859702478088670114277187 2789553717133005171415781)
                  ·
                    refine ⟨523041321962438469640459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789553717133005171415781 523041321962438469640459)
                    ·
                      rfl

theorem cell22_1527929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 4].length) (baseStart_1527929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527929 prefixEnd_1527929 := by exact prefixLift 1527929
  have htrace : WordTrace (prefixWord ++ tailWord_1527929) baseStart_1527929 baseEnd_1527929 := by
    simpa [prefixWord, tailWord_1527929, baseEnd_1527929] using wordTrace_append hprefix tailTrace_1527929
  have hstable : (prefixWord ++ tailWord_1527929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527929).length < 2 ^ (prefixWord ++ tailWord_1527929).sum := by decide
  have hdescent : baseEnd_1527929 < baseStart_1527929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527957 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 2, 4]
def baseStart_1527957 : Nat := 118140960795 + 1527957 * 2 ^ 59
def prefixEnd_1527957 : Nat := 4983230072969 + 3 ^ 40 * 1527957 * 2
def baseEnd_1527957 : Nat := 523050906934655729940373

theorem tailTrace_1527957 : CollatzResearch.WordTrace tailWord_1527957 prefixEnd_1527957 523050906934655729940373 := by
  unfold tailWord_1527957
  simp only [CollatzResearch.WordTrace]
  refine ⟨55729170125480218125078125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37152780083653478750052083 55729170125480218125078125)
  ·
    refine ⟨20898438797055081796904297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55729170125480218125078125 20898438797055081796904297)
    ·
      refine ⟨15673829097791311347678223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20898438797055081796904297 15673829097791311347678223)
      ·
        refine ⟨23510743646686967021517335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15673829097791311347678223 23510743646686967021517335)
        ·
          refine ⟨35266115470030450532276003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23510743646686967021517335 35266115470030450532276003)
          ·
            refine ⟨52899173205045675798414005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35266115470030450532276003 52899173205045675798414005)
            ·
              refine ⟨4959297487973032106101313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52899173205045675798414005 4959297487973032106101313)
              ·
                refine ⟨3719473115979774079575985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4959297487973032106101313 3719473115979774079575985)
                ·
                  refine ⟨2789604836984830559681989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3719473115979774079575985 2789604836984830559681989)
                  ·
                    refine ⟨523050906934655729940373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789604836984830559681989 523050906934655729940373)
                    ·
                      rfl

theorem cell22_1527957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_1527957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527957 prefixEnd_1527957 := by exact prefixLift 1527957
  have htrace : WordTrace (prefixWord ++ tailWord_1527957) baseStart_1527957 baseEnd_1527957 := by
    simpa [prefixWord, tailWord_1527957, baseEnd_1527957] using wordTrace_append hprefix tailTrace_1527957
  have hstable : (prefixWord ++ tailWord_1527957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527957).length < 2 ^ (prefixWord ++ tailWord_1527957).sum := by decide
  have hdescent : baseEnd_1527957 < baseStart_1527957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1527987 : List Nat := [1, 1, 1, 2, 3, 2, 1, 3, 5, 3]
def baseStart_1527987 : Nat := 118140960795 + 1527987 * 2 ^ 59
def prefixEnd_1527987 : Nat := 4983230072969 + 3 ^ 40 * 1527987 * 2
def baseEnd_1527987 : Nat := 523061176547745651690281

theorem tailTrace_1527987 : CollatzResearch.WordTrace tailWord_1527987 prefixEnd_1527987 523061176547745651690281 := by
  unfold tailWord_1527987
  simp only [CollatzResearch.WordTrace]
  refine ⟨55730264315371533248670215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37153509543581022165780143 55730264315371533248670215)
  ·
    refine ⟨83595396473057299873005323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55730264315371533248670215 83595396473057299873005323)
    ·
      refine ⟨125393094709585949809507985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83595396473057299873005323 125393094709585949809507985)
      ·
        refine ⟨94044821032189462357130989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125393094709585949809507985 94044821032189462357130989)
        ·
          refine ⟨35266807887071048383924121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94044821032189462357130989 35266807887071048383924121)
          ·
            refine ⟨26450105915303286287943091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35266807887071048383924121 26450105915303286287943091)
            ·
              refine ⟨39675158872954929431914637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26450105915303286287943091 39675158872954929431914637)
              ·
                refine ⟨14878184577358098536967989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39675158872954929431914637 14878184577358098536967989)
                ·
                  refine ⟨1394829804127321737840749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14878184577358098536967989 1394829804127321737840749)
                  ·
                    refine ⟨523061176547745651690281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394829804127321737840749 523061176547745651690281)
                    ·
                      rfl

theorem cell22_1527987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 3, 5, 3].length) (baseStart_1527987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1527987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1527987 prefixEnd_1527987 := by exact prefixLift 1527987
  have htrace : WordTrace (prefixWord ++ tailWord_1527987) baseStart_1527987 baseEnd_1527987 := by
    simpa [prefixWord, tailWord_1527987, baseEnd_1527987] using wordTrace_append hprefix tailTrace_1527987
  have hstable : (prefixWord ++ tailWord_1527987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1527987).length < 2 ^ (prefixWord ++ tailWord_1527987).sum := by decide
  have hdescent : baseEnd_1527987 < baseStart_1527987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1527987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528017 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 5]
def baseStart_1528017 : Nat := 118140960795 + 1528017 * 2 ^ 59
def prefixEnd_1528017 : Nat := 4983230072969 + 3 ^ 40 * 1528017 * 2
def baseEnd_1528017 : Nat := 174357148720278524480063

theorem tailTrace_1528017 : CollatzResearch.WordTrace tailWord_1528017 prefixEnd_1528017 174357148720278524480063 := by
  unfold tailWord_1528017
  simp only [CollatzResearch.WordTrace]
  refine ⟨55731358505262848372262305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37154239003508565581508203 55731358505262848372262305)
  ·
    refine ⟨41798518878947136279196729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55731358505262848372262305 41798518878947136279196729)
    ·
      refine ⟨31348889159210352209397547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41798518878947136279196729 31348889159210352209397547)
      ·
        refine ⟨47023333738815528314096321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31348889159210352209397547 47023333738815528314096321)
        ·
          refine ⟨35267500304111646235572241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47023333738815528314096321 35267500304111646235572241)
          ·
            refine ⟨26450625228083734676679181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35267500304111646235572241 26450625228083734676679181)
            ·
              refine ⟨9918984460531400503754693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26450625228083734676679181 9918984460531400503754693)
              ·
                refine ⟨1859809586349637594454005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9918984460531400503754693 1859809586349637594454005)
                ·
                  refine ⟨174357148720278524480063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859809586349637594454005 174357148720278524480063)
                  ·
                    rfl

theorem cell22_1528017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 5].length) (baseStart_1528017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528017 prefixEnd_1528017 := by exact prefixLift 1528017
  have htrace : WordTrace (prefixWord ++ tailWord_1528017) baseStart_1528017 baseEnd_1528017 := by
    simpa [prefixWord, tailWord_1528017, baseEnd_1528017] using wordTrace_append hprefix tailTrace_1528017
  have hstable : (prefixWord ++ tailWord_1528017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528017).length < 2 ^ (prefixWord ++ tailWord_1528017).sum := by decide
  have hdescent : baseEnd_1528017 < baseStart_1528017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528032 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 2, 5]
def baseStart_1528032 : Nat := 118140960795 + 1528032 * 2 ^ 59
def prefixEnd_1528032 : Nat := 4983230072969 + 3 ^ 40 * 1528032 * 2
def baseEnd_1528032 : Nat := 523076580967380534315143

theorem tailTrace_1528032 : CollatzResearch.WordTrace tailWord_1528032 prefixEnd_1528032 523076580967380534315143 := by
  unfold tailWord_1528032
  simp only [CollatzResearch.WordTrace]
  refine ⟨27865952800104252967029175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37154603733472337289372233 27865952800104252967029175)
  ·
    refine ⟨41798929200156379450543763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27865952800104252967029175 41798929200156379450543763)
    ·
      refine ⟨62698393800234569175815645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41798929200156379450543763 62698393800234569175815645)
      ·
        refine ⟨23511897675087963440930867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62698393800234569175815645 23511897675087963440930867)
        ·
          refine ⟨35267846512631945161396301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23511897675087963440930867 35267846512631945161396301)
          ·
            refine ⟨13225442442236979435523613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35267846512631945161396301 13225442442236979435523613)
            ·
              refine ⟨4959540915838867288321355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13225442442236979435523613 4959540915838867288321355)
              ·
                refine ⟨7439311373758300932482033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959540915838867288321355 7439311373758300932482033)
                ·
                  refine ⟨5579483530318725699361525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7439311373758300932482033 5579483530318725699361525)
                  ·
                    refine ⟨523076580967380534315143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5579483530318725699361525 523076580967380534315143)
                    ·
                      rfl

theorem cell22_1528032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_1528032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528032 prefixEnd_1528032 := by exact prefixLift 1528032
  have htrace : WordTrace (prefixWord ++ tailWord_1528032) baseStart_1528032 baseEnd_1528032 := by
    simpa [prefixWord, tailWord_1528032, baseEnd_1528032] using wordTrace_append hprefix tailTrace_1528032
  have hstable : (prefixWord ++ tailWord_1528032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528032).length < 2 ^ (prefixWord ++ tailWord_1528032).sum := by decide
  have hdescent : baseEnd_1528032 < baseStart_1528032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528068 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 5]
def baseStart_1528068 : Nat := 118140960795 + 1528068 * 2 ^ 59
def prefixEnd_1528068 : Nat := 4983230072969 + 3 ^ 40 * 1528068 * 2
def baseEnd_1528068 : Nat := 174362968167696146805011

theorem tailTrace_1528068 : CollatzResearch.WordTrace tailWord_1528068 prefixEnd_1528068 174362968167696146805011 := by
  unfold tailWord_1528068
  simp only [CollatzResearch.WordTrace]
  refine ⟨27866609314039042041184429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37155479085385389388245905 27866609314039042041184429)
  ·
    refine ⟨10449978492764640765444161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27866609314039042041184429 10449978492764640765444161)
    ·
      refine ⟨7837483869573480574083121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10449978492764640765444161 7837483869573480574083121)
      ·
        refine ⟨5878112902180110430562341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7837483869573480574083121 5878112902180110430562341)
        ·
          refine ⟨1102146169158770705730439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5878112902180110430562341 1102146169158770705730439)
          ·
            refine ⟨1653219253738156058595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102146169158770705730439 1653219253738156058595659)
            ·
              refine ⟨2479828880607234087893489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653219253738156058595659 2479828880607234087893489)
              ·
                refine ⟨1859871660455425565920117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2479828880607234087893489 1859871660455425565920117)
                ·
                  refine ⟨174362968167696146805011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1859871660455425565920117 174362968167696146805011)
                  ·
                    rfl

theorem cell22_1528068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_1528068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528068 prefixEnd_1528068 := by exact prefixLift 1528068
  have htrace : WordTrace (prefixWord ++ tailWord_1528068) baseStart_1528068 baseEnd_1528068 := by
    simpa [prefixWord, tailWord_1528068, baseEnd_1528068] using wordTrace_append hprefix tailTrace_1528068
  have hstable : (prefixWord ++ tailWord_1528068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528068).length < 2 ^ (prefixWord ++ tailWord_1528068).sum := by decide
  have hdescent : baseEnd_1528068 < baseStart_1528068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528113 : List Nat := [1, 2, 2, 3, 4, 2, 1, 3, 4]
def baseStart_1528113 : Nat := 118140960795 + 1528113 * 2 ^ 59
def prefixEnd_1528113 : Nat := 4983230072969 + 3 ^ 40 * 1528113 * 2
def baseEnd_1528113 : Nat := 174368102974241107679965

theorem tailTrace_1528113 : CollatzResearch.WordTrace tailWord_1528113 prefixEnd_1528113 174368102974241107679965 := by
  unfold tailWord_1528113
  simp only [CollatzResearch.WordTrace]
  refine ⟨55734859912915056767756993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37156573275276704511837995 55734859912915056767756993)
  ·
    refine ⟨41801144934686292575817745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55734859912915056767756993 41801144934686292575817745)
    ·
      refine ⟨31350858701014719431863309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41801144934686292575817745 31350858701014719431863309)
      ·
        refine ⟨11756572012880519786948741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31350858701014719431863309 11756572012880519786948741)
        ·
          refine ⟨2204357252415097460052889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11756572012880519786948741 2204357252415097460052889)
          ·
            refine ⟨1653267939311323095039667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204357252415097460052889 1653267939311323095039667)
            ·
              refine ⟨2479901908966984642559501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653267939311323095039667 2479901908966984642559501)
              ·
                refine ⟨929963215862619240959813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2479901908966984642559501 929963215862619240959813)
                ·
                  refine ⟨174368102974241107679965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 929963215862619240959813 174368102974241107679965)
                  ·
                    rfl

theorem cell22_1528113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 3, 4].length) (baseStart_1528113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528113 prefixEnd_1528113 := by exact prefixLift 1528113
  have htrace : WordTrace (prefixWord ++ tailWord_1528113) baseStart_1528113 baseEnd_1528113 := by
    simpa [prefixWord, tailWord_1528113, baseEnd_1528113] using wordTrace_append hprefix tailTrace_1528113
  have hstable : (prefixWord ++ tailWord_1528113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528113).length < 2 ^ (prefixWord ++ tailWord_1528113).sum := by decide
  have hdescent : baseEnd_1528113 < baseStart_1528113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528126 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_1528126 : Nat := 118140960795 + 1528126 * 2 ^ 59
def prefixEnd_1528126 : Nat := 4983230072969 + 3 ^ 40 * 1528126 * 2
def baseEnd_1528126 : Nat := 523108759088395622464855

theorem tailTrace_1528126 : CollatzResearch.WordTrace tailWord_1528126 prefixEnd_1528126 523108759088395622464855 := by
  unfold tailWord_1528126
  simp only [CollatzResearch.WordTrace]
  refine ⟨6966916757733494998497529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37156889374578639991986821 6966916757733494998497529)
  ·
    refine ⟨5225187568300121248873147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6966916757733494998497529 5225187568300121248873147)
    ·
      refine ⟨7837781352450181873309721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225187568300121248873147 7837781352450181873309721)
      ·
        refine ⟨5878336014337636404982291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7837781352450181873309721 5878336014337636404982291)
        ·
          refine ⟨8817504021506454607473437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878336014337636404982291 8817504021506454607473437)
          ·
            refine ⟨3306564008064920477802539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8817504021506454607473437 3306564008064920477802539)
            ·
              refine ⟨4959846012097380716703809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306564008064920477802539 4959846012097380716703809)
              ·
                refine ⟨3719884509073035537527857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4959846012097380716703809 3719884509073035537527857)
                ·
                  refine ⟨2789913381804776653145893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3719884509073035537527857 2789913381804776653145893)
                  ·
                    refine ⟨523108759088395622464855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2789913381804776653145893 523108759088395622464855)
                    ·
                      rfl

theorem cell22_1528126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_1528126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528126 prefixEnd_1528126 := by exact prefixLift 1528126
  have htrace : WordTrace (prefixWord ++ tailWord_1528126) baseStart_1528126 baseEnd_1528126 := by
    simpa [prefixWord, tailWord_1528126, baseEnd_1528126] using wordTrace_append hprefix tailTrace_1528126
  have hstable : (prefixWord ++ tailWord_1528126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528126).length < 2 ^ (prefixWord ++ tailWord_1528126).sum := by decide
  have hdescent : baseEnd_1528126 < baseStart_1528126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528137 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 2, 6]
def baseStart_1528137 : Nat := 118140960795 + 1528137 * 2 ^ 59
def prefixEnd_1528137 : Nat := 4983230072969 + 3 ^ 40 * 1528137 * 2
def baseEnd_1528137 : Nat := 523112524613195260439821

theorem tailTrace_1528137 : CollatzResearch.WordTrace tailWord_1528137 prefixEnd_1528137 523112524613195260439821 := by
  unfold tailWord_1528137
  simp only [CollatzResearch.WordTrace]
  refine ⟨55735735264828108866630665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37157156843218739244420443 55735735264828108866630665)
  ·
    refine ⟨41801801448621081649972999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55735735264828108866630665 41801801448621081649972999)
    ·
      refine ⟨62702702172931622474959499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41801801448621081649972999 62702702172931622474959499)
      ·
        refine ⟨94054053259397433712439249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62702702172931622474959499 94054053259397433712439249)
        ·
          refine ⟨70540539944548075284329437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94054053259397433712439249 70540539944548075284329437)
          ·
            refine ⟨26452702479205528231623539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70540539944548075284329437 26452702479205528231623539)
            ·
              refine ⟨39679053718808292347435309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26452702479205528231623539 39679053718808292347435309)
              ·
                refine ⟨14879645144553109630288241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39679053718808292347435309 14879645144553109630288241)
                ·
                  refine ⟨11159733858414832222716181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14879645144553109630288241 11159733858414832222716181)
                  ·
                    refine ⟨523112524613195260439821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11159733858414832222716181 523112524613195260439821)
                    ·
                      rfl

theorem cell22_1528137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_1528137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528137 prefixEnd_1528137 := by exact prefixLift 1528137
  have htrace : WordTrace (prefixWord ++ tailWord_1528137) baseStart_1528137 baseEnd_1528137 := by
    simpa [prefixWord, tailWord_1528137, baseEnd_1528137] using wordTrace_append hprefix tailTrace_1528137
  have hstable : (prefixWord ++ tailWord_1528137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528137).length < 2 ^ (prefixWord ++ tailWord_1528137).sum := by decide
  have hdescent : baseEnd_1528137 < baseStart_1528137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528139 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 3, 3]
def baseStart_1528139 : Nat := 118140960795 + 1528139 * 2 ^ 59
def prefixEnd_1528139 : Nat := 4983230072969 + 3 ^ 40 * 1528139 * 2
def baseEnd_1528139 : Nat := 523113209254067921889815

theorem tailTrace_1528139 : CollatzResearch.WordTrace tailWord_1528139 prefixEnd_1528139 523113209254067921889815 := by
  unfold tailWord_1528139
  simp only [CollatzResearch.WordTrace]
  refine ⟨55735808210820863208203471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37157205473880575472135647 55735808210820863208203471)
  ·
    refine ⟨83603712316231294812305207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55735808210820863208203471 83603712316231294812305207)
    ·
      refine ⟨125405568474346942218457811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83603712316231294812305207 125405568474346942218457811)
      ·
        refine ⟨188108352711520413327686717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125405568474346942218457811 188108352711520413327686717)
        ·
          refine ⟨70540632266820154997882519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188108352711520413327686717 70540632266820154997882519)
          ·
            refine ⟨105810948400230232496823779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70540632266820154997882519 105810948400230232496823779)
            ·
              refine ⟨158716422600345348745235669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105810948400230232496823779 158716422600345348745235669)
              ·
                refine ⟨3719916154695594111216461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158716422600345348745235669 3719916154695594111216461)
                ·
                  refine ⟨1394968558010847791706173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3719916154695594111216461 1394968558010847791706173)
                  ·
                    refine ⟨523113209254067921889815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394968558010847791706173 523113209254067921889815)
                    ·
                      rfl

theorem cell22_1528139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 3, 3].length) (baseStart_1528139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528139 prefixEnd_1528139 := by exact prefixLift 1528139
  have htrace : WordTrace (prefixWord ++ tailWord_1528139) baseStart_1528139 baseEnd_1528139 := by
    simpa [prefixWord, tailWord_1528139, baseEnd_1528139] using wordTrace_append hprefix tailTrace_1528139
  have hstable : (prefixWord ++ tailWord_1528139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528139).length < 2 ^ (prefixWord ++ tailWord_1528139).sum := by decide
  have hdescent : baseEnd_1528139 < baseStart_1528139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528152 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 9]
def baseStart_1528152 : Nat := 118140960795 + 1528152 * 2 ^ 59
def prefixEnd_1528152 : Nat := 4983230072969 + 3 ^ 40 * 1528152 * 2
def baseEnd_1528152 : Nat := 174372553139913407104925

theorem tailTrace_1528152 : CollatzResearch.WordTrace tailWord_1528152 prefixEnd_1528152 174372553139913407104925 := by
  unfold tailWord_1528152
  simp only [CollatzResearch.WordTrace]
  refine ⟨27868141179886883214213355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37157521573182510952284473 27868141179886883214213355)
  ·
    refine ⟨41802211769830324821320033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27868141179886883214213355 41802211769830324821320033)
    ·
      refine ⟨31351658827372743615990025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41802211769830324821320033 31351658827372743615990025)
      ·
        refine ⟨23513744120529557711992519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31351658827372743615990025 23513744120529557711992519)
        ·
          refine ⟨35270616180794336567988779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23513744120529557711992519 35270616180794336567988779)
          ·
            refine ⟨52905924271191504851983169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35270616180794336567988779 52905924271191504851983169)
            ·
              refine ⟨39679443203393628638987377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52905924271191504851983169 39679443203393628638987377)
              ·
                refine ⟨29759582402545221479240533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39679443203393628638987377 29759582402545221479240533)
                ·
                  refine ⟨174372553139913407104925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29759582402545221479240533 174372553139913407104925)
                  ·
                    rfl

theorem cell22_1528152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 9].length) (baseStart_1528152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528152 prefixEnd_1528152 := by exact prefixLift 1528152
  have htrace : WordTrace (prefixWord ++ tailWord_1528152) baseStart_1528152 baseEnd_1528152 := by
    simpa [prefixWord, tailWord_1528152, baseEnd_1528152] using wordTrace_append hprefix tailTrace_1528152
  have hstable : (prefixWord ++ tailWord_1528152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528152).length < 2 ^ (prefixWord ++ tailWord_1528152).sum := by decide
  have hdescent : baseEnd_1528152 < baseStart_1528152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528173 : List Nat := [1, 5, 1, 1, 1, 2, 2, 5, 1, 3]
def baseStart_1528173 : Nat := 118140960795 + 1528173 * 2 ^ 59
def prefixEnd_1528173 : Nat := 4983230072969 + 3 ^ 40 * 1528173 * 2
def baseEnd_1528173 : Nat := 523124848148903166539711

theorem tailTrace_1528173 : CollatzResearch.WordTrace tailWord_1528173 prefixEnd_1528173 523124848148903166539711 := by
  unfold tailWord_1528173
  simp only [CollatzResearch.WordTrace]
  refine ⟨55737048292697687014941173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37158032195131791343294115 55737048292697687014941173)
  ·
    refine ⟨5225348277440408157650735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55737048292697687014941173 5225348277440408157650735)
    ·
      refine ⟨7838022416160612236476103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225348277440408157650735 7838022416160612236476103)
      ·
        refine ⟨11757033624240918354714155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7838022416160612236476103 11757033624240918354714155)
        ·
          refine ⟨17635550436361377532071233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11757033624240918354714155 17635550436361377532071233)
          ·
            refine ⟨13226662827271033149053425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17635550436361377532071233 13226662827271033149053425)
            ·
              refine ⟨9919997120453274861790069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13226662827271033149053425 9919997120453274861790069)
              ·
                refine ⟨929999730042494518292819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9919997120453274861790069 929999730042494518292819)
                ·
                  refine ⟨1394999595063741777439229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 929999730042494518292819 1394999595063741777439229)
                  ·
                    refine ⟨523124848148903166539711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1394999595063741777439229 523124848148903166539711)
                    ·
                      rfl

theorem cell22_1528173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 5, 1, 3].length) (baseStart_1528173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528173 prefixEnd_1528173 := by exact prefixLift 1528173
  have htrace : WordTrace (prefixWord ++ tailWord_1528173) baseStart_1528173 baseEnd_1528173 := by
    simpa [prefixWord, tailWord_1528173, baseEnd_1528173] using wordTrace_append hprefix tailTrace_1528173
  have hstable : (prefixWord ++ tailWord_1528173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528173).length < 2 ^ (prefixWord ++ tailWord_1528173).sum := by decide
  have hdescent : baseEnd_1528173 < baseStart_1528173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528199 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1528199 : Nat := 118140960795 + 1528199 * 2 ^ 59
def prefixEnd_1528199 : Nat := 4983230072969 + 3 ^ 40 * 1528199 * 2
def baseEnd_1528199 : Nat := 523133748480247765389631

theorem tailTrace_1528199 : CollatzResearch.WordTrace tailWord_1528199 prefixEnd_1528199 523133748480247765389631 := by
  unfold tailWord_1528199
  simp only [CollatzResearch.WordTrace]
  refine ⟨55737996590603493455387651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37158664393735662303591767 55737996590603493455387651)
  ·
    refine ⟨83606994885905240183081477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55737996590603493455387651 83606994885905240183081477)
    ·
      refine ⟨15676311541107232534327777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83606994885905240183081477 15676311541107232534327777)
      ·
        refine ⟨11757233655830424400745833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15676311541107232534327777 11757233655830424400745833)
        ·
          refine ⟨8817925241872818300559375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11757233655830424400745833 8817925241872818300559375)
          ·
            refine ⟨13226887862809227450839063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8817925241872818300559375 13226887862809227450839063)
            ·
              refine ⟨19840331794213841176258595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13226887862809227450839063 19840331794213841176258595)
              ·
                refine ⟨29760497691320761764387893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19840331794213841176258595 29760497691320761764387893)
                ·
                  refine ⟨2790046658561321415411365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29760497691320761764387893 2790046658561321415411365)
                  ·
                    refine ⟨523133748480247765389631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790046658561321415411365 523133748480247765389631)
                    ·
                      rfl

theorem cell22_1528199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1528199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528199 prefixEnd_1528199 := by exact prefixLift 1528199
  have htrace : WordTrace (prefixWord ++ tailWord_1528199) baseStart_1528199 baseEnd_1528199 := by
    simpa [prefixWord, tailWord_1528199, baseEnd_1528199] using wordTrace_append hprefix tailTrace_1528199
  have hstable : (prefixWord ++ tailWord_1528199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528199).length < 2 ^ (prefixWord ++ tailWord_1528199).sum := by decide
  have hdescent : baseEnd_1528199 < baseStart_1528199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528216 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 3, 4]
def baseStart_1528216 : Nat := 118140960795 + 1528216 * 2 ^ 59
def prefixEnd_1528216 : Nat := 4983230072969 + 3 ^ 40 * 1528216 * 2
def baseEnd_1528216 : Nat := 523139567927665387714579

theorem tailTrace_1528216 : CollatzResearch.WordTrace tailWord_1528216 prefixEnd_1528216 523139567927665387714579 := by
  unfold tailWord_1528216
  simp only [CollatzResearch.WordTrace]
  refine ⟨27869308315770952679378251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37159077754361270239171001 27869308315770952679378251)
  ·
    refine ⟨41803962473656429019067377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27869308315770952679378251 41803962473656429019067377)
    ·
      refine ⟨31352971855242321764300533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41803962473656429019067377 31352971855242321764300533)
      ·
        refine ⟨2939341111428967665403175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31352971855242321764300533 2939341111428967665403175)
        ·
          refine ⟨4409011667143451498104763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939341111428967665403175 4409011667143451498104763)
          ·
            refine ⟨6613517500715177247157145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4409011667143451498104763 6613517500715177247157145)
            ·
              refine ⟨4960138125536382935367859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6613517500715177247157145 4960138125536382935367859)
              ·
                refine ⟨7440207188304574403051789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960138125536382935367859 7440207188304574403051789)
                ·
                  refine ⟨2790077695614215401144421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7440207188304574403051789 2790077695614215401144421)
                  ·
                    refine ⟨523139567927665387714579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790077695614215401144421 523139567927665387714579)
                    ·
                      rfl

theorem cell22_1528216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_1528216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528216 prefixEnd_1528216 := by exact prefixLift 1528216
  have htrace : WordTrace (prefixWord ++ tailWord_1528216) baseStart_1528216 baseEnd_1528216 := by
    simpa [prefixWord, tailWord_1528216, baseEnd_1528216] using wordTrace_append hprefix tailTrace_1528216
  have hstable : (prefixWord ++ tailWord_1528216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528216).length < 2 ^ (prefixWord ++ tailWord_1528216).sum := by decide
  have hdescent : baseEnd_1528216 < baseStart_1528216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528229 : List Nat := [1, 3, 1, 2, 1, 1, 3, 4, 1, 5]
def baseStart_1528229 : Nat := 118140960795 + 1528229 * 2 ^ 59
def prefixEnd_1528229 : Nat := 4983230072969 + 3 ^ 40 * 1528229 * 2
def baseEnd_1528229 : Nat := 523144018093337687139539

theorem tailTrace_1528229 : CollatzResearch.WordTrace tailWord_1528229 prefixEnd_1528229 523144018093337687139539 := by
  unfold tailWord_1528229
  simp only [CollatzResearch.WordTrace]
  refine ⟨55739090780494808578979741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37159393853663205719319827 55739090780494808578979741)
  ·
    refine ⟨20902159042685553217117403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55739090780494808578979741 20902159042685553217117403)
    ·
      refine ⟨31353238564028329825676105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20902159042685553217117403 31353238564028329825676105)
      ·
        refine ⟨23514928923021247369257079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31353238564028329825676105 23514928923021247369257079)
        ·
          refine ⟨35272393384531871053885619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23514928923021247369257079 35272393384531871053885619)
          ·
            refine ⟨52908590076797806580828429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35272393384531871053885619 52908590076797806580828429)
            ·
              refine ⟨19840721278799177467810661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52908590076797806580828429 19840721278799177467810661)
              ·
                refine ⟨3720135239774845775214499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19840721278799177467810661 3720135239774845775214499)
                ·
                  refine ⟨5580202859662268662821749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3720135239774845775214499 5580202859662268662821749)
                  ·
                    refine ⟨523144018093337687139539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5580202859662268662821749 523144018093337687139539)
                    ·
                      rfl

theorem cell22_1528229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_1528229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528229 prefixEnd_1528229 := by exact prefixLift 1528229
  have htrace : WordTrace (prefixWord ++ tailWord_1528229) baseStart_1528229 baseEnd_1528229 := by
    simpa [prefixWord, tailWord_1528229, baseEnd_1528229] using wordTrace_append hprefix tailTrace_1528229
  have hstable : (prefixWord ++ tailWord_1528229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528229).length < 2 ^ (prefixWord ++ tailWord_1528229).sum := by decide
  have hdescent : baseEnd_1528229 < baseStart_1528229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528276 : List Nat := [2, 4, 1, 2, 2, 2, 1, 8]
def baseStart_1528276 : Nat := 118140960795 + 1528276 * 2 ^ 59
def prefixEnd_1528276 : Nat := 4983230072969 + 3 ^ 40 * 1528276 * 2
def baseEnd_1528276 : Nat := 58128900794871692357155

theorem tailTrace_1528276 : CollatzResearch.WordTrace tailWord_1528276 prefixEnd_1528276 58128900794871692357155 := by
  unfold tailWord_1528276
  simp only [CollatzResearch.WordTrace]
  refine ⟨27870402505662267802970341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37160536674216357070627121 27870402505662267802970341)
  ·
    refine ⟨5225700469811675213056939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27870402505662267802970341 5225700469811675213056939)
    ·
      refine ⟨7838550704717512819585409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225700469811675213056939 7838550704717512819585409)
      ·
        refine ⟨5878913028538134614689057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7838550704717512819585409 5878913028538134614689057)
        ·
          refine ⟨4409184771403600961016793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5878913028538134614689057 4409184771403600961016793)
          ·
            refine ⟨3306888578552700720762595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4409184771403600961016793 3306888578552700720762595)
            ·
              refine ⟨4960332867829051081143893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306888578552700720762595 4960332867829051081143893)
              ·
                refine ⟨58128900794871692357155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4960332867829051081143893 58128900794871692357155)
                ·
                  rfl

theorem cell22_1528276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 8].length) (baseStart_1528276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528276 prefixEnd_1528276 := by exact prefixLift 1528276
  have htrace : WordTrace (prefixWord ++ tailWord_1528276) baseStart_1528276 baseEnd_1528276 := by
    simpa [prefixWord, tailWord_1528276, baseEnd_1528276] using wordTrace_append hprefix tailTrace_1528276
  have hstable : (prefixWord ++ tailWord_1528276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528276).length < 2 ^ (prefixWord ++ tailWord_1528276).sum := by decide
  have hdescent : baseEnd_1528276 < baseStart_1528276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528278 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1528278 : Nat := 118140960795 + 1528278 * 2 ^ 59
def prefixEnd_1528278 : Nat := 4983230072969 + 3 ^ 40 * 1528278 * 2
def baseEnd_1528278 : Nat := 523160791794717892664389

theorem tailTrace_1528278 : CollatzResearch.WordTrace tailWord_1528278 prefixEnd_1528278 523160791794717892664389 := by
  unfold tailWord_1528278
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483804872332330621719593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37160585304878193298342325 3483804872332330621719593)
  ·
    refine ⟨2612853654249247966289695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3483804872332330621719593 2612853654249247966289695)
    ·
      refine ⟨3919280481373871949434543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2612853654249247966289695 3919280481373871949434543)
      ·
        refine ⟨5878920722060807924151815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919280481373871949434543 5878920722060807924151815)
        ·
          refine ⟨8818381083091211886227723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5878920722060807924151815 8818381083091211886227723)
          ·
            refine ⟨13227571624636817829341585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8818381083091211886227723 13227571624636817829341585)
            ·
              refine ⟨9920678718477613372006189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13227571624636817829341585 9920678718477613372006189)
              ·
                refine ⟨3720254519429105014502321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9920678718477613372006189 3720254519429105014502321)
                ·
                  refine ⟨2790190889571828760876741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3720254519429105014502321 2790190889571828760876741)
                  ·
                    refine ⟨523160791794717892664389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2790190889571828760876741 523160791794717892664389)
                    ·
                      rfl

theorem cell22_1528278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1528278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528278 prefixEnd_1528278 := by exact prefixLift 1528278
  have htrace : WordTrace (prefixWord ++ tailWord_1528278) baseStart_1528278 baseEnd_1528278 := by
    simpa [prefixWord, tailWord_1528278, baseEnd_1528278] using wordTrace_append hprefix tailTrace_1528278
  have hstable : (prefixWord ++ tailWord_1528278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528278).length < 2 ^ (prefixWord ++ tailWord_1528278).sum := by decide
  have hdescent : baseEnd_1528278 < baseStart_1528278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528293 : List Nat := [1, 3, 1, 5, 3, 1, 8]
def baseStart_1528293 : Nat := 118140960795 + 1528293 * 2 ^ 59
def prefixEnd_1528293 : Nat := 4983230072969 + 3 ^ 40 * 1528293 * 2
def baseEnd_1528293 : Nat := 19376515800046772353309

theorem tailTrace_1528293 : CollatzResearch.WordTrace tailWord_1528293 prefixEnd_1528293 19376515800046772353309 := by
  unfold tailWord_1528293
  simp only [CollatzResearch.WordTrace]
  refine ⟨55741425052262947509309533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37160950034841965006206355 55741425052262947509309533)
  ·
    refine ⟨20903034394598605315991075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55741425052262947509309533 20903034394598605315991075)
    ·
      refine ⟨31354551591897907973986613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20903034394598605315991075 31354551591897907973986613)
      ·
        refine ⟨2939489211740428872561245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31354551591897907973986613 2939489211740428872561245)
        ·
          refine ⟨1102308454402660827210467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2939489211740428872561245 1102308454402660827210467)
          ·
            refine ⟨1653462681603991240815701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102308454402660827210467 1653462681603991240815701)
            ·
              refine ⟨19376515800046772353309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1653462681603991240815701 19376515800046772353309)
              ·
                rfl

theorem cell22_1528293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 8].length) (baseStart_1528293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528293 prefixEnd_1528293 := by exact prefixLift 1528293
  have htrace : WordTrace (prefixWord ++ tailWord_1528293) baseStart_1528293 baseEnd_1528293 := by
    simpa [prefixWord, tailWord_1528293, baseEnd_1528293] using wordTrace_append hprefix tailTrace_1528293
  have hstable : (prefixWord ++ tailWord_1528293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528293).length < 2 ^ (prefixWord ++ tailWord_1528293).sum := by decide
  have hdescent : baseEnd_1528293 < baseStart_1528293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528304 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 7]
def baseStart_1528304 : Nat := 118140960795 + 1528304 * 2 ^ 59
def prefixEnd_1528304 : Nat := 4983230072969 + 3 ^ 40 * 1528304 * 2
def baseEnd_1528304 : Nat := 174389897375354163838103

theorem tailTrace_1528304 : CollatzResearch.WordTrace tailWord_1528304 prefixEnd_1528304 174389897375354163838103 := by
  unfold tailWord_1528304
  simp only [CollatzResearch.WordTrace]
  refine ⟨27870913127611548193979983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37161217503482064258639977 27870913127611548193979983)
  ·
    refine ⟨41806369691417322290969975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27870913127611548193979983 41806369691417322290969975)
    ·
      refine ⟨62709554537125983436454963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41806369691417322290969975 62709554537125983436454963)
      ·
        refine ⟨94064331805688975154682445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62709554537125983436454963 94064331805688975154682445)
        ·
          refine ⟨35274124427133365683005917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94064331805688975154682445 35274124427133365683005917)
          ·
            refine ⟨13227796660175012131127219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35274124427133365683005917 13227796660175012131127219)
            ·
              refine ⟨19841694990262518196690829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13227796660175012131127219 19841694990262518196690829)
              ·
                refine ⟨7440635621348444323759061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19841694990262518196690829 7440635621348444323759061)
                ·
                  refine ⟨174389897375354163838103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7440635621348444323759061 174389897375354163838103)
                  ·
                    rfl

theorem cell22_1528304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 7].length) (baseStart_1528304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528304 prefixEnd_1528304 := by exact prefixLift 1528304
  have htrace : WordTrace (prefixWord ++ tailWord_1528304) baseStart_1528304 baseEnd_1528304 := by
    simpa [prefixWord, tailWord_1528304, baseEnd_1528304] using wordTrace_append hprefix tailTrace_1528304
  have hstable : (prefixWord ++ tailWord_1528304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528304).length < 2 ^ (prefixWord ++ tailWord_1528304).sum := by decide
  have hdescent : baseEnd_1528304 < baseStart_1528304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528319 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 1, 7]
def baseStart_1528319 : Nat := 118140960795 + 1528319 * 2 ^ 59
def prefixEnd_1528319 : Nat := 4983230072969 + 3 ^ 40 * 1528319 * 2
def baseEnd_1528319 : Nat := 523174826932607452389263

theorem tailTrace_1528319 : CollatzResearch.WordTrace tailWord_1528319 prefixEnd_1528319 523174826932607452389263 := by
  unfold tailWord_1528319
  simp only [CollatzResearch.WordTrace]
  refine ⟨55742373350168753949756011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37161582233445835966504007 55742373350168753949756011)
  ·
    refine ⟨83613560025253130924634017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55742373350168753949756011 83613560025253130924634017)
    ·
      refine ⟨62710170018939848193475513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83613560025253130924634017 62710170018939848193475513)
      ·
        refine ⟨47032627514204886145106635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62710170018939848193475513 47032627514204886145106635)
        ·
          refine ⟨70548941271307329217659953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47032627514204886145106635 70548941271307329217659953)
          ·
            refine ⟨52911705953480496913244965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70548941271307329217659953 52911705953480496913244965)
            ·
              refine ⟨9920944866277593171233431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52911705953480496913244965 9920944866277593171233431)
              ·
                refine ⟨14881417299416389756850147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9920944866277593171233431 14881417299416389756850147)
                ·
                  refine ⟨22322125949124584635275221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14881417299416389756850147 22322125949124584635275221)
                  ·
                    refine ⟨523174826932607452389263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22322125949124584635275221 523174826932607452389263)
                    ·
                      rfl

theorem cell22_1528319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_1528319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528319 prefixEnd_1528319 := by exact prefixLift 1528319
  have htrace : WordTrace (prefixWord ++ tailWord_1528319) baseStart_1528319 baseEnd_1528319 := by
    simpa [prefixWord, tailWord_1528319, baseEnd_1528319] using wordTrace_append hprefix tailTrace_1528319
  have hstable : (prefixWord ++ tailWord_1528319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528319).length < 2 ^ (prefixWord ++ tailWord_1528319).sum := by decide
  have hdescent : baseEnd_1528319 < baseStart_1528319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528359 : List Nat := [1, 1, 7, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1528359 : Nat := 118140960795 + 1528359 * 2 ^ 59
def prefixEnd_1528359 : Nat := 4983230072969 + 3 ^ 40 * 1528359 * 2
def baseEnd_1528359 : Nat := 523188519750060681389141

theorem tailTrace_1528359 : CollatzResearch.WordTrace tailWord_1528359 prefixEnd_1528359 523188519750060681389141 := by
  unfold tailWord_1528359
  simp only [CollatzResearch.WordTrace]
  refine ⟨55743832270023840781212131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37162554846682560520808087 55743832270023840781212131)
  ·
    refine ⟨83615748405035761171818197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55743832270023840781212131 83615748405035761171818197)
    ·
      refine ⟨1959744103243025652464489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 83615748405035761171818197 1959744103243025652464489)
      ·
        refine ⟨1469808077432269239348367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959744103243025652464489 1469808077432269239348367)
        ·
          refine ⟨2204712116148403859022551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469808077432269239348367 2204712116148403859022551)
          ·
            refine ⟨3307068174222605788533827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204712116148403859022551 3307068174222605788533827)
            ·
              refine ⟨4960602261333908682800741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307068174222605788533827 4960602261333908682800741)
              ·
                refine ⟨930112924000107878025139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4960602261333908682800741 930112924000107878025139)
                ·
                  refine ⟨1395169386000161817037709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930112924000107878025139 1395169386000161817037709)
                  ·
                    refine ⟨523188519750060681389141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395169386000161817037709 523188519750060681389141)
                    ·
                      rfl

theorem cell22_1528359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1528359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528359 prefixEnd_1528359 := by exact prefixLift 1528359
  have htrace : WordTrace (prefixWord ++ tailWord_1528359) baseStart_1528359 baseEnd_1528359 := by
    simpa [prefixWord, tailWord_1528359, baseEnd_1528359] using wordTrace_append hprefix tailTrace_1528359
  have hstable : (prefixWord ++ tailWord_1528359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528359).length < 2 ^ (prefixWord ++ tailWord_1528359).sum := by decide
  have hdescent : baseEnd_1528359 < baseStart_1528359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528379 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 2, 10]
def baseStart_1528379 : Nat := 118140960795 + 1528379 * 2 ^ 59
def prefixEnd_1528379 : Nat := 4983230072969 + 3 ^ 40 * 1528379 * 2
def baseEnd_1528379 : Nat := 523195366158787295889079

theorem tailTrace_1528379 : CollatzResearch.WordTrace tailWord_1528379 prefixEnd_1528379 523195366158787295889079 := by
  unfold tailWord_1528379
  simp only [CollatzResearch.WordTrace]
  refine ⟨55744561729951384196940191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37163041153300922797960127 55744561729951384196940191)
  ·
    refine ⟨83616842594927076295410287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55744561729951384196940191 83616842594927076295410287)
    ·
      refine ⟨125425263892390614443115431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83616842594927076295410287 125425263892390614443115431)
      ·
        refine ⟨188137895838585921664673147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125425263892390614443115431 188137895838585921664673147)
        ·
          refine ⟨282206843757878882497009721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188137895838585921664673147 282206843757878882497009721)
          ·
            refine ⟨211655132818409161872757291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282206843757878882497009721 211655132818409161872757291)
            ·
              refine ⟨317482699227613742809135937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211655132818409161872757291 317482699227613742809135937)
              ·
                refine ⟨238112024420710307106851953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317482699227613742809135937 238112024420710307106851953)
                ·
                  refine ⟨178584018315532730330138965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238112024420710307106851953 178584018315532730330138965)
                  ·
                    refine ⟨523195366158787295889079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 178584018315532730330138965 523195366158787295889079)
                    ·
                      rfl

theorem cell22_1528379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_1528379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528379 prefixEnd_1528379 := by exact prefixLift 1528379
  have htrace : WordTrace (prefixWord ++ tailWord_1528379) baseStart_1528379 baseEnd_1528379 := by
    simpa [prefixWord, tailWord_1528379, baseEnd_1528379] using wordTrace_append hprefix tailTrace_1528379
  have hstable : (prefixWord ++ tailWord_1528379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528379).length < 2 ^ (prefixWord ++ tailWord_1528379).sum := by decide
  have hdescent : baseEnd_1528379 < baseStart_1528379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528396 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 1, 6]
def baseStart_1528396 : Nat := 118140960795 + 1528396 * 2 ^ 59
def prefixEnd_1528396 : Nat := 4983230072969 + 3 ^ 40 * 1528396 * 2
def baseEnd_1528396 : Nat := 523201185606204918214027

theorem tailTrace_1528396 : CollatzResearch.WordTrace tailWord_1528396 prefixEnd_1528396 523201185606204918214027 := by
  unfold tailWord_1528396
  simp only [CollatzResearch.WordTrace]
  refine ⟨27872590885444898050154521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37163454513926530733539361 27872590885444898050154521)
  ·
    refine ⟨20904443164083673537615891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27872590885444898050154521 20904443164083673537615891)
    ·
      refine ⟨31356664746125510306423837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20904443164083673537615891 31356664746125510306423837)
      ·
        refine ⟨11758749279797066364908939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31356664746125510306423837 11758749279797066364908939)
        ·
          refine ⟨17638123919695599547363409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11758749279797066364908939 17638123919695599547363409)
          ·
            refine ⟨13228592939771699660522557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17638123919695599547363409 13228592939771699660522557)
            ·
              refine ⟨4960722352414387372695959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13228592939771699660522557 4960722352414387372695959)
              ·
                refine ⟨7441083528621581059043939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4960722352414387372695959 7441083528621581059043939)
                ·
                  refine ⟨11161625292932371588565909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7441083528621581059043939 11161625292932371588565909)
                  ·
                    refine ⟨523201185606204918214027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11161625292932371588565909 523201185606204918214027)
                    ·
                      rfl

theorem cell22_1528396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 1, 6].length) (baseStart_1528396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528396 prefixEnd_1528396 := by exact prefixLift 1528396
  have htrace : WordTrace (prefixWord ++ tailWord_1528396) baseStart_1528396 baseEnd_1528396 := by
    simpa [prefixWord, tailWord_1528396, baseEnd_1528396] using wordTrace_append hprefix tailTrace_1528396
  have hstable : (prefixWord ++ tailWord_1528396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528396).length < 2 ^ (prefixWord ++ tailWord_1528396).sum := by decide
  have hdescent : baseEnd_1528396 < baseStart_1528396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528432 : List Nat := [2, 1, 1, 1, 7, 1, 3, 1, 2, 3]
def baseStart_1528432 : Nat := 118140960795 + 1528432 * 2 ^ 59
def prefixEnd_1528432 : Nat := 4983230072969 + 3 ^ 40 * 1528432 * 2
def baseEnd_1528432 : Nat := 523213509141912824313917

theorem tailTrace_1528432 : CollatzResearch.WordTrace tailWord_1528432 prefixEnd_1528432 523213509141912824313917 := by
  unfold tailWord_1528432
  simp only [CollatzResearch.WordTrace]
  refine ⟨27873247399379687124309775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37164329865839582832413033 27873247399379687124309775)
  ·
    refine ⟨41809871099069530686464663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27873247399379687124309775 41809871099069530686464663)
    ·
      refine ⟨62714806648604296029696995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41809871099069530686464663 62714806648604296029696995)
      ·
        refine ⟨94072209972906444044545493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62714806648604296029696995 94072209972906444044545493)
        ·
          refine ⟨2204817421239994782294035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94072209972906444044545493 2204817421239994782294035)
          ·
            refine ⟨3307226131859992173441053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204817421239994782294035 3307226131859992173441053)
            ·
              refine ⟨1240209799447497065040395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3307226131859992173441053 1240209799447497065040395)
              ·
                refine ⟨1860314699171245597560593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240209799447497065040395 1860314699171245597560593)
                ·
                  refine ⟨1395236024378434198170445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1860314699171245597560593 1395236024378434198170445)
                  ·
                    refine ⟨523213509141912824313917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395236024378434198170445 523213509141912824313917)
                    ·
                      rfl

theorem cell22_1528432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 1, 2, 3].length) (baseStart_1528432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528432 prefixEnd_1528432 := by exact prefixLift 1528432
  have htrace : WordTrace (prefixWord ++ tailWord_1528432) baseStart_1528432 baseEnd_1528432 := by
    simpa [prefixWord, tailWord_1528432, baseEnd_1528432] using wordTrace_append hprefix tailTrace_1528432
  have hstable : (prefixWord ++ tailWord_1528432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528432).length < 2 ^ (prefixWord ++ tailWord_1528432).sum := by decide
  have hdescent : baseEnd_1528432 < baseStart_1528432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528445 : List Nat := [1, 4, 1, 1, 5, 2, 2, 6]
def baseStart_1528445 : Nat := 118140960795 + 1528445 * 2 ^ 59
def prefixEnd_1528445 : Nat := 4983230072969 + 3 ^ 40 * 1528445 * 2
def baseEnd_1528445 : Nat := 58135328811953902637653

theorem tailTrace_1528445 : CollatzResearch.WordTrace tailWord_1528445 prefixEnd_1528445 58135328811953902637653 := by
  unfold tailWord_1528445
  simp only [CollatzResearch.WordTrace]
  refine ⟨55746968947712277468842789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37164645965141518312561859 55746968947712277468842789)
  ·
    refine ⟨10452556677696052025408023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55746968947712277468842789 10452556677696052025408023)
    ·
      refine ⟨15678835016544078038112035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10452556677696052025408023 15678835016544078038112035)
      ·
        refine ⟨23518252524816117057168053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15678835016544078038112035 23518252524816117057168053)
        ·
          refine ⟨2204836174201510974109505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23518252524816117057168053 2204836174201510974109505)
          ·
            refine ⟨1653627130651133230582129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2204836174201510974109505 1653627130651133230582129)
            ·
              refine ⟨1240220347988349922936597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653627130651133230582129 1240220347988349922936597)
              ·
                refine ⟨58135328811953902637653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1240220347988349922936597 58135328811953902637653)
                ·
                  rfl

theorem cell22_1528445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 6].length) (baseStart_1528445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528445 prefixEnd_1528445 := by exact prefixLift 1528445
  have htrace : WordTrace (prefixWord ++ tailWord_1528445) baseStart_1528445 baseEnd_1528445 := by
    simpa [prefixWord, tailWord_1528445, baseEnd_1528445] using wordTrace_append hprefix tailTrace_1528445
  have hstable : (prefixWord ++ tailWord_1528445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528445).length < 2 ^ (prefixWord ++ tailWord_1528445).sum := by decide
  have hdescent : baseEnd_1528445 < baseStart_1528445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528460 : List Nat := [2, 2, 1, 2, 1, 1, 2, 7, 1, 3]
def baseStart_1528460 : Nat := 118140960795 + 1528460 * 2 ^ 59
def prefixEnd_1528460 : Nat := 4983230072969 + 3 ^ 40 * 1528460 * 2
def baseEnd_1528460 : Nat := 523223094114130084613831

theorem tailTrace_1528460 : CollatzResearch.WordTrace tailWord_1528460 prefixEnd_1528460 523223094114130084613831 := by
  unfold tailWord_1528460
  simp only [CollatzResearch.WordTrace]
  refine ⟨27873758021328967515319417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37165010695105290020425889 27873758021328967515319417)
  ·
    refine ⟨20905318515996725636489563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27873758021328967515319417 20905318515996725636489563)
    ·
      refine ⟨31357977773995088454734345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20905318515996725636489563 31357977773995088454734345)
      ·
        refine ⟨23518483330496316341050759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31357977773995088454734345 23518483330496316341050759)
        ·
          refine ⟨35277724995744474511576139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23518483330496316341050759 35277724995744474511576139)
          ·
            refine ⟨52916587493616711767364209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35277724995744474511576139 52916587493616711767364209)
            ·
              refine ⟨39687440620212533825523157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52916587493616711767364209 39687440620212533825523157)
              ·
                refine ⟨930174389536231261535699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39687440620212533825523157 930174389536231261535699)
                ·
                  refine ⟨1395261584304346892303549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930174389536231261535699 1395261584304346892303549)
                  ·
                    refine ⟨523223094114130084613831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395261584304346892303549 523223094114130084613831)
                    ·
                      rfl

theorem cell22_1528460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 1, 3].length) (baseStart_1528460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528460 prefixEnd_1528460 := by exact prefixLift 1528460
  have htrace : WordTrace (prefixWord ++ tailWord_1528460) baseStart_1528460 baseEnd_1528460 := by
    simpa [prefixWord, tailWord_1528460, baseEnd_1528460] using wordTrace_append hprefix tailTrace_1528460
  have hstable : (prefixWord ++ tailWord_1528460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528460).length < 2 ^ (prefixWord ++ tailWord_1528460).sum := by decide
  have hdescent : baseEnd_1528460 < baseStart_1528460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528535 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 4]
def baseStart_1528535 : Nat := 118140960795 + 1528535 * 2 ^ 59
def prefixEnd_1528535 : Nat := 4983230072969 + 3 ^ 40 * 1528535 * 2
def baseEnd_1528535 : Nat := 174416256048951629662867

theorem tailTrace_1528535 : CollatzResearch.WordTrace tailWord_1528535 prefixEnd_1528535 174416256048951629662867 := by
  unfold tailWord_1528535
  simp only [CollatzResearch.WordTrace]
  refine ⟨55750251517386222839619059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37166834344924148559746039 55750251517386222839619059)
  ·
    refine ⟨83625377276079334259428589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55750251517386222839619059 83625377276079334259428589)
    ·
      refine ⟨31359516478529750347285721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83625377276079334259428589 31359516478529750347285721)
      ·
        refine ⟨23519637358897312760464291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31359516478529750347285721 23519637358897312760464291)
        ·
          refine ⟨35279456038345969140696437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23519637358897312760464291 35279456038345969140696437)
          ·
            refine ⟨3307449003594934606940291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35279456038345969140696437 3307449003594934606940291)
            ·
              refine ⟨4961173505392401910410437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307449003594934606940291 4961173505392401910410437)
              ·
                refine ⟨930220032261075358201957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4961173505392401910410437 930220032261075358201957)
                ·
                  refine ⟨174416256048951629662867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 930220032261075358201957 174416256048951629662867)
                  ·
                    rfl

theorem cell22_1528535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 4].length) (baseStart_1528535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528535 prefixEnd_1528535 := by exact prefixLift 1528535
  have htrace : WordTrace (prefixWord ++ tailWord_1528535) baseStart_1528535 baseEnd_1528535 := by
    simpa [prefixWord, tailWord_1528535, baseEnd_1528535] using wordTrace_append hprefix tailTrace_1528535
  have hstable : (prefixWord ++ tailWord_1528535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528535).length < 2 ^ (prefixWord ++ tailWord_1528535).sum := by decide
  have hdescent : baseEnd_1528535 < baseStart_1528535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528595 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 3, 3]
def baseStart_1528595 : Nat := 118140960795 + 1528595 * 2 ^ 59
def prefixEnd_1528595 : Nat := 4983230072969 + 3 ^ 40 * 1528595 * 2
def baseEnd_1528595 : Nat := 523269307373034732488417

theorem tailTrace_1528595 : CollatzResearch.WordTrace tailWord_1528595 prefixEnd_1528595 523269307373034732488417 := by
  unfold tailWord_1528595
  simp only [CollatzResearch.WordTrace]
  refine ⟨55752439897168853086803239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37168293264779235391202159 55752439897168853086803239)
  ·
    refine ⟨83628659845753279630204859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55752439897168853086803239 83628659845753279630204859)
    ·
      refine ⟨125442989768629919445307289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83628659845753279630204859 125442989768629919445307289)
      ·
        refine ⟨94082242326472439583980467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125442989768629919445307289 94082242326472439583980467)
        ·
          refine ⟨141123363489708659375970701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94082242326472439583980467 141123363489708659375970701)
          ·
            refine ⟨52921261308640747265989013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141123363489708659375970701 52921261308640747265989013)
            ·
              refine ⟨2480684123842535028093235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52921261308640747265989013 2480684123842535028093235)
              ·
                refine ⟨3721026185763802542139853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480684123842535028093235 3721026185763802542139853)
                ·
                  refine ⟨1395384819661425953302445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3721026185763802542139853 1395384819661425953302445)
                  ·
                    refine ⟨523269307373034732488417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395384819661425953302445 523269307373034732488417)
                    ·
                      rfl

theorem cell22_1528595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 3, 3].length) (baseStart_1528595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528595 prefixEnd_1528595 := by exact prefixLift 1528595
  have htrace : WordTrace (prefixWord ++ tailWord_1528595) baseStart_1528595 baseEnd_1528595 := by
    simpa [prefixWord, tailWord_1528595, baseEnd_1528595] using wordTrace_append hprefix tailTrace_1528595
  have hstable : (prefixWord ++ tailWord_1528595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528595).length < 2 ^ (prefixWord ++ tailWord_1528595).sum := by decide
  have hdescent : baseEnd_1528595 < baseStart_1528595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528629 : List Nat := [1, 3, 3, 1, 3, 1, 3, 3, 1, 3]
def baseStart_1528629 : Nat := 118140960795 + 1528629 * 2 ^ 59
def prefixEnd_1528629 : Nat := 4983230072969 + 3 ^ 40 * 1528629 * 2
def baseEnd_1528629 : Nat := 523280946267869977138313

theorem tailTrace_1528629 : CollatzResearch.WordTrace tailWord_1528629 prefixEnd_1528629 523280946267869977138313 := by
  unfold tailWord_1528629
  simp only [CollatzResearch.WordTrace]
  refine ⟨55753679979045676893540941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37169119986030451262360627 55753679979045676893540941)
  ·
    refine ⟨20907629992142128835077853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55753679979045676893540941 20907629992142128835077853)
    ·
      refine ⟨7840361247053298313154195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20907629992142128835077853 7840361247053298313154195)
      ·
        refine ⟨11760541870579947469731293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7840361247053298313154195 11760541870579947469731293)
        ·
          refine ⟨4410203201467480301149235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11760541870579947469731293 4410203201467480301149235)
          ·
            refine ⟨6615304802201220451723853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410203201467480301149235 6615304802201220451723853)
            ·
              refine ⟨2480739300825457669396445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6615304802201220451723853 2480739300825457669396445)
              ·
                refine ⟨930277237809546626023667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2480739300825457669396445 930277237809546626023667)
                ·
                  refine ⟨1395415856714319939035501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930277237809546626023667 1395415856714319939035501)
                  ·
                    refine ⟨523280946267869977138313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395415856714319939035501 523280946267869977138313)
                    ·
                      rfl

theorem cell22_1528629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_1528629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528629 prefixEnd_1528629 := by exact prefixLift 1528629
  have htrace : WordTrace (prefixWord ++ tailWord_1528629) baseStart_1528629 baseEnd_1528629 := by
    simpa [prefixWord, tailWord_1528629, baseEnd_1528629] using wordTrace_append hprefix tailTrace_1528629
  have hstable : (prefixWord ++ tailWord_1528629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528629).length < 2 ^ (prefixWord ++ tailWord_1528629).sum := by decide
  have hdescent : baseEnd_1528629 < baseStart_1528629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528683 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 1, 6]
def baseStart_1528683 : Nat := 118140960795 + 1528683 * 2 ^ 59
def prefixEnd_1528683 : Nat := 4983230072969 + 3 ^ 40 * 1528683 * 2
def baseEnd_1528683 : Nat := 523299431571431836288147

theorem tailTrace_1528683 : CollatzResearch.WordTrace tailWord_1528683 prefixEnd_1528683 523299431571431836288147 := by
  unfold tailWord_1528683
  simp only [CollatzResearch.WordTrace]
  refine ⟨55755649520850044116006703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37170433013900029410671135 55755649520850044116006703)
  ·
    refine ⟨83633474281275066174010055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55755649520850044116006703 83633474281275066174010055)
    ·
      refine ⟨125450211421912599261015083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83633474281275066174010055 125450211421912599261015083)
      ·
        refine ⟨188175317132868898891522625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125450211421912599261015083 188175317132868898891522625)
        ·
          refine ⟨141131487849651674168641969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188175317132868898891522625 141131487849651674168641969)
          ·
            refine ⟨105848615887238755626481477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141131487849651674168641969 105848615887238755626481477)
            ·
              refine ⟨19846615478857266679965277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105848615887238755626481477 19846615478857266679965277)
              ·
                refine ⟨7442480804571475004986979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19846615478857266679965277 7442480804571475004986979)
                ·
                  refine ⟨11163721206857212507480469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7442480804571475004986979 11163721206857212507480469)
                  ·
                    refine ⟨523299431571431836288147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11163721206857212507480469 523299431571431836288147)
                    ·
                      rfl

theorem cell22_1528683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_1528683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528683 prefixEnd_1528683 := by exact prefixLift 1528683
  have htrace : WordTrace (prefixWord ++ tailWord_1528683) baseStart_1528683 baseEnd_1528683 := by
    simpa [prefixWord, tailWord_1528683, baseEnd_1528683] using wordTrace_append hprefix tailTrace_1528683
  have hstable : (prefixWord ++ tailWord_1528683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528683).length < 2 ^ (prefixWord ++ tailWord_1528683).sum := by decide
  have hdescent : baseEnd_1528683 < baseStart_1528683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528760 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 7]
def baseStart_1528760 : Nat := 118140960795 + 1528760 * 2 ^ 59
def prefixEnd_1528760 : Nat := 4983230072969 + 3 ^ 40 * 1528760 * 2
def baseEnd_1528760 : Nat := 174441930081676434037637

theorem tailTrace_1528760 : CollatzResearch.WordTrace tailWord_1528760 prefixEnd_1528760 174441930081676434037637 := by
  unfold tailWord_1528760
  simp only [CollatzResearch.WordTrace]
  refine ⟨27879228970785543133279867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37172305294380724177706489 27879228970785543133279867)
  ·
    refine ⟨41818843456178314699919801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27879228970785543133279867 41818843456178314699919801)
    ·
      refine ⟨31364132592133736024939851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41818843456178314699919801 31364132592133736024939851)
      ·
        refine ⟨47046198888200604037409777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31364132592133736024939851 47046198888200604037409777)
        ·
          refine ⟨35284649166150453028057333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47046198888200604037409777 35284649166150453028057333)
          ·
            refine ⟨3307935859326604971380375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35284649166150453028057333 3307935859326604971380375)
            ·
              refine ⟨4961903788989907457070563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307935859326604971380375 4961903788989907457070563)
              ·
                refine ⟨7442855683484861185605845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961903788989907457070563 7442855683484861185605845)
                ·
                  refine ⟨174441930081676434037637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7442855683484861185605845 174441930081676434037637)
                  ·
                    rfl

theorem cell22_1528760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 7].length) (baseStart_1528760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528760 prefixEnd_1528760 := by exact prefixLift 1528760
  have htrace : WordTrace (prefixWord ++ tailWord_1528760) baseStart_1528760 baseEnd_1528760 := by
    simpa [prefixWord, tailWord_1528760, baseEnd_1528760] using wordTrace_append hprefix tailTrace_1528760
  have hstable : (prefixWord ++ tailWord_1528760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528760).length < 2 ^ (prefixWord ++ tailWord_1528760).sum := by decide
  have hdescent : baseEnd_1528760 < baseStart_1528760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528775 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1528775 : Nat := 118140960795 + 1528775 * 2 ^ 59
def prefixEnd_1528775 : Nat := 4983230072969 + 3 ^ 40 * 1528775 * 2
def baseEnd_1528775 : Nat := 523330925051574262987865

theorem tailTrace_1528775 : CollatzResearch.WordTrace tailWord_1528775 prefixEnd_1528775 523330925051574262987865 := by
  unfold tailWord_1528775
  simp only [CollatzResearch.WordTrace]
  refine ⟨55759005036516743828355779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37172670024344495885570519 55759005036516743828355779)
  ·
    refine ⟨83638507554775115742533669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55759005036516743828355779 83638507554775115742533669)
    ·
      refine ⟨15682220166520334201725063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83638507554775115742533669 15682220166520334201725063)
      ·
        refine ⟨23523330249780501302587595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15682220166520334201725063 23523330249780501302587595)
        ·
          refine ⟨35284995374670751953881393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23523330249780501302587595 35284995374670751953881393)
          ·
            refine ⟨26463746531003063965411045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35284995374670751953881393 26463746531003063965411045)
            ·
              refine ⟨4961952474563074493514571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26463746531003063965411045 4961952474563074493514571)
              ·
                refine ⟨7442928711844611740271857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4961952474563074493514571 7442928711844611740271857)
                ·
                  refine ⟨5582196533883458805203893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7442928711844611740271857 5582196533883458805203893)
                  ·
                    refine ⟨523330925051574262987865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5582196533883458805203893 523330925051574262987865)
                    ·
                      rfl

theorem cell22_1528775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1528775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528775 prefixEnd_1528775 := by exact prefixLift 1528775
  have htrace : WordTrace (prefixWord ++ tailWord_1528775) baseStart_1528775 baseEnd_1528775 := by
    simpa [prefixWord, tailWord_1528775, baseEnd_1528775] using wordTrace_append hprefix tailTrace_1528775
  have hstable : (prefixWord ++ tailWord_1528775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528775).length < 2 ^ (prefixWord ++ tailWord_1528775).sum := by decide
  have hdescent : baseEnd_1528775 < baseStart_1528775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528871 : List Nat := [1, 1, 7, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1528871 : Nat := 118140960795 + 1528871 * 2 ^ 59
def prefixEnd_1528871 : Nat := 4983230072969 + 3 ^ 40 * 1528871 * 2
def baseEnd_1528871 : Nat := 523363787813462012587571

theorem tailTrace_1528871 : CollatzResearch.WordTrace tailWord_1528871 prefixEnd_1528871 523363787813462012587571 := by
  unfold tailWord_1528871
  simp only [CollatzResearch.WordTrace]
  refine ⟨55762506444168952223850467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37175004296112634815900311 55762506444168952223850467)
  ·
    refine ⟨83643759666253428335775701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55762506444168952223850467 83643759666253428335775701)
    ·
      refine ⟨1960400617177814726619743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 83643759666253428335775701 1960400617177814726619743)
      ·
        refine ⟨2940600925766722089929615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960400617177814726619743 2940600925766722089929615)
        ·
          refine ⟨4410901388650083134894423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940600925766722089929615 4410901388650083134894423)
          ·
            refine ⟨6616352082975124702341635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410901388650083134894423 6616352082975124702341635)
            ·
              refine ⟨9924528124462687053512453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6616352082975124702341635 9924528124462687053512453)
              ·
                refine ⟨1860849023336753822533585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9924528124462687053512453 1860849023336753822533585)
                ·
                  refine ⟨1395636767502565366900189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1860849023336753822533585 1395636767502565366900189)
                  ·
                    refine ⟨523363787813462012587571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395636767502565366900189 523363787813462012587571)
                    ·
                      rfl

theorem cell22_1528871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1528871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528871 prefixEnd_1528871 := by exact prefixLift 1528871
  have htrace : WordTrace (prefixWord ++ tailWord_1528871) baseStart_1528871 baseEnd_1528871 := by
    simpa [prefixWord, tailWord_1528871, baseEnd_1528871] using wordTrace_append hprefix tailTrace_1528871
  have hstable : (prefixWord ++ tailWord_1528871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528871).length < 2 ^ (prefixWord ++ tailWord_1528871).sum := by decide
  have hdescent : baseEnd_1528871 < baseStart_1528871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528880 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 1, 8]
def baseStart_1528880 : Nat := 118140960795 + 1528880 * 2 ^ 59
def prefixEnd_1528880 : Nat := 4983230072969 + 3 ^ 40 * 1528880 * 2
def baseEnd_1528880 : Nat := 523366868697388989112543

theorem tailTrace_1528880 : CollatzResearch.WordTrace tailWord_1528880 prefixEnd_1528880 523366868697388989112543 := by
  unfold tailWord_1528880
  simp only [CollatzResearch.WordTrace]
  refine ⟨27881417350568173380464047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37175223134090897840618729 27881417350568173380464047)
  ·
    refine ⟨41822126025852260070696071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27881417350568173380464047 41822126025852260070696071)
    ·
      refine ⟨62733189038778390106044107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41822126025852260070696071 62733189038778390106044107)
      ·
        refine ⟨94099783558167585159066161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62733189038778390106044107 94099783558167585159066161)
        ·
          refine ⟨70574837668625688869299621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94099783558167585159066161 70574837668625688869299621)
          ·
            refine ⟨13232782062867316662993679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70574837668625688869299621 13232782062867316662993679)
            ·
              refine ⟨19849173094300974994490519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13232782062867316662993679 19849173094300974994490519)
              ·
                refine ⟨29773759641451462491735779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19849173094300974994490519 29773759641451462491735779)
                ·
                  refine ⟨44660639462177193737603669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29773759641451462491735779 44660639462177193737603669)
                  ·
                    refine ⟨523366868697388989112543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44660639462177193737603669 523366868697388989112543)
                    ·
                      rfl

theorem cell22_1528880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_1528880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528880 prefixEnd_1528880 := by exact prefixLift 1528880
  have htrace : WordTrace (prefixWord ++ tailWord_1528880) baseStart_1528880 baseEnd_1528880 := by
    simpa [prefixWord, tailWord_1528880, baseEnd_1528880] using wordTrace_append hprefix tailTrace_1528880
  have hstable : (prefixWord ++ tailWord_1528880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528880).length < 2 ^ (prefixWord ++ tailWord_1528880).sum := by decide
  have hdescent : baseEnd_1528880 < baseStart_1528880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528884 : List Nat := [2, 5, 1, 2, 1, 1, 3, 7]
def baseStart_1528884 : Nat := 118140960795 + 1528884 * 2 ^ 59
def prefixEnd_1528884 : Nat := 4983230072969 + 3 ^ 40 * 1528884 * 2
def baseEnd_1528884 : Nat := 58152026442126034668059

theorem tailTrace_1528884 : CollatzResearch.WordTrace tailWord_1528884 prefixEnd_1528884 58152026442126034668059 := by
  unfold tailWord_1528884
  simp only [CollatzResearch.WordTrace]
  refine ⟨27881490296560927722036853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37175320395414570296049137 27881490296560927722036853)
  ·
    refine ⟨2613889715302586973940955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27881490296560927722036853 2613889715302586973940955)
    ·
      refine ⟨3920834572953880460911433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2613889715302586973940955 3920834572953880460911433)
      ·
        refine ⟨2940625929715410345683575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3920834572953880460911433 2940625929715410345683575)
        ·
          refine ⟨4410938894573115518525363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940625929715410345683575 4410938894573115518525363)
          ·
            refine ⟨6616408341859673277788045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4410938894573115518525363 6616408341859673277788045)
            ·
              refine ⟨2481153128197377479170517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6616408341859673277788045 2481153128197377479170517)
              ·
                refine ⟨58152026442126034668059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2481153128197377479170517 58152026442126034668059)
                ·
                  rfl

theorem cell22_1528884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 7].length) (baseStart_1528884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528884 prefixEnd_1528884 := by exact prefixLift 1528884
  have htrace : WordTrace (prefixWord ++ tailWord_1528884) baseStart_1528884 baseEnd_1528884 := by
    simpa [prefixWord, tailWord_1528884, baseEnd_1528884] using wordTrace_append hprefix tailTrace_1528884
  have hstable : (prefixWord ++ tailWord_1528884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528884).length < 2 ^ (prefixWord ++ tailWord_1528884).sum := by decide
  have hdescent : baseEnd_1528884 < baseStart_1528884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528895 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 9]
def baseStart_1528895 : Nat := 118140960795 + 1528895 * 2 ^ 59
def prefixEnd_1528895 : Nat := 4983230072969 + 3 ^ 40 * 1528895 * 2
def baseEnd_1528895 : Nat := 174457334501311316662499

theorem tailTrace_1528895 : CollatzResearch.WordTrace tailWord_1528895 prefixEnd_1528895 174457334501311316662499 := by
  unfold tailWord_1528895
  simp only [CollatzResearch.WordTrace]
  refine ⟨55763381796082004322724139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37175587864054669548482759 55763381796082004322724139)
  ·
    refine ⟨83645072694123006484086209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55763381796082004322724139 83645072694123006484086209)
    ·
      refine ⟨62733804520592254863064657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83645072694123006484086209 62733804520592254863064657)
      ·
        refine ⟨47050353390444191147298493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62733804520592254863064657 47050353390444191147298493)
        ·
          refine ⟨17643882521416571680236935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47050353390444191147298493 17643882521416571680236935)
          ·
            refine ⟨26465823782124857520355403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17643882521416571680236935 26465823782124857520355403)
            ·
              refine ⟨39698735673187286280533105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26465823782124857520355403 39698735673187286280533105)
              ·
                refine ⟨29774051754890464710399829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39698735673187286280533105 29774051754890464710399829)
                ·
                  refine ⟨174457334501311316662499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29774051754890464710399829 174457334501311316662499)
                  ·
                    rfl

theorem cell22_1528895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 9].length) (baseStart_1528895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528895 prefixEnd_1528895 := by exact prefixLift 1528895
  have htrace : WordTrace (prefixWord ++ tailWord_1528895) baseStart_1528895 baseEnd_1528895 := by
    simpa [prefixWord, tailWord_1528895, baseEnd_1528895] using wordTrace_append hprefix tailTrace_1528895
  have hstable : (prefixWord ++ tailWord_1528895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528895).length < 2 ^ (prefixWord ++ tailWord_1528895).sum := by decide
  have hdescent : baseEnd_1528895 < baseStart_1528895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528916 : List Nat := [2, 4, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_1528916 : Nat := 118140960795 + 1528916 * 2 ^ 59
def prefixEnd_1528916 : Nat := 4983230072969 + 3 ^ 40 * 1528916 * 2
def baseEnd_1528916 : Nat := 523379192233096895212433

theorem tailTrace_1528916 : CollatzResearch.WordTrace tailWord_1528916 prefixEnd_1528916 523379192233096895212433 := by
  unfold tailWord_1528916
  simp only [CollatzResearch.WordTrace]
  refine ⟨27882073864502962454619301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37176098486003949939492401 27882073864502962454619301)
  ·
    refine ⟨5227888849594305460241119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27882073864502962454619301 5227888849594305460241119)
    ·
      refine ⟨7841833274391458190361679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5227888849594305460241119 7841833274391458190361679)
      ·
        refine ⟨11762749911587187285542519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7841833274391458190361679 11762749911587187285542519)
        ·
          refine ⟨17644124867380780928313779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11762749911587187285542519 17644124867380780928313779)
          ·
            refine ⟨26466187301071171392470669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17644124867380780928313779 26466187301071171392470669)
            ·
              refine ⟨9924820237901689272176501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26466187301071171392470669 9924820237901689272176501)
              ·
                refine ⟨930451897303283369266547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9924820237901689272176501 930451897303283369266547)
                ·
                  refine ⟨1395677845954925053899821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930451897303283369266547 1395677845954925053899821)
                  ·
                    refine ⟨523379192233096895212433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395677845954925053899821 523379192233096895212433)
                    ·
                      rfl

theorem cell22_1528916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_1528916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528916 prefixEnd_1528916 := by exact prefixLift 1528916
  have htrace : WordTrace (prefixWord ++ tailWord_1528916) baseStart_1528916 baseEnd_1528916 := by
    simpa [prefixWord, tailWord_1528916, baseEnd_1528916] using wordTrace_append hprefix tailTrace_1528916
  have hstable : (prefixWord ++ tailWord_1528916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528916).length < 2 ^ (prefixWord ++ tailWord_1528916).sum := by decide
  have hdescent : baseEnd_1528916 < baseStart_1528916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528957 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 6]
def baseStart_1528957 : Nat := 118140960795 + 1528957 * 2 ^ 59
def prefixEnd_1528957 : Nat := 4983230072969 + 3 ^ 40 * 1528957 * 2
def baseEnd_1528957 : Nat := 174464409123662151645769

theorem tailTrace_1528957 : CollatzResearch.WordTrace tailWord_1528957 prefixEnd_1528957 174464409123662151645769 := by
  unfold tailWord_1528957
  simp only [CollatzResearch.WordTrace]
  refine ⟨55765643121857388911481125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37177095414571592607654083 55765643121857388911481125)
  ·
    refine ⟨10456058085348260420902711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55765643121857388911481125 10456058085348260420902711)
    ·
      refine ⟨15684087128022390631354067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10456058085348260420902711 15684087128022390631354067)
      ·
        refine ⟨23526130692033585947031101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684087128022390631354067 23526130692033585947031101)
        ·
          refine ⟨8822299009512594730136663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23526130692033585947031101 8822299009512594730136663)
          ·
            refine ⟨13233448514268892095204995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822299009512594730136663 13233448514268892095204995)
            ·
              refine ⟨19850172771403338142807493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13233448514268892095204995 19850172771403338142807493)
              ·
                refine ⟨3721907394638125901776405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19850172771403338142807493 3721907394638125901776405)
                ·
                  refine ⟨174464409123662151645769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3721907394638125901776405 174464409123662151645769)
                  ·
                    rfl

theorem cell22_1528957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_1528957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528957 prefixEnd_1528957 := by exact prefixLift 1528957
  have htrace : WordTrace (prefixWord ++ tailWord_1528957) baseStart_1528957 baseEnd_1528957 := by
    simpa [prefixWord, tailWord_1528957, baseEnd_1528957] using wordTrace_append hprefix tailTrace_1528957
  have hstable : (prefixWord ++ tailWord_1528957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528957).length < 2 ^ (prefixWord ++ tailWord_1528957).sum := by decide
  have hdescent : baseEnd_1528957 < baseStart_1528957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528972 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 1, 5]
def baseStart_1528972 : Nat := 118140960795 + 1528972 * 2 ^ 59
def prefixEnd_1528972 : Nat := 4983230072969 + 3 ^ 40 * 1528972 * 2
def baseEnd_1528972 : Nat := 523398362177531415812261

theorem tailTrace_1528972 : CollatzResearch.WordTrace tailWord_1528972 prefixEnd_1528972 523398362177531415812261 := by
  unfold tailWord_1528972
  simp only [CollatzResearch.WordTrace]
  refine ⟨27883095108401523236638585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37177460144535364315518113 27883095108401523236638585)
  ·
    refine ⟨20912321331301142427478939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27883095108401523236638585 20912321331301142427478939)
    ·
      refine ⟨31368481996951713641218409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20912321331301142427478939 31368481996951713641218409)
      ·
        refine ⟨23526361497713785230913807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31368481996951713641218409 23526361497713785230913807)
        ·
          refine ⟨35289542246570677846370711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23526361497713785230913807 35289542246570677846370711)
          ·
            refine ⟨52934313369856016769556067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35289542246570677846370711 52934313369856016769556067)
            ·
              refine ⟨79401470054784025154334101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52934313369856016769556067 79401470054784025154334101)
              ·
                refine ⟨3721943908818001179109411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79401470054784025154334101 3721943908818001179109411)
                ·
                  refine ⟨5582915863227001768664117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721943908818001179109411 5582915863227001768664117)
                  ·
                    refine ⟨523398362177531415812261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5582915863227001768664117 523398362177531415812261)
                    ·
                      rfl

theorem cell22_1528972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 1, 5].length) (baseStart_1528972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528972 prefixEnd_1528972 := by exact prefixLift 1528972
  have htrace : WordTrace (prefixWord ++ tailWord_1528972) baseStart_1528972 baseEnd_1528972 := by
    simpa [prefixWord, tailWord_1528972, baseEnd_1528972] using wordTrace_append hprefix tailTrace_1528972
  have hstable : (prefixWord ++ tailWord_1528972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528972).length < 2 ^ (prefixWord ++ tailWord_1528972).sum := by decide
  have hdescent : baseEnd_1528972 < baseStart_1528972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528989 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 4, 3]
def baseStart_1528989 : Nat := 118140960795 + 1528989 * 2 ^ 59
def prefixEnd_1528989 : Nat := 4983230072969 + 3 ^ 40 * 1528989 * 2
def baseEnd_1528989 : Nat := 523404181624949038137209

theorem tailTrace_1528989 : CollatzResearch.WordTrace tailWord_1528989 prefixEnd_1528989 523404181624949038137209 := by
  unfold tailWord_1528989
  simp only [CollatzResearch.WordTrace]
  refine ⟨55766810257741458376646021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37177873505160972251097347 55766810257741458376646021)
  ·
    refine ⟨10456276923326523445621129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55766810257741458376646021 10456276923326523445621129)
    ·
      refine ⟨7842207692494892584215847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10456276923326523445621129 7842207692494892584215847)
      ·
        refine ⟨11763311538742338876323771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7842207692494892584215847 11763311538742338876323771)
        ·
          refine ⟨17644967308113508314485657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11763311538742338876323771 17644967308113508314485657)
          ·
            refine ⟨13233725481085131235864243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17644967308113508314485657 13233725481085131235864243)
            ·
              refine ⟨19850588221627696853796365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13233725481085131235864243 19850588221627696853796365)
              ·
                refine ⟨7443970583110386320173637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19850588221627696853796365 7443970583110386320173637)
                ·
                  refine ⟨1395744484333197435032557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7443970583110386320173637 1395744484333197435032557)
                  ·
                    refine ⟨523404181624949038137209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395744484333197435032557 523404181624949038137209)
                    ·
                      rfl

theorem cell22_1528989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_1528989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528989 prefixEnd_1528989 := by exact prefixLift 1528989
  have htrace : WordTrace (prefixWord ++ tailWord_1528989) baseStart_1528989 baseEnd_1528989 := by
    simpa [prefixWord, tailWord_1528989, baseEnd_1528989] using wordTrace_append hprefix tailTrace_1528989
  have hstable : (prefixWord ++ tailWord_1528989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528989).length < 2 ^ (prefixWord ++ tailWord_1528989).sum := by decide
  have hdescent : baseEnd_1528989 < baseStart_1528989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1528991 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 6]
def baseStart_1528991 : Nat := 118140960795 + 1528991 * 2 ^ 59
def prefixEnd_1528991 : Nat := 4983230072969 + 3 ^ 40 * 1528991 * 2
def baseEnd_1528991 : Nat := 174468288755273899862401

theorem tailTrace_1528991 : CollatzResearch.WordTrace tailWord_1528991 prefixEnd_1528991 174468288755273899862401 := by
  unfold tailWord_1528991
  simp only [CollatzResearch.WordTrace]
  refine ⟨55766883203734212718218827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37177922135822808478812551 55766883203734212718218827)
  ·
    refine ⟨83650324805601319077328241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55766883203734212718218827 83650324805601319077328241)
    ·
      refine ⟨62737743604200989307996181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83650324805601319077328241 62737743604200989307996181)
      ·
        refine ⟨2940831731446921373812321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62737743604200989307996181 2940831731446921373812321)
        ·
          refine ⟨2205623798585191030359241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2940831731446921373812321 2205623798585191030359241)
          ·
            refine ⟨1654217848938893272769431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2205623798585191030359241 1654217848938893272769431)
            ·
              refine ⟨2481326773408339909154147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654217848938893272769431 2481326773408339909154147)
              ·
                refine ⟨3721990160112509863731221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481326773408339909154147 3721990160112509863731221)
                ·
                  refine ⟨174468288755273899862401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3721990160112509863731221 174468288755273899862401)
                  ·
                    rfl

theorem cell22_1528991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 6].length) (baseStart_1528991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1528991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1528991 prefixEnd_1528991 := by exact prefixLift 1528991
  have htrace : WordTrace (prefixWord ++ tailWord_1528991) baseStart_1528991 baseEnd_1528991 := by
    simpa [prefixWord, tailWord_1528991, baseEnd_1528991] using wordTrace_append hprefix tailTrace_1528991
  have hstable : (prefixWord ++ tailWord_1528991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1528991).length < 2 ^ (prefixWord ++ tailWord_1528991).sum := by decide
  have hdescent : baseEnd_1528991 < baseStart_1528991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1528991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529047 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 7]
def baseStart_1529047 : Nat := 118140960795 + 1529047 * 2 ^ 59
def prefixEnd_1529047 : Nat := 4983230072969 + 3 ^ 40 * 1529047 * 2
def baseEnd_1529047 : Nat := 174474678736752073395677

theorem tailTrace_1529047 : CollatzResearch.WordTrace tailWord_1529047 prefixEnd_1529047 174474678736752073395677 := by
  unfold tailWord_1529047
  simp only [CollatzResearch.WordTrace]
  refine ⟨55768925691531334282257395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37179283794354222854838263 55768925691531334282257395)
  ·
    refine ⟨83653388537297001423386093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55768925691531334282257395 83653388537297001423386093)
    ·
      refine ⟨31370020701486375533769785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83653388537297001423386093 31370020701486375533769785)
      ·
        refine ⟨23527515526114781650327339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31370020701486375533769785 23527515526114781650327339)
        ·
          refine ⟨35291273289172172475491009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23527515526114781650327339 35291273289172172475491009)
          ·
            refine ⟨26468454966879129356618257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35291273289172172475491009 26468454966879129356618257)
            ·
              refine ⟨19851341225159347017463693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26468454966879129356618257 19851341225159347017463693)
              ·
                refine ⟨7444252959434755131548885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19851341225159347017463693 7444252959434755131548885)
                ·
                  refine ⟨174474678736752073395677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7444252959434755131548885 174474678736752073395677)
                  ·
                    rfl

theorem cell22_1529047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 7].length) (baseStart_1529047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529047 prefixEnd_1529047 := by exact prefixLift 1529047
  have htrace : WordTrace (prefixWord ++ tailWord_1529047) baseStart_1529047 baseEnd_1529047 := by
    simpa [prefixWord, tailWord_1529047, baseEnd_1529047] using wordTrace_append hprefix tailTrace_1529047
  have hstable : (prefixWord ++ tailWord_1529047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529047).length < 2 ^ (prefixWord ++ tailWord_1529047).sum := by decide
  have hdescent : baseEnd_1529047 < baseStart_1529047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529053 : List Nat := [1, 4, 3, 2, 3, 1, 1, 7]
def baseStart_1529053 : Nat := 118140960795 + 1529053 * 2 ^ 59
def prefixEnd_1529053 : Nat := 4983230072969 + 3 ^ 40 * 1529053 * 2
def baseEnd_1529053 : Nat := 58158454459208244948557

theorem tailTrace_1529053 : CollatzResearch.WordTrace tailWord_1529053 prefixEnd_1529053 58158454459208244948557 := by
  unfold tailWord_1529053
  simp only [CollatzResearch.WordTrace]
  refine ⟨55769144529509597306975813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37179429686339731537983875 55769144529509597306975813)
  ·
    refine ⟨10456714599283049495057965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55769144529509597306975813 10456714599283049495057965)
    ·
      refine ⟨3921267974731143560646737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10456714599283049495057965 3921267974731143560646737)
      ·
        refine ⟨2940950981048357670485053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3921267974731143560646737 2940950981048357670485053)
        ·
          refine ⟨1102856617893134126431895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2940950981048357670485053 1102856617893134126431895)
          ·
            refine ⟨1654284926839701189647843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102856617893134126431895 1654284926839701189647843)
            ·
              refine ⟨2481427390259551784471765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654284926839701189647843 2481427390259551784471765)
              ·
                refine ⟨58158454459208244948557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2481427390259551784471765 58158454459208244948557)
                ·
                  rfl

theorem cell22_1529053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 7].length) (baseStart_1529053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529053 prefixEnd_1529053 := by exact prefixLift 1529053
  have htrace : WordTrace (prefixWord ++ tailWord_1529053) baseStart_1529053 baseEnd_1529053 := by
    simpa [prefixWord, tailWord_1529053, baseEnd_1529053] using wordTrace_append hprefix tailTrace_1529053
  have hstable : (prefixWord ++ tailWord_1529053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529053).length < 2 ^ (prefixWord ++ tailWord_1529053).sum := by decide
  have hdescent : baseEnd_1529053 < baseStart_1529053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529064 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 5]
def baseStart_1529064 : Nat := 118140960795 + 1529064 * 2 ^ 59
def prefixEnd_1529064 : Nat := 4983230072969 + 3 ^ 40 * 1529064 * 2
def baseEnd_1529064 : Nat := 174476618552557947503993

theorem tailTrace_1529064 : CollatzResearch.WordTrace tailWord_1529064 prefixEnd_1529064 174476618552557947503993 := by
  unfold tailWord_1529064
  simp only [CollatzResearch.WordTrace]
  refine ⟨27884772866234873092813123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37179697154979830790417497 27884772866234873092813123)
  ·
    refine ⟨41827159299352309639219685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27884772866234873092813123 41827159299352309639219685)
    ·
      refine ⟨7842592368628558057353691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41827159299352309639219685 7842592368628558057353691)
      ·
        refine ⟨11763888552942837086030537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7842592368628558057353691 11763888552942837086030537)
        ·
          refine ⟨8822916414707127814522903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11763888552942837086030537 8822916414707127814522903)
          ·
            refine ⟨13234374622060691721784355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8822916414707127814522903 13234374622060691721784355)
            ·
              refine ⟨19851561933091037582676533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13234374622060691721784355 19851561933091037582676533)
              ·
                refine ⟨1861083931227284773375925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19851561933091037582676533 1861083931227284773375925)
                ·
                  refine ⟨174476618552557947503993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1861083931227284773375925 174476618552557947503993)
                  ·
                    rfl

theorem cell22_1529064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 5].length) (baseStart_1529064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529064 prefixEnd_1529064 := by exact prefixLift 1529064
  have htrace : WordTrace (prefixWord ++ tailWord_1529064) baseStart_1529064 baseEnd_1529064 := by
    simpa [prefixWord, tailWord_1529064, baseEnd_1529064] using wordTrace_append hprefix tailTrace_1529064
  have hstable : (prefixWord ++ tailWord_1529064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529064).length < 2 ^ (prefixWord ++ tailWord_1529064).sum := by decide
  have hdescent : baseEnd_1529064 < baseStart_1529064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529107 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 2, 9]
def baseStart_1529107 : Nat := 118140960795 + 1529107 * 2 ^ 59
def prefixEnd_1529107 : Nat := 4983230072969 + 3 ^ 40 * 1529107 * 2
def baseEnd_1529107 : Nat := 523444575436436063686847

theorem tailTrace_1529107 : CollatzResearch.WordTrace tailWord_1529107 prefixEnd_1529107 523444575436436063686847 := by
  unfold tailWord_1529107
  simp only [CollatzResearch.WordTrace]
  refine ⟨55771114071313964529441575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37180742714209309686294383 55771114071313964529441575)
  ·
    refine ⟨83656671106970946794162363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55771114071313964529441575 83656671106970946794162363)
    ·
      refine ⟨125485006660456420191243545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83656671106970946794162363 125485006660456420191243545)
      ·
        refine ⟨94113754995342315143432659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125485006660456420191243545 94113754995342315143432659)
        ·
          refine ⟨141170632493013472715148989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94113754995342315143432659 141170632493013472715148989)
          ·
            refine ⟨52938987184880052268180871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141170632493013472715148989 52938987184880052268180871)
            ·
              refine ⟨79408480777320078402271307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52938987184880052268180871 79408480777320078402271307)
              ·
                refine ⟨119112721165980117603406961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79408480777320078402271307 119112721165980117603406961)
                ·
                  refine ⟨89334540874485088202555221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119112721165980117603406961 89334540874485088202555221)
                  ·
                    refine ⟨523444575436436063686847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 89334540874485088202555221 523444575436436063686847)
                    ·
                      rfl

theorem cell22_1529107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_1529107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529107 prefixEnd_1529107 := by exact prefixLift 1529107
  have htrace : WordTrace (prefixWord ++ tailWord_1529107) baseStart_1529107 baseEnd_1529107 := by
    simpa [prefixWord, tailWord_1529107, baseEnd_1529107] using wordTrace_append hprefix tailTrace_1529107
  have hstable : (prefixWord ++ tailWord_1529107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529107).length < 2 ^ (prefixWord ++ tailWord_1529107).sum := by decide
  have hdescent : baseEnd_1529107 < baseStart_1529107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529128 : List Nat := [2, 1, 5, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1529128 : Nat := 118140960795 + 1529128 * 2 ^ 59
def prefixEnd_1529128 : Nat := 4983230072969 + 3 ^ 40 * 1529128 * 2
def baseEnd_1529128 : Nat := 523451764165599008911783

theorem tailTrace_1529128 : CollatzResearch.WordTrace tailWord_1529128 prefixEnd_1529128 523451764165599008911783 := by
  unfold tailWord_1529128
  simp only [CollatzResearch.WordTrace]
  refine ⟨27885940002118942557978019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37181253336158590077304025 27885940002118942557978019)
  ·
    refine ⟨41828910003178413836967029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27885940002118942557978019 41828910003178413836967029)
    ·
      refine ⟨3921460312797976297215659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41828910003178413836967029 3921460312797976297215659)
      ·
        refine ⟨5882190469196964445823489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3921460312797976297215659 5882190469196964445823489)
        ·
          refine ⟨4411642851897723334367617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5882190469196964445823489 4411642851897723334367617)
          ·
            refine ⟨3308732138923292500775713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4411642851897723334367617 3308732138923292500775713)
            ·
              refine ⟨2481549104192469375581785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3308732138923292500775713 2481549104192469375581785)
              ·
                refine ⟨1861161828144352031686339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2481549104192469375581785 1861161828144352031686339)
                ·
                  refine ⟨2791742742216528047529509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1861161828144352031686339 2791742742216528047529509)
                  ·
                    refine ⟨523451764165599008911783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2791742742216528047529509 523451764165599008911783)
                    ·
                      rfl

theorem cell22_1529128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1529128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529128 prefixEnd_1529128 := by exact prefixLift 1529128
  have htrace : WordTrace (prefixWord ++ tailWord_1529128) baseStart_1529128 baseEnd_1529128 := by
    simpa [prefixWord, tailWord_1529128, baseEnd_1529128] using wordTrace_append hprefix tailTrace_1529128
  have hstable : (prefixWord ++ tailWord_1529128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529128).length < 2 ^ (prefixWord ++ tailWord_1529128).sum := by decide
  have hdescent : baseEnd_1529128 < baseStart_1529128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529139 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 1, 6]
def baseStart_1529139 : Nat := 118140960795 + 1529139 * 2 ^ 59
def prefixEnd_1529139 : Nat := 4983230072969 + 3 ^ 40 * 1529139 * 2
def baseEnd_1529139 : Nat := 523455529690398646886749

theorem tailTrace_1529139 : CollatzResearch.WordTrace tailWord_1529139 prefixEnd_1529139 523455529690398646886749 := by
  unfold tailWord_1529139
  simp only [CollatzResearch.WordTrace]
  refine ⟨55772281207198033994606471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37181520804798689329737647 55772281207198033994606471)
  ·
    refine ⟨83658421810797050991909707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55772281207198033994606471 83658421810797050991909707)
    ·
      refine ⟨125487632716195576487864561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83658421810797050991909707 125487632716195576487864561)
      ·
        refine ⟨94115724537146682365898421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125487632716195576487864561 94115724537146682365898421)
        ·
          refine ⟨8823349175357501471802977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94115724537146682365898421 8823349175357501471802977)
          ·
            refine ⟨6617511881518126103852233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8823349175357501471802977 6617511881518126103852233)
            ·
              refine ⟨4963133911138594577889175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6617511881518126103852233 4963133911138594577889175)
              ·
                refine ⟨7444700866707891866833763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4963133911138594577889175 7444700866707891866833763)
                ·
                  refine ⟨11167051300061837800250645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7444700866707891866833763 11167051300061837800250645)
                  ·
                    refine ⟨523455529690398646886749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11167051300061837800250645 523455529690398646886749)
                    ·
                      rfl

theorem cell22_1529139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_1529139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529139 prefixEnd_1529139 := by exact prefixLift 1529139
  have htrace : WordTrace (prefixWord ++ tailWord_1529139) baseStart_1529139 baseEnd_1529139 := by
    simpa [prefixWord, tailWord_1529139, baseEnd_1529139] using wordTrace_append hprefix tailTrace_1529139
  have hstable : (prefixWord ++ tailWord_1529139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529139).length < 2 ^ (prefixWord ++ tailWord_1529139).sum := by decide
  have hdescent : baseEnd_1529139 < baseStart_1529139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529141 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 4, 3]
def baseStart_1529141 : Nat := 118140960795 + 1529141 * 2 ^ 59
def prefixEnd_1529141 : Nat := 4983230072969 + 3 ^ 40 * 1529141 * 2
def baseEnd_1529141 : Nat := 523456214331271308336743

theorem tailTrace_1529141 : CollatzResearch.WordTrace tailWord_1529141 prefixEnd_1529141 523456214331271308336743 := by
  unfold tailWord_1529141
  simp only [CollatzResearch.WordTrace]
  refine ⟨55772354153190788336179277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37181569435460525557452851 55772354153190788336179277)
  ·
    refine ⟨20914632807446545626067229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55772354153190788336179277 20914632807446545626067229)
    ·
      refine ⟨7842987302792454609775211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20914632807446545626067229 7842987302792454609775211)
      ·
        refine ⟨11764480954188681914662817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7842987302792454609775211 11764480954188681914662817)
        ·
          refine ⟨8823360715641511435997113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11764480954188681914662817 8823360715641511435997113)
          ·
            refine ⟨6617520536731133576997835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8823360715641511435997113 6617520536731133576997835)
            ·
              refine ⟨9926280805096700365496753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617520536731133576997835 9926280805096700365496753)
              ·
                refine ⟨7444710603822525274122565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9926280805096700365496753 7444710603822525274122565)
                ·
                  refine ⟨1395883238216723488897981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7444710603822525274122565 1395883238216723488897981)
                  ·
                    refine ⟨523456214331271308336743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395883238216723488897981 523456214331271308336743)
                    ·
                      rfl

theorem cell22_1529141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_1529141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529141 prefixEnd_1529141 := by exact prefixLift 1529141
  have htrace : WordTrace (prefixWord ++ tailWord_1529141) baseStart_1529141 baseEnd_1529141 := by
    simpa [prefixWord, tailWord_1529141, baseEnd_1529141] using wordTrace_append hprefix tailTrace_1529141
  have hstable : (prefixWord ++ tailWord_1529141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529141).length < 2 ^ (prefixWord ++ tailWord_1529141).sum := by decide
  have hdescent : baseEnd_1529141 < baseStart_1529141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529175 : List Nat := [1, 1, 3, 2, 3, 4, 2, 1, 2, 3]
def baseStart_1529175 : Nat := 118140960795 + 1529175 * 2 ^ 59
def prefixEnd_1529175 : Nat := 4983230072969 + 3 ^ 40 * 1529175 * 2
def baseEnd_1529175 : Nat := 523467853226106552986639

theorem tailTrace_1529175 : CollatzResearch.WordTrace tailWord_1529175 prefixEnd_1529175 523467853226106552986639 := by
  unfold tailWord_1529175
  simp only [CollatzResearch.WordTrace]
  refine ⟨55773594235067612142916979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37182396156711741428611319 55773594235067612142916979)
  ·
    refine ⟨83660391352601418214375469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55773594235067612142916979 83660391352601418214375469)
    ·
      refine ⟨31372646757225531830390801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83660391352601418214375469 31372646757225531830390801)
      ·
        refine ⟨23529485067919148872793101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31372646757225531830390801 23529485067919148872793101)
        ·
          refine ⟨8823556900469680827297413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23529485067919148872793101 8823556900469680827297413)
          ·
            refine ⟨1654416918838065155118265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8823556900469680827297413 1654416918838065155118265)
            ·
              refine ⟨1240812689128548866338699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1654416918838065155118265 1240812689128548866338699)
              ·
                refine ⟨1861219033692823299508049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1240812689128548866338699 1861219033692823299508049)
                ·
                  refine ⟨1395914275269617474631037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1861219033692823299508049 1395914275269617474631037)
                  ·
                    refine ⟨523467853226106552986639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395914275269617474631037 523467853226106552986639)
                    ·
                      rfl

theorem cell22_1529175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_1529175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529175 prefixEnd_1529175 := by exact prefixLift 1529175
  have htrace : WordTrace (prefixWord ++ tailWord_1529175) baseStart_1529175 baseEnd_1529175 := by
    simpa [prefixWord, tailWord_1529175, baseEnd_1529175] using wordTrace_append hprefix tailTrace_1529175
  have hstable : (prefixWord ++ tailWord_1529175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529175).length < 2 ^ (prefixWord ++ tailWord_1529175).sum := by decide
  have hdescent : baseEnd_1529175 < baseStart_1529175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529218 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1529218 : Nat := 118140960795 + 1529218 * 2 ^ 59
def prefixEnd_1529218 : Nat := 4983230072969 + 3 ^ 40 * 1529218 * 2
def baseEnd_1529218 : Nat := 523482573004868774161507

theorem tailTrace_1529218 : CollatzResearch.WordTrace tailWord_1529218 prefixEnd_1529218 523482573004868774161507 := by
  unfold tailWord_1529218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13943790643477957621683077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37183441715941220324488205 13943790643477957621683077)
  ·
    refine ⟨2614460745652117054065577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13943790643477957621683077 2614460745652117054065577)
    ·
      refine ⟨1960845559239087790549183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2614460745652117054065577 1960845559239087790549183)
      ·
        refine ⟨2941268338858631685823775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960845559239087790549183 2941268338858631685823775)
        ·
          refine ⟨4411902508287947528735663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941268338858631685823775 4411902508287947528735663)
          ·
            refine ⟨6617853762431921293103495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4411902508287947528735663 6617853762431921293103495)
            ·
              refine ⟨9926780643647881939655243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6617853762431921293103495 9926780643647881939655243)
              ·
                refine ⟨14890170965471822909482865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9926780643647881939655243 14890170965471822909482865)
                ·
                  refine ⟨11167628224103867182112149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14890170965471822909482865 11167628224103867182112149)
                  ·
                    refine ⟨523482573004868774161507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11167628224103867182112149 523482573004868774161507)
                    ·
                      rfl

theorem cell22_1529218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1529218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529218 prefixEnd_1529218 := by exact prefixLift 1529218
  have htrace : WordTrace (prefixWord ++ tailWord_1529218) baseStart_1529218 baseEnd_1529218 := by
    simpa [prefixWord, tailWord_1529218, baseEnd_1529218] using wordTrace_append hprefix tailTrace_1529218
  have hstable : (prefixWord ++ tailWord_1529218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529218).length < 2 ^ (prefixWord ++ tailWord_1529218).sum := by decide
  have hdescent : baseEnd_1529218 < baseStart_1529218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529220 : List Nat := [2, 3, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_1529220 : Nat := 118140960795 + 1529220 * 2 ^ 59
def prefixEnd_1529220 : Nat := 4983230072969 + 3 ^ 40 * 1529220 * 2
def baseEnd_1529220 : Nat := 523483257645741435611501

theorem tailTrace_1529220 : CollatzResearch.WordTrace tailWord_1529220 prefixEnd_1529220 523483257645741435611501 := by
  unfold tailWord_1529220
  simp only [CollatzResearch.WordTrace]
  refine ⟨27887617759952292414152557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37183490346603056552203409 27887617759952292414152557)
  ·
    refine ⟨10457856659982109655307209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27887617759952292414152557 10457856659982109655307209)
    ·
      refine ⟨7843392494986582241480407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10457856659982109655307209 7843392494986582241480407)
      ·
        refine ⟨11765088742479873362220611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7843392494986582241480407 11765088742479873362220611)
        ·
          refine ⟨17647633113719810043330917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11765088742479873362220611 17647633113719810043330917)
          ·
            refine ⟨3308931208822464383124547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17647633113719810043330917 3308931208822464383124547)
            ·
              refine ⟨4963396813233696574686821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3308931208822464383124547 4963396813233696574686821)
              ·
                refine ⟨930636902481318107753779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4963396813233696574686821 930636902481318107753779)
                ·
                  refine ⟨1395955353721977161630669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930636902481318107753779 1395955353721977161630669)
                  ·
                    refine ⟨523483257645741435611501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395955353721977161630669 523483257645741435611501)
                    ·
                      rfl

theorem cell22_1529220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_1529220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529220 prefixEnd_1529220 := by exact prefixLift 1529220
  have htrace : WordTrace (prefixWord ++ tailWord_1529220) baseStart_1529220 baseEnd_1529220 := by
    simpa [prefixWord, tailWord_1529220, baseEnd_1529220] using wordTrace_append hprefix tailTrace_1529220
  have hstable : (prefixWord ++ tailWord_1529220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529220).length < 2 ^ (prefixWord ++ tailWord_1529220).sum := by decide
  have hdescent : baseEnd_1529220 < baseStart_1529220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529259 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 7, 5]
def baseStart_1529259 : Nat := 118140960795 + 1529259 * 2 ^ 59
def prefixEnd_1529259 : Nat := 4983230072969 + 3 ^ 40 * 1529259 * 2
def baseEnd_1529259 : Nat := 523496608142758333886381

theorem tailTrace_1529259 : CollatzResearch.WordTrace tailWord_1529259 prefixEnd_1529259 523496608142758333886381 := by
  unfold tailWord_1529259
  simp only [CollatzResearch.WordTrace]
  refine ⟨55776657966763294488974831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37184438644508862992649887 55776657966763294488974831)
  ·
    refine ⟨83664986950144941733462247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55776657966763294488974831 83664986950144941733462247)
    ·
      refine ⟨125497480425217412600193371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83664986950144941733462247 125497480425217412600193371)
      ·
        refine ⟨188246220637826118900290057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125497480425217412600193371 188246220637826118900290057)
        ·
          refine ⟨141184665478369589175217543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188246220637826118900290057 141184665478369589175217543)
          ·
            refine ⟨211776998217554383762826315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141184665478369589175217543 211776998217554383762826315)
            ·
              refine ⟨317665497326331575644239473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211776998217554383762826315 317665497326331575644239473)
              ·
                refine ⟨238249122994748681733179605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317665497326331575644239473 238249122994748681733179605)
                ·
                  refine ⟨5583963820189422228121397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 238249122994748681733179605 5583963820189422228121397)
                  ·
                    refine ⟨523496608142758333886381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5583963820189422228121397 523496608142758333886381)
                    ·
                      rfl

theorem cell22_1529259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_1529259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529259 prefixEnd_1529259 := by exact prefixLift 1529259
  have htrace : WordTrace (prefixWord ++ tailWord_1529259) baseStart_1529259 baseEnd_1529259 := by
    simpa [prefixWord, tailWord_1529259, baseEnd_1529259] using wordTrace_append hprefix tailTrace_1529259
  have hstable : (prefixWord ++ tailWord_1529259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529259).length < 2 ^ (prefixWord ++ tailWord_1529259).sum := by decide
  have hdescent : baseEnd_1529259 < baseStart_1529259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529289 : List Nat := [1, 2, 1, 1, 2, 1, 3, 11]
def baseStart_1529289 : Nat := 118140960795 + 1529289 * 2 ^ 59
def prefixEnd_1529289 : Nat := 4983230072969 + 3 ^ 40 * 1529289 * 2
def baseEnd_1529289 : Nat := 58167430861760917292921

theorem tailTrace_1529289 : CollatzResearch.WordTrace tailWord_1529289 prefixEnd_1529289 58167430861760917292921 := by
  unfold tailWord_1529289
  simp only [CollatzResearch.WordTrace]
  refine ⟨55777752156654609612566921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37185168104436406408377947 55777752156654609612566921)
  ·
    refine ⟨41833314117490957209425191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55777752156654609612566921 41833314117490957209425191)
    ·
      refine ⟨62749971176236435814137787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41833314117490957209425191 62749971176236435814137787)
      ·
        refine ⟨94124956764354653721206681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62749971176236435814137787 94124956764354653721206681)
        ·
          refine ⟨70593717573265990290905011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94124956764354653721206681 70593717573265990290905011)
          ·
            refine ⟨105890576359898985436357517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70593717573265990290905011 105890576359898985436357517)
            ·
              refine ⟨39708966134962119538634069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105890576359898985436357517 39708966134962119538634069)
              ·
                refine ⟨58167430861760917292921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39708966134962119538634069 58167430861760917292921)
                ·
                  rfl

theorem cell22_1529289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 11].length) (baseStart_1529289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529289 prefixEnd_1529289 := by exact prefixLift 1529289
  have htrace : WordTrace (prefixWord ++ tailWord_1529289) baseStart_1529289 baseEnd_1529289 := by
    simpa [prefixWord, tailWord_1529289, baseEnd_1529289] using wordTrace_append hprefix tailTrace_1529289
  have hstable : (prefixWord ++ tailWord_1529289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529289).length < 2 ^ (prefixWord ++ tailWord_1529289).sum := by decide
  have hdescent : baseEnd_1529289 < baseStart_1529289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529306 : List Nat := [3, 1, 1, 2, 3, 3, 1, 8]
def baseStart_1529306 : Nat := 118140960795 + 1529306 * 2 ^ 59
def prefixEnd_1529306 : Nat := 4983230072969 + 3 ^ 40 * 1529306 * 2
def baseEnd_1529306 : Nat := 58168077467029541995693

theorem tailTrace_1529306 : CollatzResearch.WordTrace tailWord_1529306 prefixEnd_1529306 58168077467029541995693 := by
  unfold tailWord_1529306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13944593049398255378983943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37185581465062014343957181 13944593049398255378983943)
  ·
    refine ⟨20916889574097383068475915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13944593049398255378983943 20916889574097383068475915)
    ·
      refine ⟨31375334361146074602713873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20916889574097383068475915 31375334361146074602713873)
      ·
        refine ⟨23531500770859555952035405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31375334361146074602713873 23531500770859555952035405)
        ·
          refine ⟨8824312789072333482013277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23531500770859555952035405 8824312789072333482013277)
          ·
            refine ⟨3309117295902125055754979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8824312789072333482013277 3309117295902125055754979)
            ·
              refine ⟨4963675943853187583632469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309117295902125055754979 4963675943853187583632469)
              ·
                refine ⟨58168077467029541995693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4963675943853187583632469 58168077467029541995693)
                ·
                  rfl

theorem cell22_1529306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 8].length) (baseStart_1529306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529306 prefixEnd_1529306 := by exact prefixLift 1529306
  have htrace : WordTrace (prefixWord ++ tailWord_1529306) baseStart_1529306 baseEnd_1529306 := by
    simpa [prefixWord, tailWord_1529306, baseEnd_1529306] using wordTrace_append hprefix tailTrace_1529306
  have hstable : (prefixWord ++ tailWord_1529306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529306).length < 2 ^ (prefixWord ++ tailWord_1529306).sum := by decide
  have hdescent : baseEnd_1529306 < baseStart_1529306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529325 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 2, 4]
def baseStart_1529325 : Nat := 118140960795 + 1529325 * 2 ^ 59
def prefixEnd_1529325 : Nat := 4983230072969 + 3 ^ 40 * 1529325 * 2
def baseEnd_1529325 : Nat := 523519201291556161736179

theorem tailTrace_1529325 : CollatzResearch.WordTrace tailWord_1529325 prefixEnd_1529325 523519201291556161736179 := by
  unfold tailWord_1529325
  simp only [CollatzResearch.WordTrace]
  refine ⟨55779065184524187760877429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37186043456349458507251619 55779065184524187760877429)
  ·
    refine ⟨5229287361049142602582259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55779065184524187760877429 5229287361049142602582259)
    ·
      refine ⟨7843931041573713903873389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5229287361049142602582259 7843931041573713903873389)
      ·
        refine ⟨2941474140590142713952521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7843931041573713903873389 2941474140590142713952521)
        ·
          refine ⟨2206105605442607035464391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2941474140590142713952521 2206105605442607035464391)
          ·
            refine ⟨3309158408163910553196587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206105605442607035464391 3309158408163910553196587)
            ·
              refine ⟨4963737612245865829794881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309158408163910553196587 4963737612245865829794881)
              ·
                refine ⟨3722803209184399372346161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4963737612245865829794881 3722803209184399372346161)
                ·
                  refine ⟨2792102406888299529259621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3722803209184399372346161 2792102406888299529259621)
                  ·
                    refine ⟨523519201291556161736179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792102406888299529259621 523519201291556161736179)
                    ·
                      rfl

theorem cell22_1529325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_1529325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529325 prefixEnd_1529325 := by exact prefixLift 1529325
  have htrace : WordTrace (prefixWord ++ tailWord_1529325) baseStart_1529325 baseEnd_1529325 := by
    simpa [prefixWord, tailWord_1529325, baseEnd_1529325] using wordTrace_append hprefix tailTrace_1529325
  have hstable : (prefixWord ++ tailWord_1529325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529325).length < 2 ^ (prefixWord ++ tailWord_1529325).sum := by decide
  have hdescent : baseEnd_1529325 < baseStart_1529325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529428 : List Nat := [2, 4, 1, 1, 1, 2, 1, 4, 1, 5]
def baseStart_1529428 : Nat := 118140960795 + 1529428 * 2 ^ 59
def prefixEnd_1529428 : Nat := 4983230072969 + 3 ^ 40 * 1529428 * 2
def baseEnd_1529428 : Nat := 523554460296498226410863

theorem tailTrace_1529428 : CollatzResearch.WordTrace tailWord_1529428 prefixEnd_1529428 523554460296498226410863 := by
  unfold tailWord_1529428
  simp only [CollatzResearch.WordTrace]
  refine ⟨27891410951575518175938469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37188547935434024234584625 27891410951575518175938469)
  ·
    refine ⟨5229639553420409657988463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27891410951575518175938469 5229639553420409657988463)
    ·
      refine ⟨7844459330130614486982695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5229639553420409657988463 7844459330130614486982695)
      ·
        refine ⟨11766688995195921730474043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7844459330130614486982695 11766688995195921730474043)
        ·
          refine ⟨17650033492793882595711065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11766688995195921730474043 17650033492793882595711065)
          ·
            refine ⟨13237525119595411946783299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17650033492793882595711065 13237525119595411946783299)
            ·
              refine ⟨19856287679393117920174949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13237525119595411946783299 19856287679393117920174949)
              ·
                refine ⟨3723053939886209610032803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19856287679393117920174949 3723053939886209610032803)
                ·
                  refine ⟨5584580909829314415049205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723053939886209610032803 5584580909829314415049205)
                  ·
                    refine ⟨523554460296498226410863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5584580909829314415049205 523554460296498226410863)
                    ·
                      rfl

theorem cell22_1529428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 4, 1, 5].length) (baseStart_1529428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529428 prefixEnd_1529428 := by exact prefixLift 1529428
  have htrace : WordTrace (prefixWord ++ tailWord_1529428) baseStart_1529428 baseEnd_1529428 := by
    simpa [prefixWord, tailWord_1529428, baseEnd_1529428] using wordTrace_append hprefix tailTrace_1529428
  have hstable : (prefixWord ++ tailWord_1529428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529428).length < 2 ^ (prefixWord ++ tailWord_1529428).sum := by decide
  have hdescent : baseEnd_1529428 < baseStart_1529428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529441 : List Nat := [1, 2, 3, 1, 1, 3, 11]
def baseStart_1529441 : Nat := 118140960795 + 1529441 * 2 ^ 59
def prefixEnd_1529441 : Nat := 4983230072969 + 3 ^ 40 * 1529441 * 2
def baseEnd_1529441 : Nat := 19391070757858167623549

theorem tailTrace_1529441 : CollatzResearch.WordTrace tailWord_1529441 prefixEnd_1529441 19391070757858167623549 := by
  unfold tailWord_1529441
  simp only [CollatzResearch.WordTrace]
  refine ⟨55783296052103939572100177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37188864034735959714733451 55783296052103939572100177)
  ·
    refine ⟨41837472039077954679075133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55783296052103939572100177 41837472039077954679075133)
    ·
      refine ⟨15689052014654233004653175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41837472039077954679075133 15689052014654233004653175)
      ·
        refine ⟨23533578021981349506979763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15689052014654233004653175 23533578021981349506979763)
        ·
          refine ⟨35300367032972024260469645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23533578021981349506979763 35300367032972024260469645)
          ·
            refine ⟨13237637637364509097676117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35300367032972024260469645 13237637637364509097676117)
            ·
              refine ⟨19391070757858167623549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13237637637364509097676117 19391070757858167623549)
              ·
                rfl

theorem cell22_1529441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 11].length) (baseStart_1529441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529441 prefixEnd_1529441 := by exact prefixLift 1529441
  have htrace : WordTrace (prefixWord ++ tailWord_1529441) baseStart_1529441 baseEnd_1529441 := by
    simpa [prefixWord, tailWord_1529441, baseEnd_1529441] using wordTrace_append hprefix tailTrace_1529441
  have hstable : (prefixWord ++ tailWord_1529441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529441).length < 2 ^ (prefixWord ++ tailWord_1529441).sum := by decide
  have hdescent : baseEnd_1529441 < baseStart_1529441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529445 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 4, 3]
def baseStart_1529445 : Nat := 118140960795 + 1529445 * 2 ^ 59
def prefixEnd_1529445 : Nat := 4983230072969 + 3 ^ 40 * 1529445 * 2
def baseEnd_1529445 : Nat := 523560279743915848735811

theorem tailTrace_1529445 : CollatzResearch.WordTrace tailWord_1529445 prefixEnd_1529445 523560279743915848735811 := by
  unfold tailWord_1529445
  simp only [CollatzResearch.WordTrace]
  refine ⟨55783441944089448255245789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37188961296059632170163859 55783441944089448255245789)
  ·
    refine ⟨20918790729033543095717171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55783441944089448255245789 20918790729033543095717171)
    ·
      refine ⟨31378186093550314643575757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20918790729033543095717171 31378186093550314643575757)
      ·
        refine ⟨11766819785081367991340909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31378186093550314643575757 11766819785081367991340909)
        ·
          refine ⟨4412557419405512996752841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11766819785081367991340909 4412557419405512996752841)
          ·
            refine ⟨3309418064554134747564631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4412557419405512996752841 3309418064554134747564631)
            ·
              refine ⟨4964127096831202121346947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309418064554134747564631 4964127096831202121346947)
              ·
                refine ⟨7446190645246803182020421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4964127096831202121346947 7446190645246803182020421)
                ·
                  refine ⟨1396160745983775596628829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7446190645246803182020421 1396160745983775596628829)
                  ·
                    refine ⟨523560279743915848735811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396160745983775596628829 523560279743915848735811)
                    ·
                      rfl

theorem cell22_1529445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_1529445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529445 prefixEnd_1529445 := by exact prefixLift 1529445
  have htrace : WordTrace (prefixWord ++ tailWord_1529445) baseStart_1529445 baseEnd_1529445 := by
    simpa [prefixWord, tailWord_1529445, baseEnd_1529445] using wordTrace_append hprefix tailTrace_1529445
  have hstable : (prefixWord ++ tailWord_1529445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529445).length < 2 ^ (prefixWord ++ tailWord_1529445).sum := by decide
  have hdescent : baseEnd_1529445 < baseStart_1529445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529462 : List Nat := [5, 1, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1529462 : Nat := 118140960795 + 1529462 * 2 ^ 59
def prefixEnd_1529462 : Nat := 4983230072969 + 3 ^ 40 * 1529462 * 2
def baseEnd_1529462 : Nat := 523566099191333471060759

theorem tailTrace_1529462 : CollatzResearch.WordTrace tailWord_1529462 prefixEnd_1529462 523566099191333471060759 := by
  unfold tailWord_1529462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486503874064241259913415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37189374656685240105743093 3486503874064241259913415)
  ·
    refine ⟨5229755811096361889870123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486503874064241259913415 5229755811096361889870123)
    ·
      refine ⟨7844633716644542834805185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5229755811096361889870123 7844633716644542834805185)
      ·
        refine ⟨5883475287483407126103889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7844633716644542834805185 5883475287483407126103889)
        ·
          refine ⟨4412606465612555344577917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5883475287483407126103889 4412606465612555344577917)
          ·
            refine ⟨1654727424604708254216719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4412606465612555344577917 1654727424604708254216719)
            ·
              refine ⟨2482091136907062381325079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654727424604708254216719 2482091136907062381325079)
              ·
                refine ⟨3723136705360593571987619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482091136907062381325079 3723136705360593571987619)
                ·
                  refine ⟨5584705058040890357981429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3723136705360593571987619 5584705058040890357981429)
                  ·
                    refine ⟨523566099191333471060759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5584705058040890357981429 523566099191333471060759)
                    ·
                      rfl

theorem cell22_1529462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1529462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529462 prefixEnd_1529462 := by exact prefixLift 1529462
  have htrace : WordTrace (prefixWord ++ tailWord_1529462) baseStart_1529462 baseEnd_1529462 := by
    simpa [prefixWord, tailWord_1529462, baseEnd_1529462] using wordTrace_append hprefix tailTrace_1529462
  have hstable : (prefixWord ++ tailWord_1529462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529462).length < 2 ^ (prefixWord ++ tailWord_1529462).sum := by decide
  have hdescent : baseEnd_1529462 < baseStart_1529462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529471 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 3, 8]
def baseStart_1529471 : Nat := 118140960795 + 1529471 * 2 ^ 59
def prefixEnd_1529471 : Nat := 4983230072969 + 3 ^ 40 * 1529471 * 2
def baseEnd_1529471 : Nat := 523569180075260447585731

theorem tailTrace_1529471 : CollatzResearch.WordTrace tailWord_1529471 prefixEnd_1529471 523569180075260447585731 := by
  unfold tailWord_1529471
  simp only [CollatzResearch.WordTrace]
  refine ⟨55784390241995254695692267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37189593494663503130461511 55784390241995254695692267)
  ·
    refine ⟨83676585362992882043538401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55784390241995254695692267 83676585362992882043538401)
    ·
      refine ⟨62757439022244661532653801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83676585362992882043538401 62757439022244661532653801)
      ·
        refine ⟨47068079266683496149490351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62757439022244661532653801 47068079266683496149490351)
        ·
          refine ⟨70602118900025244224235527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47068079266683496149490351 70602118900025244224235527)
          ·
            refine ⟨105903178350037866336353291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70602118900025244224235527 105903178350037866336353291)
            ·
              refine ⟨158854767525056799504529937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105903178350037866336353291 158854767525056799504529937)
              ·
                refine ⟨119141075643792599628397453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158854767525056799504529937 119141075643792599628397453)
                ·
                  refine ⟨44677903366422224860649045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119141075643792599628397453 44677903366422224860649045)
                  ·
                    refine ⟨523569180075260447585731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44677903366422224860649045 523569180075260447585731)
                    ·
                      rfl

theorem cell22_1529471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_1529471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529471 prefixEnd_1529471 := by exact prefixLift 1529471
  have htrace : WordTrace (prefixWord ++ tailWord_1529471) baseStart_1529471 baseEnd_1529471 := by
    simpa [prefixWord, tailWord_1529471, baseEnd_1529471] using wordTrace_append hprefix tailTrace_1529471
  have hstable : (prefixWord ++ tailWord_1529471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529471).length < 2 ^ (prefixWord ++ tailWord_1529471).sum := by decide
  have hdescent : baseEnd_1529471 < baseStart_1529471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529492 : List Nat := [2, 4, 2, 2, 3, 1, 8]
def baseStart_1529492 : Nat := 118140960795 + 1529492 * 2 ^ 59
def prefixEnd_1529492 : Nat := 4983230072969 + 3 ^ 40 * 1529492 * 2
def baseEnd_1529492 : Nat := 19391717363126792326321

theorem tailTrace_1529492 : CollatzResearch.WordTrace tailWord_1529492 prefixEnd_1529492 19391717363126792326321 := by
  unfold tailWord_1529492
  simp only [CollatzResearch.WordTrace]
  refine ⟨27892578087459587641103365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37190104116612783521471153 27892578087459587641103365)
  ·
    refine ⟨5229858391398672682706881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27892578087459587641103365 5229858391398672682706881)
    ·
      refine ⟨3922393793549004512030161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5229858391398672682706881 3922393793549004512030161)
      ·
        refine ⟨2941795345161753384022621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3922393793549004512030161 2941795345161753384022621)
        ·
          refine ⟨1103173254435657519008483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2941795345161753384022621 1103173254435657519008483)
          ·
            refine ⟨1654759881653486278512725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103173254435657519008483 1654759881653486278512725)
            ·
              refine ⟨19391717363126792326321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1654759881653486278512725 19391717363126792326321)
              ·
                rfl

theorem cell22_1529492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 8].length) (baseStart_1529492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529492 prefixEnd_1529492 := by exact prefixLift 1529492
  have htrace : WordTrace (prefixWord ++ tailWord_1529492) baseStart_1529492 baseEnd_1529492 := by
    simpa [prefixWord, tailWord_1529492, baseEnd_1529492] using wordTrace_append hprefix tailTrace_1529492
  have hstable : (prefixWord ++ tailWord_1529492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529492).length < 2 ^ (prefixWord ++ tailWord_1529492).sum := by decide
  have hdescent : baseEnd_1529492 < baseStart_1529492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529520 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 5]
def baseStart_1529520 : Nat := 118140960795 + 1529520 * 2 ^ 59
def prefixEnd_1529520 : Nat := 4983230072969 + 3 ^ 40 * 1529520 * 2
def baseEnd_1529520 : Nat := 174528651258880217703527

theorem tailTrace_1529520 : CollatzResearch.WordTrace tailWord_1529520 prefixEnd_1529520 174528651258880217703527 := by
  unfold tailWord_1529520
  simp only [CollatzResearch.WordTrace]
  refine ⟨27893088709408868032113007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37190784945878490709484009 27893088709408868032113007)
  ·
    refine ⟨41839633064113302048169511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27893088709408868032113007 41839633064113302048169511)
    ·
      refine ⟨62759449596169953072254267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41839633064113302048169511 62759449596169953072254267)
      ·
        refine ⟨94139174394254929608381401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62759449596169953072254267 94139174394254929608381401)
        ·
          refine ⟨70604380795691197206286051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94139174394254929608381401 70604380795691197206286051)
          ·
            refine ⟨105906571193536795809429077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70604380795691197206286051 105906571193536795809429077)
            ·
              refine ⟨1241092631174259325891747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 105906571193536795809429077 1241092631174259325891747)
              ·
                refine ⟨1861638946761388988837621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241092631174259325891747 1861638946761388988837621)
                ·
                  refine ⟨174528651258880217703527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1861638946761388988837621 174528651258880217703527)
                  ·
                    rfl

theorem cell22_1529520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 5].length) (baseStart_1529520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529520 prefixEnd_1529520 := by exact prefixLift 1529520
  have htrace : WordTrace (prefixWord ++ tailWord_1529520) baseStart_1529520 baseEnd_1529520 := by
    simpa [prefixWord, tailWord_1529520, baseEnd_1529520] using wordTrace_append hprefix tailTrace_1529520
  have hstable : (prefixWord ++ tailWord_1529520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529520).length < 2 ^ (prefixWord ++ tailWord_1529520).sum := by decide
  have hdescent : baseEnd_1529520 < baseStart_1529520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529558 : List Nat := [5, 2, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_1529558 : Nat := 118140960795 + 1529558 * 2 ^ 59
def prefixEnd_1529558 : Nat := 4983230072969 + 3 ^ 40 * 1529558 * 2
def baseEnd_1529558 : Nat := 523598961953221220660465

theorem tailTrace_1529558 : CollatzResearch.WordTrace tailWord_1529558 prefixEnd_1529558 523598961953221220660465 := by
  unfold tailWord_1529558
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486722712042504284631833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37191708928453379036072885 3486722712042504284631833)
  ·
    refine ⟨2615042034031878213473875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3486722712042504284631833 2615042034031878213473875)
    ·
      refine ⟨3922563051047817320210813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615042034031878213473875 3922563051047817320210813)
      ·
        refine ⟨1470961144142931495079055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3922563051047817320210813 1470961144142931495079055)
        ·
          refine ⟨2206441716214397242618583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470961144142931495079055 2206441716214397242618583)
          ·
            refine ⟨3309662574321595863927875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206441716214397242618583 3309662574321595863927875)
            ·
              refine ⟨4964493861482393795891813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3309662574321595863927875 4964493861482393795891813)
              ·
                refine ⟨930842599027948836729715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4964493861482393795891813 930842599027948836729715)
                ·
                  refine ⟨1396263898541923255094573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930842599027948836729715 1396263898541923255094573)
                  ·
                    refine ⟨523598961953221220660465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396263898541923255094573 523598961953221220660465)
                    ·
                      rfl

theorem cell22_1529558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_1529558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529558 prefixEnd_1529558 := by exact prefixLift 1529558
  have htrace : WordTrace (prefixWord ++ tailWord_1529558) baseStart_1529558 baseEnd_1529558 := by
    simpa [prefixWord, tailWord_1529558, baseEnd_1529558] using wordTrace_append hprefix tailTrace_1529558
  have hstable : (prefixWord ++ tailWord_1529558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529558).length < 2 ^ (prefixWord ++ tailWord_1529558).sum := by decide
  have hdescent : baseEnd_1529558 < baseStart_1529558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529676 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_1529676 : Nat := 118140960795 + 1529676 * 2 ^ 59
def prefixEnd_1529676 : Nat := 4983230072969 + 3 ^ 40 * 1529676 * 2
def baseEnd_1529676 : Nat := 523639355764708246210103

theorem tailTrace_1529676 : CollatzResearch.WordTrace tailWord_1529676 prefixEnd_1529676 523639355764708246210103 := by
  unfold tailWord_1529676
  simp only [CollatzResearch.WordTrace]
  refine ⟨27895933603126287353452441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37194578137501716471269921 27895933603126287353452441)
  ·
    refine ⟨20921950202344715515089331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27895933603126287353452441 20921950202344715515089331)
    ·
      refine ⟨31382925303517073272633997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20921950202344715515089331 31382925303517073272633997)
      ·
        refine ⟨11768596988818902477237749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31382925303517073272633997 11768596988818902477237749)
        ·
          refine ⟨1103305967701772107241039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11768596988818902477237749 1103305967701772107241039)
          ·
            refine ⟨1654958951552658160861559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103305967701772107241039 1654958951552658160861559)
            ·
              refine ⟨2482438427328987241292339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654958951552658160861559 2482438427328987241292339)
              ·
                refine ⟨3723657640993480861938509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482438427328987241292339 3723657640993480861938509)
                ·
                  refine ⟨1396371615372555323226941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3723657640993480861938509 1396371615372555323226941)
                  ·
                    refine ⟨523639355764708246210103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396371615372555323226941 523639355764708246210103)
                    ·
                      rfl

theorem cell22_1529676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_1529676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529676 prefixEnd_1529676 := by exact prefixLift 1529676
  have htrace : WordTrace (prefixWord ++ tailWord_1529676) baseStart_1529676 baseEnd_1529676 := by
    simpa [prefixWord, tailWord_1529676, baseEnd_1529676] using wordTrace_append hprefix tailTrace_1529676
  have hstable : (prefixWord ++ tailWord_1529676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529676).length < 2 ^ (prefixWord ++ tailWord_1529676).sum := by decide
  have hdescent : baseEnd_1529676 < baseStart_1529676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529732 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_1529732 : Nat := 118140960795 + 1529732 * 2 ^ 59
def prefixEnd_1529732 : Nat := 4983230072969 + 3 ^ 40 * 1529732 * 2
def baseEnd_1529732 : Nat := 523658525709142766809931

theorem tailTrace_1529732 : CollatzResearch.WordTrace tailWord_1529732 prefixEnd_1529732 523658525709142766809931 := by
  unfold tailWord_1529732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27896954847024848135471725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37195939796033130847295633 27896954847024848135471725)
  ·
    refine ⟨10461358067634318050801897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27896954847024848135471725 10461358067634318050801897)
    ·
      refine ⟨7846018550725738538101423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10461358067634318050801897 7846018550725738538101423)
      ·
        refine ⟨11769027826088607807152135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7846018550725738538101423 11769027826088607807152135)
        ·
          refine ⟨17653541739132911710728203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769027826088607807152135 17653541739132911710728203)
          ·
            refine ⟨26480312608699367566092305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17653541739132911710728203 26480312608699367566092305)
            ·
              refine ⟨19860234456524525674569229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26480312608699367566092305 19860234456524525674569229)
              ·
                refine ⟨7447587921196697127963461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19860234456524525674569229 7447587921196697127963461)
                ·
                  refine ⟨1396422735224380711493149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7447587921196697127963461 1396422735224380711493149)
                  ·
                    refine ⟨523658525709142766809931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396422735224380711493149 523658525709142766809931)
                    ·
                      rfl

theorem cell22_1529732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_1529732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529732 prefixEnd_1529732 := by exact prefixLift 1529732
  have htrace : WordTrace (prefixWord ++ tailWord_1529732) baseStart_1529732 baseEnd_1529732 := by
    simpa [prefixWord, tailWord_1529732, baseEnd_1529732] using wordTrace_append hprefix tailTrace_1529732
  have hstable : (prefixWord ++ tailWord_1529732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529732).length < 2 ^ (prefixWord ++ tailWord_1529732).sum := by decide
  have hdescent : baseEnd_1529732 < baseStart_1529732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529745 : List Nat := [1, 2, 2, 1, 1, 1, 7, 7]
def baseStart_1529745 : Nat := 118140960795 + 1529745 * 2 ^ 59
def prefixEnd_1529745 : Nat := 4983230072969 + 3 ^ 40 * 1529745 * 2
def baseEnd_1529745 : Nat := 58184775097201674026099

theorem tailTrace_1529745 : CollatzResearch.WordTrace tailWord_1529745 prefixEnd_1529745 58184775097201674026099 := by
  unfold tailWord_1529745
  simp only [CollatzResearch.WordTrace]
  refine ⟨55794383843002599491166689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37196255895335066327444459 55794383843002599491166689)
  ·
    refine ⟨41845787882251949618375017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55794383843002599491166689 41845787882251949618375017)
    ·
      refine ⟨31384340911688962213781263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41845787882251949618375017 31384340911688962213781263)
      ·
        refine ⟨47076511367533443320671895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31384340911688962213781263 47076511367533443320671895)
        ·
          refine ⟨70614767051300164981007843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47076511367533443320671895 70614767051300164981007843)
          ·
            refine ⟨105922150576950247471511765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70614767051300164981007843 105922150576950247471511765)
            ·
              refine ⟨2482550404147271425113557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 105922150576950247471511765 2482550404147271425113557)
              ·
                refine ⟨58184775097201674026099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2482550404147271425113557 58184775097201674026099)
                ·
                  rfl

theorem cell22_1529745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 7].length) (baseStart_1529745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529745 prefixEnd_1529745 := by exact prefixLift 1529745
  have htrace : WordTrace (prefixWord ++ tailWord_1529745) baseStart_1529745 baseEnd_1529745 := by
    simpa [prefixWord, tailWord_1529745, baseEnd_1529745] using wordTrace_append hprefix tailTrace_1529745
  have hstable : (prefixWord ++ tailWord_1529745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529745).length < 2 ^ (prefixWord ++ tailWord_1529745).sum := by decide
  have hdescent : baseEnd_1529745 < baseStart_1529745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529764 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 2, 4]
def baseStart_1529764 : Nat := 118140960795 + 1529764 * 2 ^ 59
def prefixEnd_1529764 : Nat := 4983230072969 + 3 ^ 40 * 1529764 * 2
def baseEnd_1529764 : Nat := 523669479963105350009833

theorem tailTrace_1529764 : CollatzResearch.WordTrace tailWord_1529764 prefixEnd_1529764 523669479963105350009833 := by
  unfold tailWord_1529764
  simp only [CollatzResearch.WordTrace]
  refine ⟨27897538414966882868054173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37196717886622510490738897 27897538414966882868054173)
  ·
    refine ⟨10461576905612581075520315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27897538414966882868054173 10461576905612581075520315)
    ·
      refine ⟨15692365358418871613280473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10461576905612581075520315 15692365358418871613280473)
      ·
        refine ⟨11769274018814153709960355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15692365358418871613280473 11769274018814153709960355)
        ·
          refine ⟨17653911028221230564940533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11769274018814153709960355 17653911028221230564940533)
          ·
            refine ⟨1655054158895740365463175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17653911028221230564940533 1655054158895740365463175)
            ·
              refine ⟨2482581238343610548194763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655054158895740365463175 2482581238343610548194763)
              ·
                refine ⟨3723871857515415822292145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2482581238343610548194763 3723871857515415822292145)
                ·
                  refine ⟨2792903893136561866719109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3723871857515415822292145 2792903893136561866719109)
                  ·
                    refine ⟨523669479963105350009833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2792903893136561866719109 523669479963105350009833)
                    ·
                      rfl

theorem cell22_1529764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_1529764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529764 prefixEnd_1529764 := by exact prefixLift 1529764
  have htrace : WordTrace (prefixWord ++ tailWord_1529764) baseStart_1529764 baseEnd_1529764 := by
    simpa [prefixWord, tailWord_1529764, baseEnd_1529764] using wordTrace_append hprefix tailTrace_1529764
  have hstable : (prefixWord ++ tailWord_1529764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529764).length < 2 ^ (prefixWord ++ tailWord_1529764).sum := by decide
  have hdescent : baseEnd_1529764 < baseStart_1529764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529768 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 4]
def baseStart_1529768 : Nat := 118140960795 + 1529768 * 2 ^ 59
def prefixEnd_1529768 : Nat := 4983230072969 + 3 ^ 40 * 1529768 * 2
def baseEnd_1529768 : Nat := 174556949748283557636607

theorem tailTrace_1529768 : CollatzResearch.WordTrace tailWord_1529768 prefixEnd_1529768 174556949748283557636607 := by
  unfold tailWord_1529768
  simp only [CollatzResearch.WordTrace]
  refine ⟨27897611360959637209626979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37196815147946182946169305 27897611360959637209626979)
  ·
    refine ⟨41846417041439455814440469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27897611360959637209626979 41846417041439455814440469)
    ·
      refine ⟨1961550798817474491301897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41846417041439455814440469 1961550798817474491301897)
      ·
        refine ⟨1471163099113105868476423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1961550798817474491301897 1471163099113105868476423)
        ·
          refine ⟨2206744648669658802714635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471163099113105868476423 2206744648669658802714635)
          ·
            refine ⟨3310116973004488204071953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2206744648669658802714635 3310116973004488204071953)
            ·
              refine ⟨2482587729753366153053965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3310116973004488204071953 2482587729753366153053965)
              ·
                refine ⟨930970398657512307395237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2482587729753366153053965 930970398657512307395237)
                ·
                  refine ⟨174556949748283557636607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 930970398657512307395237 174556949748283557636607)
                  ·
                    rfl

theorem cell22_1529768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 4].length) (baseStart_1529768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529768 prefixEnd_1529768 := by exact prefixLift 1529768
  have htrace : WordTrace (prefixWord ++ tailWord_1529768) baseStart_1529768 baseEnd_1529768 := by
    simpa [prefixWord, tailWord_1529768, baseEnd_1529768] using wordTrace_append hprefix tailTrace_1529768
  have hstable : (prefixWord ++ tailWord_1529768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529768).length < 2 ^ (prefixWord ++ tailWord_1529768).sum := by decide
  have hdescent : baseEnd_1529768 < baseStart_1529768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529835 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 8]
def baseStart_1529835 : Nat := 118140960795 + 1529835 * 2 ^ 59
def prefixEnd_1529835 : Nat := 4983230072969 + 3 ^ 40 * 1529835 * 2
def baseEnd_1529835 : Nat := 174564594904694943828205

theorem tailTrace_1529835 : CollatzResearch.WordTrace tailWord_1529835 prefixEnd_1529835 174564594904694943828205 := by
  unfold tailWord_1529835
  simp only [CollatzResearch.WordTrace]
  refine ⟨55797666412676544861942959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37198444275117696574628639 55797666412676544861942959)
  ·
    refine ⟨83696499619014817292914439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55797666412676544861942959 83696499619014817292914439)
    ·
      refine ⟨125544749428522225939371659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83696499619014817292914439 125544749428522225939371659)
      ·
        refine ⟨188317124142783338909057489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125544749428522225939371659 188317124142783338909057489)
        ·
          refine ⟨141237843107087504181793117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188317124142783338909057489 141237843107087504181793117)
          ·
            refine ⟨52964191165157814068172419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141237843107087504181793117 52964191165157814068172419)
            ·
              refine ⟨79446286747736721102258629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52964191165157814068172419 79446286747736721102258629)
              ·
                refine ⟨14896178765200635206673493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79446286747736721102258629 14896178765200635206673493)
                ·
                  refine ⟨174564594904694943828205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14896178765200635206673493 174564594904694943828205)
                  ·
                    rfl

theorem cell22_1529835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 8].length) (baseStart_1529835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529835 prefixEnd_1529835 := by exact prefixLift 1529835
  have htrace : WordTrace (prefixWord ++ tailWord_1529835) baseStart_1529835 baseEnd_1529835 := by
    simpa [prefixWord, tailWord_1529835, baseEnd_1529835] using wordTrace_append hprefix tailTrace_1529835
  have hstable : (prefixWord ++ tailWord_1529835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529835).length < 2 ^ (prefixWord ++ tailWord_1529835).sum := by decide
  have hdescent : baseEnd_1529835 < baseStart_1529835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529867 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 1, 5]
def baseStart_1529867 : Nat := 118140960795 + 1529867 * 2 ^ 59
def prefixEnd_1529867 : Nat := 4983230072969 + 3 ^ 40 * 1529867 * 2
def baseEnd_1529867 : Nat := 523704738968047414684517

theorem tailTrace_1529867 : CollatzResearch.WordTrace tailWord_1529867 prefixEnd_1529867 523704738968047414684517 := by
  unfold tailWord_1529867
  simp only [CollatzResearch.WordTrace]
  refine ⟨55798833548560614327107855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37199222365707076218071903 55798833548560614327107855)
  ·
    refine ⟨83698250322840921490661783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55798833548560614327107855 83698250322840921490661783)
    ·
      refine ⟨125547375484261382235992675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83698250322840921490661783 125547375484261382235992675)
      ·
        refine ⟨188321063226392073353989013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125547375484261382235992675 188321063226392073353989013)
        ·
          refine ⟨8827549838737128438468235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 188321063226392073353989013 8827549838737128438468235)
          ·
            refine ⟨13241324758105692657702353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827549838737128438468235 13241324758105692657702353)
            ·
              refine ⟨9930993568579269493276765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13241324758105692657702353 9930993568579269493276765)
              ·
                refine ⟨3724122588217226059978787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9930993568579269493276765 3724122588217226059978787)
                ·
                  refine ⟨5586183882325839089968181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724122588217226059978787 5586183882325839089968181)
                  ·
                    refine ⟨523704738968047414684517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5586183882325839089968181 523704738968047414684517)
                    ·
                      rfl

theorem cell22_1529867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 5].length) (baseStart_1529867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529867 prefixEnd_1529867 := by exact prefixLift 1529867
  have htrace : WordTrace (prefixWord ++ tailWord_1529867) baseStart_1529867 baseEnd_1529867 := by
    simpa [prefixWord, tailWord_1529867, baseEnd_1529867] using wordTrace_append hprefix tailTrace_1529867
  have hstable : (prefixWord ++ tailWord_1529867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529867).length < 2 ^ (prefixWord ++ tailWord_1529867).sum := by decide
  have hdescent : baseEnd_1529867 < baseStart_1529867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529884 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1529884 : Nat := 118140960795 + 1529884 * 2 ^ 59
def prefixEnd_1529884 : Nat := 4983230072969 + 3 ^ 40 * 1529884 * 2
def baseEnd_1529884 : Nat := 523710558415465037009465

theorem tailTrace_1529884 : CollatzResearch.WordTrace tailWord_1529884 prefixEnd_1529884 523710558415465037009465 := by
  unfold tailWord_1529884
  simp only [CollatzResearch.WordTrace]
  refine ⟨27899726794749513115238353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37199635726332684153651137 27899726794749513115238353)
  ·
    refine ⟨20924795096062134836428765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27899726794749513115238353 20924795096062134836428765)
    ·
      refine ⟨7846798161023300563660787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20924795096062134836428765 7846798161023300563660787)
      ·
        refine ⟨11770197241534950845491181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7846798161023300563660787 11770197241534950845491181)
        ·
          refine ⟨4413823965575606567059193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11770197241534950845491181 4413823965575606567059193)
          ·
            refine ⟨3310367974181704925294395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4413823965575606567059193 3310367974181704925294395)
            ·
              refine ⟨4965551961272557387941593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310367974181704925294395 4965551961272557387941593)
              ·
                refine ⟨3724163970954418040956195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4965551961272557387941593 3724163970954418040956195)
                ·
                  refine ⟨5586245956431627061434293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3724163970954418040956195 5586245956431627061434293)
                  ·
                    refine ⟨523710558415465037009465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5586245956431627061434293 523710558415465037009465)
                    ·
                      rfl

theorem cell22_1529884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1529884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529884 prefixEnd_1529884 := by exact prefixLift 1529884
  have htrace : WordTrace (prefixWord ++ tailWord_1529884) baseStart_1529884 baseEnd_1529884 := by
    simpa [prefixWord, tailWord_1529884, baseEnd_1529884] using wordTrace_append hprefix tailTrace_1529884
  have hstable : (prefixWord ++ tailWord_1529884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529884).length < 2 ^ (prefixWord ++ tailWord_1529884).sum := by decide
  have hdescent : baseEnd_1529884 < baseStart_1529884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529927 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1529927 : Nat := 118140960795 + 1529927 * 2 ^ 59
def prefixEnd_1529927 : Nat := 4983230072969 + 3 ^ 40 * 1529927 * 2
def baseEnd_1529927 : Nat := 523725278194227258184333

theorem tailTrace_1529927 : CollatzResearch.WordTrace tailWord_1529927 prefixEnd_1529927 523725278194227258184333 := by
  unfold tailWord_1529927
  simp only [CollatzResearch.WordTrace]
  refine ⟨55801021928343244574292035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37200681285562163049528023 55801021928343244574292035)
  ·
    refine ⟨83701532892514866861438053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55801021928343244574292035 83701532892514866861438053)
    ·
      refine ⟨15694037417346537536519635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83701532892514866861438053 15694037417346537536519635)
      ·
        refine ⟨23541056126019806304779453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15694037417346537536519635 23541056126019806304779453)
        ·
          refine ⟨8827896047257427364292295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23541056126019806304779453 8827896047257427364292295)
          ·
            refine ⟨13241844070886141046438443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8827896047257427364292295 13241844070886141046438443)
            ·
              refine ⟨19862766106329211569657665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13241844070886141046438443 19862766106329211569657665)
              ·
                refine ⟨14897074579746908677243249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19862766106329211569657665 14897074579746908677243249)
                ·
                  refine ⟨11172805934810181507932437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14897074579746908677243249 11172805934810181507932437)
                  ·
                    refine ⟨523725278194227258184333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11172805934810181507932437 523725278194227258184333)
                    ·
                      rfl

theorem cell22_1529927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1529927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529927 prefixEnd_1529927 := by exact prefixLift 1529927
  have htrace : WordTrace (prefixWord ++ tailWord_1529927) baseStart_1529927 baseEnd_1529927 := by
    simpa [prefixWord, tailWord_1529927, baseEnd_1529927] using wordTrace_append hprefix tailTrace_1529927
  have hstable : (prefixWord ++ tailWord_1529927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529927).length < 2 ^ (prefixWord ++ tailWord_1529927).sum := by decide
  have hdescent : baseEnd_1529927 < baseStart_1529927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1529929 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 3, 3]
def baseStart_1529929 : Nat := 118140960795 + 1529929 * 2 ^ 59
def prefixEnd_1529929 : Nat := 4983230072969 + 3 ^ 40 * 1529929 * 2
def baseEnd_1529929 : Nat := 523725962835099919634327

theorem tailTrace_1529929 : CollatzResearch.WordTrace tailWord_1529929 prefixEnd_1529929 523725962835099919634327 := by
  unfold tailWord_1529929
  simp only [CollatzResearch.WordTrace]
  refine ⟨55801094874335998915864841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37200729916223999277243227 55801094874335998915864841)
  ·
    refine ⟨41850821155751999186898631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55801094874335998915864841 41850821155751999186898631)
    ·
      refine ⟨62776231733627998780347947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41850821155751999186898631 62776231733627998780347947)
      ·
        refine ⟨94164347600441998170521921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62776231733627998780347947 94164347600441998170521921)
        ·
          refine ⟨70623260700331498627891441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94164347600441998170521921 70623260700331498627891441)
          ·
            refine ⟨52967445525248623970918581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70623260700331498627891441 52967445525248623970918581)
            ·
              refine ⟨4965698017992058497273617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52967445525248623970918581 4965698017992058497273617)
              ·
                refine ⟨3724273513494043872955213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4965698017992058497273617 3724273513494043872955213)
                ·
                  refine ⟨1396602567560266452358205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3724273513494043872955213 1396602567560266452358205)
                  ·
                    refine ⟨523725962835099919634327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396602567560266452358205 523725962835099919634327)
                    ·
                      rfl

theorem cell22_1529929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 3, 3].length) (baseStart_1529929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1529929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1529929 prefixEnd_1529929 := by exact prefixLift 1529929
  have htrace : WordTrace (prefixWord ++ tailWord_1529929) baseStart_1529929 baseEnd_1529929 := by
    simpa [prefixWord, tailWord_1529929, baseEnd_1529929] using wordTrace_append hprefix tailTrace_1529929
  have hstable : (prefixWord ++ tailWord_1529929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1529929).length < 2 ^ (prefixWord ++ tailWord_1529929).sum := by decide
  have hdescent : baseEnd_1529929 < baseStart_1529929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1529929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530034 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1530034 : Nat := 118140960795 + 1530034 * 2 ^ 59
def prefixEnd_1530034 : Nat := 4983230072969 + 3 ^ 40 * 1530034 * 2
def baseEnd_1530034 : Nat := 523761906480914645759005

theorem tailTrace_1530034 : CollatzResearch.WordTrace tailWord_1530034 prefixEnd_1530034 523761906480914645759005 := by
  unfold tailWord_1530034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951231134738900462109289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37203283025970401232291437 13951231134738900462109289)
  ·
    refine ⟨10463423351054175346581967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13951231134738900462109289 10463423351054175346581967)
    ·
      refine ⟨15695135026581263019872951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10463423351054175346581967 15695135026581263019872951)
      ·
        refine ⟨23542702539871894529809427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15695135026581263019872951 23542702539871894529809427)
        ·
          refine ⟨35314053809807841794714141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23542702539871894529809427 35314053809807841794714141)
          ·
            refine ⟨13242770178677940673017803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35314053809807841794714141 13242770178677940673017803)
            ·
              refine ⟨19864155268016911009526705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13242770178677940673017803 19864155268016911009526705)
              ·
                refine ⟨14898116451012683257145029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19864155268016911009526705 14898116451012683257145029)
                ·
                  refine ⟨2793396834564878110714693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14898116451012683257145029 2793396834564878110714693)
                  ·
                    refine ⟨523761906480914645759005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2793396834564878110714693 523761906480914645759005)
                    ·
                      rfl

theorem cell22_1530034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1530034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530034 prefixEnd_1530034 := by exact prefixLift 1530034
  have htrace : WordTrace (prefixWord ++ tailWord_1530034) baseStart_1530034 baseEnd_1530034 := by
    simpa [prefixWord, tailWord_1530034, baseEnd_1530034] using wordTrace_append hprefix tailTrace_1530034
  have hstable : (prefixWord ++ tailWord_1530034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530034).length < 2 ^ (prefixWord ++ tailWord_1530034).sum := by decide
  have hdescent : baseEnd_1530034 < baseStart_1530034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530070 : List Nat := [5, 2, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1530070 : Nat := 118140960795 + 1530070 * 2 ^ 59
def prefixEnd_1530070 : Nat := 4983230072969 + 3 ^ 40 * 1530070 * 2
def baseEnd_1530070 : Nat := 523774230016622551858895

theorem tailTrace_1530070 : CollatzResearch.WordTrace tailWord_1530070 prefixEnd_1530070 523774230016622551858895 := by
  unfold tailWord_1530070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487889847926573749796729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37204158377883453331165109 3487889847926573749796729)
  ·
    refine ⟨2615917385944930312347547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3487889847926573749796729 2615917385944930312347547)
    ·
      refine ⟨3923876078917395468521321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615917385944930312347547 3923876078917395468521321)
      ·
        refine ⟨2942907059188046601390991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3923876078917395468521321 2942907059188046601390991)
        ·
          refine ⟨4414360588782069902086487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942907059188046601390991 4414360588782069902086487)
          ·
            refine ⟨6621540883173104853129731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4414360588782069902086487 6621540883173104853129731)
            ·
              refine ⟨9932311324759657279694597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621540883173104853129731 9932311324759657279694597)
              ·
                refine ⟨1862308373392435739942737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9932311324759657279694597 1862308373392435739942737)
                ·
                  refine ⟨1396731280044326804957053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862308373392435739942737 1396731280044326804957053)
                  ·
                    refine ⟨523774230016622551858895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396731280044326804957053 523774230016622551858895)
                    ·
                      rfl

theorem cell22_1530070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1530070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530070 prefixEnd_1530070 := by exact prefixLift 1530070
  have htrace : WordTrace (prefixWord ++ tailWord_1530070) baseStart_1530070 baseEnd_1530070 := by
    simpa [prefixWord, tailWord_1530070, baseEnd_1530070] using wordTrace_append hprefix tailTrace_1530070
  have hstable : (prefixWord ++ tailWord_1530070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530070).length < 2 ^ (prefixWord ++ tailWord_1530070).sum := by decide
  have hdescent : baseEnd_1530070 < baseStart_1530070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530081 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1530081 : Nat := 118140960795 + 1530081 * 2 ^ 59
def prefixEnd_1530081 : Nat := 4983230072969 + 3 ^ 40 * 1530081 * 2
def baseEnd_1530081 : Nat := 523777995541422189833861

theorem tailTrace_1530081 : CollatzResearch.WordTrace tailWord_1530081 prefixEnd_1530081 523777995541422189833861 := by
  unfold tailWord_1530081
  simp only [CollatzResearch.WordTrace]
  refine ⟨55806638769785328875398097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37204425846523552583598731 55806638769785328875398097)
  ·
    refine ⟨41854979077338996656548573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55806638769785328875398097 41854979077338996656548573)
    ·
      refine ⟨15695617154002123746205715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41854979077338996656548573 15695617154002123746205715)
      ·
        refine ⟨23543425731003185619308573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15695617154002123746205715 23543425731003185619308573)
        ·
          refine ⟨8828784649126194607240715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23543425731003185619308573 8828784649126194607240715)
          ·
            refine ⟨13243176973689291910861073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8828784649126194607240715 13243176973689291910861073)
            ·
              refine ⟨9932382730266968933145805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13243176973689291910861073 9932382730266968933145805)
              ·
                refine ⟨3724643523850113349929677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9932382730266968933145805 3724643523850113349929677)
                ·
                  refine ⟨1396741321443792506223629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3724643523850113349929677 1396741321443792506223629)
                  ·
                    refine ⟨523777995541422189833861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396741321443792506223629 523777995541422189833861)
                    ·
                      rfl

theorem cell22_1530081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1530081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530081 prefixEnd_1530081 := by exact prefixLift 1530081
  have htrace : WordTrace (prefixWord ++ tailWord_1530081) baseStart_1530081 baseEnd_1530081 := by
    simpa [prefixWord, tailWord_1530081, baseEnd_1530081] using wordTrace_append hprefix tailTrace_1530081
  have hstable : (prefixWord ++ tailWord_1530081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530081).length < 2 ^ (prefixWord ++ tailWord_1530081).sum := by decide
  have hdescent : baseEnd_1530081 < baseStart_1530081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530083 : List Nat := [1, 1, 1, 8, 1, 2, 1, 7]
def baseStart_1530083 : Nat := 118140960795 + 1530083 * 2 ^ 59
def prefixEnd_1530083 : Nat := 4983230072969 + 3 ^ 40 * 1530083 * 2
def baseEnd_1530083 : Nat := 58197631131366094587095

theorem tailTrace_1530083 : CollatzResearch.WordTrace tailWord_1530083 prefixEnd_1530083 58197631131366094587095 := by
  unfold tailWord_1530083
  simp only [CollatzResearch.WordTrace]
  refine ⟨55806711715778083216970903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37204474477185388811313935 55806711715778083216970903)
  ·
    refine ⟨83710067573667124825456355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55806711715778083216970903 83710067573667124825456355)
    ·
      refine ⟨125565101360500687238184533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83710067573667124825456355 125565101360500687238184533)
      ·
        refine ⟨1471466031568367428572475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 125565101360500687238184533 1471466031568367428572475)
        ·
          refine ⟨2207199047352551142858713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471466031568367428572475 2207199047352551142858713)
          ·
            refine ⟨1655399285514413357144035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207199047352551142858713 1655399285514413357144035)
            ·
              refine ⟨2483098928271620035716053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655399285514413357144035 2483098928271620035716053)
              ·
                refine ⟨58197631131366094587095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2483098928271620035716053 58197631131366094587095)
                ·
                  rfl

theorem cell22_1530083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 7].length) (baseStart_1530083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530083 prefixEnd_1530083 := by exact prefixLift 1530083
  have htrace : WordTrace (prefixWord ++ tailWord_1530083) baseStart_1530083 baseEnd_1530083 := by
    simpa [prefixWord, tailWord_1530083, baseEnd_1530083] using wordTrace_append hprefix tailTrace_1530083
  have hstable : (prefixWord ++ tailWord_1530083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530083).length < 2 ^ (prefixWord ++ tailWord_1530083).sum := by decide
  have hdescent : baseEnd_1530083 < baseStart_1530083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530094 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_1530094 : Nat := 118140960795 + 1530094 * 2 ^ 59
def prefixEnd_1530094 : Nat := 4983230072969 + 3 ^ 40 * 1530094 * 2
def baseEnd_1530094 : Nat := 174594148569031496419607

theorem tailTrace_1530094 : CollatzResearch.WordTrace tailWord_1530094 prefixEnd_1530094 174594148569031496419607 := by
  unfold tailWord_1530094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975889114842279011952667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37204741945825488063747557 6975889114842279011952667)
  ·
    refine ⟨10463833672263418517929001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6975889114842279011952667 10463833672263418517929001)
    ·
      refine ⟨7847875254197563888446751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10463833672263418517929001 7847875254197563888446751)
      ·
        refine ⟨11771812881296345832670127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7847875254197563888446751 11771812881296345832670127)
        ·
          refine ⟨17657719321944518749005191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11771812881296345832670127 17657719321944518749005191)
          ·
            refine ⟨26486578982916778123507787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17657719321944518749005191 26486578982916778123507787)
            ·
              refine ⟨39729868474375167185261681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26486578982916778123507787 39729868474375167185261681)
              ·
                refine ⟨29797401355781375388946261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39729868474375167185261681 29797401355781375388946261)
                ·
                  refine ⟨174594148569031496419607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29797401355781375388946261 174594148569031496419607)
                  ·
                    rfl

theorem cell22_1530094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_1530094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530094 prefixEnd_1530094 := by exact prefixLift 1530094
  have htrace : WordTrace (prefixWord ++ tailWord_1530094) baseStart_1530094 baseEnd_1530094 := by
    simpa [prefixWord, tailWord_1530094, baseEnd_1530094] using wordTrace_append hprefix tailTrace_1530094
  have hstable : (prefixWord ++ tailWord_1530094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530094).length < 2 ^ (prefixWord ++ tailWord_1530094).sum := by decide
  have hdescent : baseEnd_1530094 < baseStart_1530094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530098 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_1530098 : Nat := 118140960795 + 1530098 * 2 ^ 59
def prefixEnd_1530098 : Nat := 4983230072969 + 3 ^ 40 * 1530098 * 2
def baseEnd_1530098 : Nat := 523783814988839812158809

theorem tailTrace_1530098 : CollatzResearch.WordTrace tailWord_1530098 prefixEnd_1530098 523783814988839812158809 := by
  unfold tailWord_1530098
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951814702680935194691737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37204839207149160519177965 13951814702680935194691737)
  ·
    refine ⟨10463861027010701396018803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13951814702680935194691737 10463861027010701396018803)
    ·
      refine ⟨15695791540516052094028205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10463861027010701396018803 15695791540516052094028205)
      ·
        refine ⟨5885921827693519535260577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15695791540516052094028205 5885921827693519535260577)
        ·
          refine ⟨4414441370770139651445433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5885921827693519535260577 4414441370770139651445433)
          ·
            refine ⟨3310831028077604738584075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4414441370770139651445433 3310831028077604738584075)
            ·
              refine ⟨4966246542116407107876113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310831028077604738584075 4966246542116407107876113)
              ·
                refine ⟨3724684906587305330907085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4966246542116407107876113 3724684906587305330907085)
                ·
                  refine ⟨1396756839970239499090157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3724684906587305330907085 1396756839970239499090157)
                  ·
                    refine ⟨523783814988839812158809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396756839970239499090157 523783814988839812158809)
                    ·
                      rfl

theorem cell22_1530098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_1530098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530098 prefixEnd_1530098 := by exact prefixLift 1530098
  have htrace : WordTrace (prefixWord ++ tailWord_1530098) baseStart_1530098 baseEnd_1530098 := by
    simpa [prefixWord, tailWord_1530098, baseEnd_1530098] using wordTrace_append hprefix tailTrace_1530098
  have hstable : (prefixWord ++ tailWord_1530098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530098).length < 2 ^ (prefixWord ++ tailWord_1530098).sum := by decide
  have hdescent : baseEnd_1530098 < baseStart_1530098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530139 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 6]
def baseStart_1530139 : Nat := 118140960795 + 1530139 * 2 ^ 59
def prefixEnd_1530139 : Nat := 4983230072969 + 3 ^ 40 * 1530139 * 2
def baseEnd_1530139 : Nat := 174599283375576457294561

theorem tailTrace_1530139 : CollatzResearch.WordTrace tailWord_1530139 prefixEnd_1530139 174599283375576457294561 := by
  unfold tailWord_1530139
  simp only [CollatzResearch.WordTrace]
  refine ⟨55808754203575204781009471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37205836135716803187339647 55808754203575204781009471)
  ·
    refine ⟨83713131305362807171514207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55808754203575204781009471 83713131305362807171514207)
    ·
      refine ⟨125569696958044210757271311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83713131305362807171514207 125569696958044210757271311)
      ·
        refine ⟨188354545437066316135906967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125569696958044210757271311 188354545437066316135906967)
        ·
          refine ⟨282531818155599474203860451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188354545437066316135906967 282531818155599474203860451)
          ·
            refine ⟨423797727233399211305790677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282531818155599474203860451 423797727233399211305790677)
            ·
              refine ⟨9932759232032794014979469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 423797727233399211305790677 9932759232032794014979469)
              ·
                refine ⟨3724784712012297755617301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9932759232032794014979469 3724784712012297755617301)
                ·
                  refine ⟨174599283375576457294561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3724784712012297755617301 174599283375576457294561)
                  ·
                    rfl

theorem cell22_1530139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 6].length) (baseStart_1530139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530139 prefixEnd_1530139 := by exact prefixLift 1530139
  have htrace : WordTrace (prefixWord ++ tailWord_1530139) baseStart_1530139 baseEnd_1530139 := by
    simpa [prefixWord, tailWord_1530139, baseEnd_1530139] using wordTrace_append hprefix tailTrace_1530139
  have hstable : (prefixWord ++ tailWord_1530139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530139).length < 2 ^ (prefixWord ++ tailWord_1530139).sum := by decide
  have hdescent : baseEnd_1530139 < baseStart_1530139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530184 : List Nat := [2, 1, 3, 1, 1, 2, 12]
def baseStart_1530184 : Nat := 118140960795 + 1530184 * 2 ^ 59
def prefixEnd_1530184 : Nat := 4983230072969 + 3 ^ 40 * 1530184 * 2
def baseEnd_1530184 : Nat := 19400490909124602018835

theorem tailTrace_1530184 : CollatzResearch.WordTrace tailWord_1530184 prefixEnd_1530184 19400490909124602018835 := by
  unfold tailWord_1530184
  simp only [CollatzResearch.WordTrace]
  refine ⟨27905197744206088733198803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37206930325608118310931737 27905197744206088733198803)
  ·
    refine ⟨41857796616309133099798205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27905197744206088733198803 41857796616309133099798205)
    ·
      refine ⟨15696673731115924912424327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41857796616309133099798205 15696673731115924912424327)
      ·
        refine ⟨23545010596673887368636491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15696673731115924912424327 23545010596673887368636491)
        ·
          refine ⟨35317515895010831052954737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23545010596673887368636491 35317515895010831052954737)
          ·
            refine ⟨26488136921258123289716053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35317515895010831052954737 26488136921258123289716053)
            ·
              refine ⟨19400490909124602018835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 26488136921258123289716053 19400490909124602018835)
              ·
                rfl

theorem cell22_1530184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 12].length) (baseStart_1530184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530184 prefixEnd_1530184 := by exact prefixLift 1530184
  have htrace : WordTrace (prefixWord ++ tailWord_1530184) baseStart_1530184 baseEnd_1530184 := by
    simpa [prefixWord, tailWord_1530184, baseEnd_1530184] using wordTrace_append hprefix tailTrace_1530184
  have hstable : (prefixWord ++ tailWord_1530184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530184).length < 2 ^ (prefixWord ++ tailWord_1530184).sum := by decide
  have hdescent : baseEnd_1530184 < baseStart_1530184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530188 : List Nat := [2, 2, 1, 3, 2, 1, 2, 4, 2, 3]
def baseStart_1530188 : Nat := 118140960795 + 1530188 * 2 ^ 59
def prefixEnd_1530188 : Nat := 4983230072969 + 3 ^ 40 * 1530188 * 2
def baseEnd_1530188 : Nat := 523814623828109577408533

theorem tailTrace_1530188 : CollatzResearch.WordTrace tailWord_1530188 prefixEnd_1530188 523814623828109577408533 := by
  unfold tailWord_1530188
  simp only [CollatzResearch.WordTrace]
  refine ⟨27905270690198843074771609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37207027586931790766362145 27905270690198843074771609)
  ·
    refine ⟨20928953017649132306078707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27905270690198843074771609 20928953017649132306078707)
    ·
      refine ⟨31393429526473698459118061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20928953017649132306078707 31393429526473698459118061)
      ·
        refine ⟨11772536072427636922169273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31393429526473698459118061 11772536072427636922169273)
        ·
          refine ⟨8829402054320727691626955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11772536072427636922169273 8829402054320727691626955)
          ·
            refine ⟨13244103081481091537440433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8829402054320727691626955 13244103081481091537440433)
            ·
              refine ⟨9933077311110818653080325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13244103081481091537440433 9933077311110818653080325)
              ·
                refine ⟨1862451995833278497452561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9933077311110818653080325 1862451995833278497452561)
                ·
                  refine ⟨1396838996874958873089421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862451995833278497452561 1396838996874958873089421)
                  ·
                    refine ⟨523814623828109577408533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1396838996874958873089421 523814623828109577408533)
                    ·
                      rfl

theorem cell22_1530188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_1530188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530188 prefixEnd_1530188 := by exact prefixLift 1530188
  have htrace : WordTrace (prefixWord ++ tailWord_1530188) baseStart_1530188 baseEnd_1530188 := by
    simpa [prefixWord, tailWord_1530188, baseEnd_1530188] using wordTrace_append hprefix tailTrace_1530188
  have hstable : (prefixWord ++ tailWord_1530188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530188).length < 2 ^ (prefixWord ++ tailWord_1530188).sum := by decide
  have hdescent : baseEnd_1530188 < baseStart_1530188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530336 : List Nat := [2, 1, 1, 3, 1, 1, 5, 8]
def baseStart_1530336 : Nat := 118140960795 + 1530336 * 2 ^ 59
def prefixEnd_1530336 : Nat := 4983230072969 + 3 ^ 40 * 1530336 * 2
def baseEnd_1530336 : Nat := 58207254139187391634231

theorem tailTrace_1530336 : CollatzResearch.WordTrace tailWord_1530336 prefixEnd_1530336 58207254139187391634231 := by
  unfold tailWord_1530336
  simp only [CollatzResearch.WordTrace]
  refine ⟨27907969691930753712965431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37210626255907671617287241 27907969691930753712965431)
  ·
    refine ⟨41861954537896130569448147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27907969691930753712965431 41861954537896130569448147)
    ·
      refine ⟨62792931806844195854172221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41861954537896130569448147 62792931806844195854172221)
      ·
        refine ⟨23547349427566573445314583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62792931806844195854172221 23547349427566573445314583)
        ·
          refine ⟨35321024141349860167971875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23547349427566573445314583 35321024141349860167971875)
          ·
            refine ⟨52981536212024790251957813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35321024141349860167971875 52981536212024790251957813)
            ·
              refine ⟨4967019019877324086121045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52981536212024790251957813 4967019019877324086121045)
              ·
                refine ⟨58207254139187391634231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4967019019877324086121045 58207254139187391634231)
                ·
                  rfl

theorem cell22_1530336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 8].length) (baseStart_1530336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530336 prefixEnd_1530336 := by exact prefixLift 1530336
  have htrace : WordTrace (prefixWord ++ tailWord_1530336) baseStart_1530336 baseEnd_1530336 := by
    simpa [prefixWord, tailWord_1530336, baseEnd_1530336] using wordTrace_append hprefix tailTrace_1530336
  have hstable : (prefixWord ++ tailWord_1530336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530336).length < 2 ^ (prefixWord ++ tailWord_1530336).sum := by decide
  have hdescent : baseEnd_1530336 < baseStart_1530336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530402 : List Nat := [3, 3, 1, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1530402 : Nat := 118140960795 + 1530402 * 2 ^ 59
def prefixEnd_1530402 : Nat := 4983230072969 + 3 ^ 40 * 1530402 * 2
def baseEnd_1530402 : Nat := 523887880401484352557877

theorem tailTrace_1530402 : CollatzResearch.WordTrace tailWord_1530402 prefixEnd_1530402 523887880401484352557877 := by
  unfold tailWord_1530402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13954586650405600174458365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37212231067748267131888973 13954586650405600174458365)
  ·
    refine ⟨5232969993902100065421887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13954586650405600174458365 5232969993902100065421887)
    ·
      refine ⟨7849454990853150098132831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5232969993902100065421887 7849454990853150098132831)
      ·
        refine ⟨11774182486279725147199247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849454990853150098132831 11774182486279725147199247)
        ·
          refine ⟨17661273729419587720798871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11774182486279725147199247 17661273729419587720798871)
          ·
            refine ⟨26491910594129381581198307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17661273729419587720798871 26491910594129381581198307)
            ·
              refine ⟨39737865891194072371797461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26491910594129381581198307 39737865891194072371797461)
              ·
                refine ⟨931356231824861071214003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39737865891194072371797461 931356231824861071214003)
                ·
                  refine ⟨1397034347737291606821005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931356231824861071214003 1397034347737291606821005)
                  ·
                    refine ⟨523887880401484352557877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397034347737291606821005 523887880401484352557877)
                    ·
                      rfl

theorem cell22_1530402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1530402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530402 prefixEnd_1530402 := by exact prefixLift 1530402
  have htrace : WordTrace (prefixWord ++ tailWord_1530402) baseStart_1530402 baseEnd_1530402 := by
    simpa [prefixWord, tailWord_1530402, baseEnd_1530402] using wordTrace_append hprefix tailTrace_1530402
  have hstable : (prefixWord ++ tailWord_1530402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530402).length < 2 ^ (prefixWord ++ tailWord_1530402).sum := by decide
  have hdescent : baseEnd_1530402 < baseStart_1530402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530436 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1530436 : Nat := 118140960795 + 1530436 * 2 ^ 59
def prefixEnd_1530436 : Nat := 4983230072969 + 3 ^ 40 * 1530436 * 2
def baseEnd_1530436 : Nat := 523899519296319597207773

theorem tailTrace_1530436 : CollatzResearch.WordTrace tailWord_1530436 prefixEnd_1530436 523899519296319597207773 := by
  unfold tailWord_1530436
  simp only [CollatzResearch.WordTrace]
  refine ⟨27909793341749612252285581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37213057788999483003047441 27909793341749612252285581)
  ·
    refine ⟨10466172503156104594607093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27909793341749612252285581 10466172503156104594607093)
    ·
      refine ⟨981203672170884805744415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10466172503156104594607093 981203672170884805744415)
      ·
        refine ⟨1471805508256327208616623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 981203672170884805744415 1471805508256327208616623)
        ·
          refine ⟨2207708262384490812924935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471805508256327208616623 2207708262384490812924935)
          ·
            refine ⟨3311562393576736219387403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207708262384490812924935 3311562393576736219387403)
            ·
              refine ⟨4967343590365104329081105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3311562393576736219387403 4967343590365104329081105)
              ·
                refine ⟨3725507692773828246810829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4967343590365104329081105 3725507692773828246810829)
                ·
                  refine ⟨1397065384790185592554061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3725507692773828246810829 1397065384790185592554061)
                  ·
                    refine ⟨523899519296319597207773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397065384790185592554061 523899519296319597207773)
                    ·
                      rfl

theorem cell22_1530436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1530436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530436 prefixEnd_1530436 := by exact prefixLift 1530436
  have htrace : WordTrace (prefixWord ++ tailWord_1530436) baseStart_1530436 baseEnd_1530436 := by
    simpa [prefixWord, tailWord_1530436, baseEnd_1530436] using wordTrace_append hprefix tailTrace_1530436
  have hstable : (prefixWord ++ tailWord_1530436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530436).length < 2 ^ (prefixWord ++ tailWord_1530436).sum := by decide
  have hdescent : baseEnd_1530436 < baseStart_1530436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530466 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_1530466 : Nat := 118140960795 + 1530466 * 2 ^ 59
def prefixEnd_1530466 : Nat := 4983230072969 + 3 ^ 40 * 1530466 * 2
def baseEnd_1530466 : Nat := 174636596303136506319227

theorem tailTrace_1530466 : CollatzResearch.WordTrace tailWord_1530466 prefixEnd_1530466 174636596303136506319227 := by
  unfold tailWord_1530466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955170218347634907040813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37213787248927026418775501 13955170218347634907040813)
  ·
    refine ⟨5233188831880363090140305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13955170218347634907040813 5233188831880363090140305)
    ·
      refine ⟨3924891623910272317605229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5233188831880363090140305 3924891623910272317605229)
      ·
        refine ⟨1471834358966352119101961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3924891623910272317605229 1471834358966352119101961)
        ·
          refine ⟨1103875769224764089326471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1471834358966352119101961 1103875769224764089326471)
          ·
            refine ⟨1655813653837146133989707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1103875769224764089326471 1655813653837146133989707)
            ·
              refine ⟨2483720480755719200984561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1655813653837146133989707 2483720480755719200984561)
              ·
                refine ⟨1862790360566789400738421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2483720480755719200984561 1862790360566789400738421)
                ·
                  refine ⟨174636596303136506319227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1862790360566789400738421 174636596303136506319227)
                  ·
                    rfl

theorem cell22_1530466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_1530466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530466 prefixEnd_1530466 := by exact prefixLift 1530466
  have htrace : WordTrace (prefixWord ++ tailWord_1530466) baseStart_1530466 baseEnd_1530466 := by
    simpa [prefixWord, tailWord_1530466, baseEnd_1530466] using wordTrace_append hprefix tailTrace_1530466
  have hstable : (prefixWord ++ tailWord_1530466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530466).length < 2 ^ (prefixWord ++ tailWord_1530466).sum := by decide
  have hdescent : baseEnd_1530466 < baseStart_1530466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530473 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 4, 4]
def baseStart_1530473 : Nat := 118140960795 + 1530473 * 2 ^ 59
def prefixEnd_1530473 : Nat := 4983230072969 + 3 ^ 40 * 1530473 * 2
def baseEnd_1530473 : Nat := 523912185152463834032659

theorem tailTrace_1530473 : CollatzResearch.WordTrace tailWord_1530473 prefixEnd_1530473 523912185152463834032659 := by
  unfold tailWord_1530473
  simp only [CollatzResearch.WordTrace]
  refine ⟨55820936184365179823668073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37213957456243453215778715 55820936184365179823668073)
  ·
    refine ⟨41865702138273884867751055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55820936184365179823668073 41865702138273884867751055)
    ·
      refine ⟨62798553207410827301626583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41865702138273884867751055 62798553207410827301626583)
      ·
        refine ⟨94197829811116240952439875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62798553207410827301626583 94197829811116240952439875)
        ·
          refine ⟨141296744716674361428659813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94197829811116240952439875 141296744716674361428659813)
          ·
            refine ⟨26493139634376442767873715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141296744716674361428659813 26493139634376442767873715)
            ·
              refine ⟨39739709451564664151810573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26493139634376442767873715 39739709451564664151810573)
              ·
                refine ⟨14902391044336749056928965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39739709451564664151810573 14902391044336749056928965)
                ·
                  refine ⟨2794198320813140448174181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14902391044336749056928965 2794198320813140448174181)
                  ·
                    refine ⟨523912185152463834032659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794198320813140448174181 523912185152463834032659)
                    ·
                      rfl

theorem cell22_1530473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_1530473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530473 prefixEnd_1530473 := by exact prefixLift 1530473
  have htrace : WordTrace (prefixWord ++ tailWord_1530473) baseStart_1530473 baseEnd_1530473 := by
    simpa [prefixWord, tailWord_1530473, baseEnd_1530473] using wordTrace_append hprefix tailTrace_1530473
  have hstable : (prefixWord ++ tailWord_1530473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530473).length < 2 ^ (prefixWord ++ tailWord_1530473).sum := by decide
  have hdescent : baseEnd_1530473 < baseStart_1530473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530475 : List Nat := [1, 1, 1, 1, 2, 2, 1, 8, 2, 3]
def baseStart_1530475 : Nat := 118140960795 + 1530475 * 2 ^ 59
def prefixEnd_1530475 : Nat := 4983230072969 + 3 ^ 40 * 1530475 * 2
def baseEnd_1530475 : Nat := 523912869793336495482653

theorem tailTrace_1530475 : CollatzResearch.WordTrace tailWord_1530475 prefixEnd_1530475 523912869793336495482653 := by
  unfold tailWord_1530475
  simp only [CollatzResearch.WordTrace]
  refine ⟨55821009130357934165240879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37214006086905289443493919 55821009130357934165240879)
  ·
    refine ⟨83731513695536901247861319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55821009130357934165240879 83731513695536901247861319)
    ·
      refine ⟨125597270543305351871791979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83731513695536901247861319 125597270543305351871791979)
      ·
        refine ⟨188395905814958027807687969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125597270543305351871791979 188395905814958027807687969)
        ·
          refine ⟨141296929361218520855765977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188395905814958027807687969 141296929361218520855765977)
          ·
            refine ⟨105972697020913890641824483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141296929361218520855765977 105972697020913890641824483)
            ·
              refine ⟨158959045531370835962736725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105972697020913890641824483 158959045531370835962736725)
              ·
                refine ⟨1862801314820751983938321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 158959045531370835962736725 1862801314820751983938321)
                ·
                  refine ⟨1397100986115563987953741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1862801314820751983938321 1397100986115563987953741)
                  ·
                    refine ⟨523912869793336495482653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397100986115563987953741 523912869793336495482653)
                    ·
                      rfl

theorem cell22_1530475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 2, 3].length) (baseStart_1530475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530475 prefixEnd_1530475 := by exact prefixLift 1530475
  have htrace : WordTrace (prefixWord ++ tailWord_1530475) baseStart_1530475 baseEnd_1530475 := by
    simpa [prefixWord, tailWord_1530475, baseEnd_1530475] using wordTrace_append hprefix tailTrace_1530475
  have hstable : (prefixWord ++ tailWord_1530475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530475).length < 2 ^ (prefixWord ++ tailWord_1530475).sum := by decide
  have hdescent : baseEnd_1530475 < baseStart_1530475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530477 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1530477 : Nat := 118140960795 + 1530477 * 2 ^ 59
def prefixEnd_1530477 : Nat := 4983230072969 + 3 ^ 40 * 1530477 * 2
def baseEnd_1530477 : Nat := 174637851478069718977549

theorem tailTrace_1530477 : CollatzResearch.WordTrace tailWord_1530477 prefixEnd_1530477 174637851478069718977549 := by
  unfold tailWord_1530477
  simp only [CollatzResearch.WordTrace]
  refine ⟨55821082076350688506813685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37214054717567125671209123 55821082076350688506813685)
  ·
    refine ⟨5233226444657877047513783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55821082076350688506813685 5233226444657877047513783)
    ·
      refine ⟨7849839666986815571270675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233226444657877047513783 7849839666986815571270675)
      ·
        refine ⟨11774759500480223356906013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849839666986815571270675 11774759500480223356906013)
        ·
          refine ⟨4415534812680083758839755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11774759500480223356906013 4415534812680083758839755)
          ·
            refine ⟨6623302219020125638259633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415534812680083758839755 6623302219020125638259633)
            ·
              refine ⟨4967476664265094228694725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6623302219020125638259633 4967476664265094228694725)
              ·
                refine ⟨931401874549705167880261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4967476664265094228694725 931401874549705167880261)
                ·
                  refine ⟨174637851478069718977549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 931401874549705167880261 174637851478069718977549)
                  ·
                    rfl

theorem cell22_1530477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1530477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530477 prefixEnd_1530477 := by exact prefixLift 1530477
  have htrace : WordTrace (prefixWord ++ tailWord_1530477) baseStart_1530477 baseEnd_1530477 := by
    simpa [prefixWord, tailWord_1530477, baseEnd_1530477] using wordTrace_append hprefix tailTrace_1530477
  have hstable : (prefixWord ++ tailWord_1530477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530477).length < 2 ^ (prefixWord ++ tailWord_1530477).sum := by decide
  have hdescent : baseEnd_1530477 < baseStart_1530477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530503 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1530503 : Nat := 118140960795 + 1530503 * 2 ^ 59
def prefixEnd_1530503 : Nat := 4983230072969 + 3 ^ 40 * 1530503 * 2
def baseEnd_1530503 : Nat := 523922454765553755782567

theorem tailTrace_1530503 : CollatzResearch.WordTrace tailWord_1530503 prefixEnd_1530503 523922454765553755782567 := by
  unfold tailWord_1530503
  simp only [CollatzResearch.WordTrace]
  refine ⟨55822030374256494947260163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37214686916170996631506775 55822030374256494947260163)
  ·
    refine ⟨83733045561384742420890245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55822030374256494947260163 83733045561384742420890245)
    ·
      refine ⟨15699946042759639203916921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83733045561384742420890245 15699946042759639203916921)
      ·
        refine ⟨11774959532069729402937691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15699946042759639203916921 11774959532069729402937691)
        ·
          refine ⟨17662439298104594104406537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11774959532069729402937691 17662439298104594104406537)
          ·
            refine ⟨13246829473578445578304903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17662439298104594104406537 13246829473578445578304903)
            ·
              refine ⟨19870244210367668367457355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13246829473578445578304903 19870244210367668367457355)
              ·
                refine ⟨29805366315551502551186033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19870244210367668367457355 29805366315551502551186033)
                ·
                  refine ⟨22354024736663626913389525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29805366315551502551186033 22354024736663626913389525)
                  ·
                    refine ⟨523922454765553755782567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22354024736663626913389525 523922454765553755782567)
                    ·
                      rfl

theorem cell22_1530503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1530503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530503 prefixEnd_1530503 := by exact prefixLift 1530503
  have htrace : WordTrace (prefixWord ++ tailWord_1530503) baseStart_1530503 baseEnd_1530503 := by
    simpa [prefixWord, tailWord_1530503, baseEnd_1530503] using wordTrace_append hprefix tailTrace_1530503
  have hstable : (prefixWord ++ tailWord_1530503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530503).length < 2 ^ (prefixWord ++ tailWord_1530503).sum := by decide
  have hdescent : baseEnd_1530503 < baseStart_1530503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530522 : List Nat := [3, 1, 1, 6, 1, 2, 8]
def baseStart_1530522 : Nat := 118140960795 + 1530522 * 2 ^ 59
def prefixEnd_1530522 : Nat := 4983230072969 + 3 ^ 40 * 1530522 * 2
def baseEnd_1530522 : Nat := 19404776253846075539167

theorem tailTrace_1530522 : CollatzResearch.WordTrace tailWord_1530522 prefixEnd_1530522 19404776253846075539167 := by
  unfold tailWord_1530522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13955680840296915298050455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37215148907458440794801213 13955680840296915298050455)
  ·
    refine ⟨20933521260445372947075683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13955680840296915298050455 20933521260445372947075683)
    ·
      refine ⟨31400281890668059420613525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20933521260445372947075683 31400281890668059420613525)
      ·
        refine ⟨1471888213625065285341259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31400281890668059420613525 1471888213625065285341259)
        ·
          refine ⟨2207832320437597928011889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471888213625065285341259 2207832320437597928011889)
          ·
            refine ⟨1655874240328198446008917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2207832320437597928011889 1655874240328198446008917)
            ·
              refine ⟨19404776253846075539167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1655874240328198446008917 19404776253846075539167)
              ·
                rfl

theorem cell22_1530522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 8].length) (baseStart_1530522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530522 prefixEnd_1530522 := by exact prefixLift 1530522
  have htrace : WordTrace (prefixWord ++ tailWord_1530522) baseStart_1530522 baseEnd_1530522 := by
    simpa [prefixWord, tailWord_1530522, baseEnd_1530522] using wordTrace_append hprefix tailTrace_1530522
  have hstable : (prefixWord ++ tailWord_1530522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530522).length < 2 ^ (prefixWord ++ tailWord_1530522).sum := by decide
  have hdescent : baseEnd_1530522 < baseStart_1530522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530588 : List Nat := [2, 2, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1530588 : Nat := 118140960795 + 1530588 * 2 ^ 59
def prefixEnd_1530588 : Nat := 4983230072969 + 3 ^ 40 * 1530588 * 2
def baseEnd_1530588 : Nat := 523951552002641867407307

theorem tailTrace_1530588 : CollatzResearch.WordTrace tailWord_1530588 prefixEnd_1530588 523951552002641867407307 := by
  unfold tailWord_1530588
  simp only [CollatzResearch.WordTrace]
  refine ⟨27912565289474277232052209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37216753719299036309402945 27912565289474277232052209)
  ·
    refine ⟨20934423967105707924039157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27912565289474277232052209 20934423967105707924039157)
    ·
      refine ⟨1962602246916160117878671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20934423967105707924039157 1962602246916160117878671)
      ·
        refine ⟨2943903370374240176818007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962602246916160117878671 2943903370374240176818007)
        ·
          refine ⟨4415855055561360265227011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943903370374240176818007 4415855055561360265227011)
          ·
            refine ⟨6623782583342040397840517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415855055561360265227011 6623782583342040397840517)
            ·
              refine ⟨1241959234376632574595097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6623782583342040397840517 1241959234376632574595097)
              ·
                refine ⟨931469425782474430946323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241959234376632574595097 931469425782474430946323)
                ·
                  refine ⟨1397204138673711646419485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931469425782474430946323 1397204138673711646419485)
                  ·
                    refine ⟨523951552002641867407307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397204138673711646419485 523951552002641867407307)
                    ·
                      rfl

theorem cell22_1530588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1530588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530588 prefixEnd_1530588 := by exact prefixLift 1530588
  have htrace : WordTrace (prefixWord ++ tailWord_1530588) baseStart_1530588 baseEnd_1530588 := by
    simpa [prefixWord, tailWord_1530588, baseEnd_1530588] using wordTrace_append hprefix tailTrace_1530588
  have hstable : (prefixWord ++ tailWord_1530588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530588).length < 2 ^ (prefixWord ++ tailWord_1530588).sum := by decide
  have hdescent : baseEnd_1530588 < baseStart_1530588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530631 : List Nat := [1, 1, 4, 4, 1, 3, 2, 1, 1, 4]
def baseStart_1530631 : Nat := 118140960795 + 1530631 * 2 ^ 59
def prefixEnd_1530631 : Nat := 4983230072969 + 3 ^ 40 * 1530631 * 2
def baseEnd_1530631 : Nat := 523966271781404088582175

theorem tailTrace_1530631 : CollatzResearch.WordTrace tailWord_1530631 prefixEnd_1530631 523966271781404088582175 := by
  unfold tailWord_1530631
  simp only [CollatzResearch.WordTrace]
  refine ⟨55826698917792772807919747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37217799278528515205279831 55826698917792772807919747)
  ·
    refine ⟨83740048376689159211879621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55826698917792772807919747 83740048376689159211879621)
    ·
      refine ⟨15701259070629217352227429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83740048376689159211879621 15701259070629217352227429)
      ·
        refine ⟨2943986075742978253542643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15701259070629217352227429 2943986075742978253542643)
        ·
          refine ⟨4415979113614467380313965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943986075742978253542643 4415979113614467380313965)
          ·
            refine ⟨1655992167605425267617737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4415979113614467380313965 1655992167605425267617737)
            ·
              refine ⟨1241994125704068950713303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655992167605425267617737 1241994125704068950713303)
              ·
                refine ⟨1862991188556103426069955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241994125704068950713303 1862991188556103426069955)
                ·
                  refine ⟨2794486782834155139104933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1862991188556103426069955 2794486782834155139104933)
                  ·
                    refine ⟨523966271781404088582175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794486782834155139104933 523966271781404088582175)
                    ·
                      rfl

theorem cell22_1530631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_1530631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530631 prefixEnd_1530631 := by exact prefixLift 1530631
  have htrace : WordTrace (prefixWord ++ tailWord_1530631) baseStart_1530631 baseEnd_1530631 := by
    simpa [prefixWord, tailWord_1530631, baseEnd_1530631] using wordTrace_append hprefix tailTrace_1530631
  have hstable : (prefixWord ++ tailWord_1530631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530631).length < 2 ^ (prefixWord ++ tailWord_1530631).sum := by decide
  have hdescent : baseEnd_1530631 < baseStart_1530631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530732 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1530732 : Nat := 118140960795 + 1530732 * 2 ^ 59
def prefixEnd_1530732 : Nat := 4983230072969 + 3 ^ 40 * 1530732 * 2
def baseEnd_1530732 : Nat := 524000846145473491806865

theorem tailTrace_1530732 : CollatzResearch.WordTrace tailWord_1530732 prefixEnd_1530732 524000846145473491806865 := by
  unfold tailWord_1530732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27915191345213433528673225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37220255126951244704897633 27915191345213433528673225)
  ·
    refine ⟨20936393508910075146504919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27915191345213433528673225 20936393508910075146504919)
    ·
      refine ⟨31404590263365112719757379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20936393508910075146504919 31404590263365112719757379)
      ·
        refine ⟨47106885395047669079636069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31404590263365112719757379 47106885395047669079636069)
        ·
          refine ⟨8832541011571437952431763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47106885395047669079636069 8832541011571437952431763)
          ·
            refine ⟨13248811517357156928647645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8832541011571437952431763 13248811517357156928647645)
            ·
              refine ⟨4968304319008933848242867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13248811517357156928647645 4968304319008933848242867)
              ·
                refine ⟨7452456478513400772364301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968304319008933848242867 7452456478513400772364301)
                ·
                  refine ⟨2794671179442525289636613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7452456478513400772364301 2794671179442525289636613)
                  ·
                    refine ⟨524000846145473491806865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794671179442525289636613 524000846145473491806865)
                    ·
                      rfl

theorem cell22_1530732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1530732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530732 prefixEnd_1530732 := by exact prefixLift 1530732
  have htrace : WordTrace (prefixWord ++ tailWord_1530732) baseStart_1530732 baseEnd_1530732 := by
    simpa [prefixWord, tailWord_1530732, baseEnd_1530732] using wordTrace_append hprefix tailTrace_1530732
  have hstable : (prefixWord ++ tailWord_1530732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530732).length < 2 ^ (prefixWord ++ tailWord_1530732).sum := by decide
  have hdescent : baseEnd_1530732 < baseStart_1530732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530813 : List Nat := [1, 4, 1, 2, 4, 2, 1, 2, 2, 3]
def baseStart_1530813 : Nat := 118140960795 + 1530813 * 2 ^ 59
def prefixEnd_1530813 : Nat := 4983230072969 + 3 ^ 40 * 1530813 * 2
def baseEnd_1530813 : Nat := 524028574100816280531617

theorem tailTrace_1530813 : CollatzResearch.WordTrace tailWord_1530813 prefixEnd_1530813 524028574100816280531617 := by
  unfold tailWord_1530813
  simp only [CollatzResearch.WordTrace]
  refine ⟨55833337003133417891045093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37222224668755611927363395 55833337003133417891045093)
  ·
    refine ⟨10468750688087515854570955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55833337003133417891045093 10468750688087515854570955)
    ·
      refine ⟨15703126032131273781856433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10468750688087515854570955 15703126032131273781856433)
      ·
        refine ⟨11777344524098455336392325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15703126032131273781856433 11777344524098455336392325)
        ·
          refine ⟨2208252098268460375573561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11777344524098455336392325 2208252098268460375573561)
          ·
            refine ⟨1656189073701345281680171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208252098268460375573561 1656189073701345281680171)
            ·
              refine ⟨2484283610552017922520257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656189073701345281680171 2484283610552017922520257)
              ·
                refine ⟨1863212707914013441890193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2484283610552017922520257 1863212707914013441890193)
                ·
                  refine ⟨1397409530935510081417645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1863212707914013441890193 1397409530935510081417645)
                  ·
                    refine ⟨524028574100816280531617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397409530935510081417645 524028574100816280531617)
                    ·
                      rfl

theorem cell22_1530813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 2, 2, 3].length) (baseStart_1530813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530813 prefixEnd_1530813 := by exact prefixLift 1530813
  have htrace : WordTrace (prefixWord ++ tailWord_1530813) baseStart_1530813 baseEnd_1530813 := by
    simpa [prefixWord, tailWord_1530813, baseEnd_1530813] using wordTrace_append hprefix tailTrace_1530813
  have hstable : (prefixWord ++ tailWord_1530813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530813).length < 2 ^ (prefixWord ++ tailWord_1530813).sum := by decide
  have hdescent : baseEnd_1530813 < baseStart_1530813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530852 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_1530852 : Nat := 118140960795 + 1530852 * 2 ^ 59
def prefixEnd_1530852 : Nat := 4983230072969 + 3 ^ 40 * 1530852 * 2
def baseEnd_1530852 : Nat := 524041924597833178806497

theorem tailTrace_1530852 : CollatzResearch.WordTrace tailWord_1530852 prefixEnd_1530852 524041924597833178806497 := by
  unfold tailWord_1530852
  simp only [CollatzResearch.WordTrace]
  refine ⟨27917379724996063775857405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37223172966661418367809873 27917379724996063775857405)
  ·
    refine ⟨10469017396873523915946527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27917379724996063775857405 10469017396873523915946527)
    ·
      refine ⟨15703526095310285873919791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10469017396873523915946527 15703526095310285873919791)
      ·
        refine ⟨23555289142965428810879687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15703526095310285873919791 23555289142965428810879687)
        ·
          refine ⟨35332933714448143216319531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23555289142965428810879687 35332933714448143216319531)
          ·
            refine ⟨52999400571672214824479297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35332933714448143216319531 52999400571672214824479297)
            ·
              refine ⟨39749550428754161118359473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52999400571672214824479297 39749550428754161118359473)
              ·
                refine ⟨29812162821565620838769605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39749550428754161118359473 29812162821565620838769605)
                ·
                  refine ⟨5589780529043553907269301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29812162821565620838769605 5589780529043553907269301)
                  ·
                    refine ⟨524041924597833178806497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5589780529043553907269301 524041924597833178806497)
                    ·
                      rfl

theorem cell22_1530852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_1530852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530852 prefixEnd_1530852 := by exact prefixLift 1530852
  have htrace : WordTrace (prefixWord ++ tailWord_1530852) baseStart_1530852 baseEnd_1530852 := by
    simpa [prefixWord, tailWord_1530852, baseEnd_1530852] using wordTrace_append hprefix tailTrace_1530852
  have hstable : (prefixWord ++ tailWord_1530852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530852).length < 2 ^ (prefixWord ++ tailWord_1530852).sum := by decide
  have hdescent : baseEnd_1530852 < baseStart_1530852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530858 : List Nat := [3, 1, 3, 1, 2, 2, 3, 3, 1, 3]
def baseStart_1530858 : Nat := 118140960795 + 1530858 * 2 ^ 59
def prefixEnd_1530858 : Nat := 4983230072969 + 3 ^ 40 * 1530858 * 2
def baseEnd_1530858 : Nat := 524043978520451163156479

theorem tailTrace_1530858 : CollatzResearch.WordTrace tailWord_1530858 prefixEnd_1530858 524043978520451163156479 := by
  unfold tailWord_1530858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13958744571992597644108307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37223318858646927050955485 13958744571992597644108307)
  ·
    refine ⟨20938116857988896466162461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13958744571992597644108307 20938116857988896466162461)
    ·
      refine ⟨7851793821745836174810923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20938116857988896466162461 7851793821745836174810923)
      ·
        refine ⟨11777690732618754262216385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7851793821745836174810923 11777690732618754262216385)
        ·
          refine ⟨8833268049464065696662289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11777690732618754262216385 8833268049464065696662289)
          ·
            refine ⟨6624951037098049272496717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8833268049464065696662289 6624951037098049272496717)
            ·
              refine ⟨2484356638911768477186269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6624951037098049272496717 2484356638911768477186269)
              ·
                refine ⟨931633739591913178944851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2484356638911768477186269 931633739591913178944851)
                ·
                  refine ⟨1397450609387869768417277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931633739591913178944851 1397450609387869768417277)
                  ·
                    refine ⟨524043978520451163156479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397450609387869768417277 524043978520451163156479)
                    ·
                      rfl

theorem cell22_1530858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_1530858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530858 prefixEnd_1530858 := by exact prefixLift 1530858
  have htrace : WordTrace (prefixWord ++ tailWord_1530858) baseStart_1530858 baseEnd_1530858 := by
    simpa [prefixWord, tailWord_1530858, baseEnd_1530858] using wordTrace_append hprefix tailTrace_1530858
  have hstable : (prefixWord ++ tailWord_1530858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530858).length < 2 ^ (prefixWord ++ tailWord_1530858).sum := by decide
  have hdescent : baseEnd_1530858 < baseStart_1530858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530867 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 7, 4]
def baseStart_1530867 : Nat := 118140960795 + 1530867 * 2 ^ 59
def prefixEnd_1530867 : Nat := 4983230072969 + 3 ^ 40 * 1530867 * 2
def baseEnd_1530867 : Nat := 524047059404378139681451

theorem tailTrace_1530867 : CollatzResearch.WordTrace tailWord_1530867 prefixEnd_1530867 524047059404378139681451 := by
  unfold tailWord_1530867
  simp only [CollatzResearch.WordTrace]
  refine ⟨55835306544937785113510855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37223537696625190075673903 55835306544937785113510855)
  ·
    refine ⟨83752959817406677670266283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55835306544937785113510855 83752959817406677670266283)
    ·
      refine ⟨125629439726110016505399425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83752959817406677670266283 125629439726110016505399425)
      ·
        refine ⟨94222079794582512379049569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125629439726110016505399425 94222079794582512379049569)
        ·
          refine ⟨70666559845936884284287177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94222079794582512379049569 70666559845936884284287177)
          ·
            refine ⟨52999919884452663213215383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70666559845936884284287177 52999919884452663213215383)
            ·
              refine ⟨79499879826678994819823075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52999919884452663213215383 79499879826678994819823075)
              ·
                refine ⟨119249819740018492229734613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79499879826678994819823075 119249819740018492229734613)
                ·
                  refine ⟨2794917650156683411634405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 119249819740018492229734613 2794917650156683411634405)
                  ·
                    refine ⟨524047059404378139681451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794917650156683411634405 524047059404378139681451)
                    ·
                      rfl

theorem cell22_1530867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 7, 4].length) (baseStart_1530867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530867 prefixEnd_1530867 := by exact prefixLift 1530867
  have htrace : WordTrace (prefixWord ++ tailWord_1530867) baseStart_1530867 baseEnd_1530867 := by
    simpa [prefixWord, tailWord_1530867, baseEnd_1530867] using wordTrace_append hprefix tailTrace_1530867
  have hstable : (prefixWord ++ tailWord_1530867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530867).length < 2 ^ (prefixWord ++ tailWord_1530867).sum := by decide
  have hdescent : baseEnd_1530867 < baseStart_1530867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530897 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1530897 : Nat := 118140960795 + 1530897 * 2 ^ 59
def prefixEnd_1530897 : Nat := 4983230072969 + 3 ^ 40 * 1530897 * 2
def baseEnd_1530897 : Nat := 524057329017468061431359

theorem tailTrace_1530897 : CollatzResearch.WordTrace tailWord_1530897 prefixEnd_1530897 524057329017468061431359 := by
  unfold tailWord_1530897
  simp only [CollatzResearch.WordTrace]
  refine ⟨55836400734829100237102945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37224267156552733491401963 55836400734829100237102945)
  ·
    refine ⟨41877300551121825177827209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55836400734829100237102945 41877300551121825177827209)
    ·
      refine ⟨31407975413341368883370407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41877300551121825177827209 31407975413341368883370407)
      ·
        refine ⟨47111963120012053325055611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31407975413341368883370407 47111963120012053325055611)
        ·
          refine ⟨70667944680018079987583417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47111963120012053325055611 70667944680018079987583417)
          ·
            refine ⟨53000958510013559990687563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70667944680018079987583417 53000958510013559990687563)
            ·
              refine ⟨79501437765020339986031345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53000958510013559990687563 79501437765020339986031345)
              ·
                refine ⟨59626078323765254989523509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79501437765020339986031345 59626078323765254989523509)
                ·
                  refine ⟨5589944842852992655267829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59626078323765254989523509 5589944842852992655267829)
                  ·
                    refine ⟨524057329017468061431359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5589944842852992655267829 524057329017468061431359)
                    ·
                      rfl

theorem cell22_1530897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1530897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530897 prefixEnd_1530897 := by exact prefixLift 1530897
  have htrace : WordTrace (prefixWord ++ tailWord_1530897) baseStart_1530897 baseEnd_1530897 := by
    simpa [prefixWord, tailWord_1530897, baseEnd_1530897] using wordTrace_append hprefix tailTrace_1530897
  have hstable : (prefixWord ++ tailWord_1530897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530897).length < 2 ^ (prefixWord ++ tailWord_1530897).sum := by decide
  have hdescent : baseEnd_1530897 < baseStart_1530897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530901 : List Nat := [1, 3, 2, 1, 4, 1, 3, 2, 1, 4]
def baseStart_1530901 : Nat := 118140960795 + 1530901 * 2 ^ 59
def prefixEnd_1530901 : Nat := 4983230072969 + 3 ^ 40 * 1530901 * 2
def baseEnd_1530901 : Nat := 524058698299213384331347

theorem tailTrace_1530901 : CollatzResearch.WordTrace tailWord_1530901 prefixEnd_1530901 524058698299213384331347 := by
  unfold tailWord_1530901
  simp only [CollatzResearch.WordTrace]
  refine ⟨55836546626814608920248557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37224364417876405946832371 55836546626814608920248557)
  ·
    refine ⟨20938704985055478345093209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55836546626814608920248557 20938704985055478345093209)
    ·
      refine ⟨15704028738791608758819907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20938704985055478345093209 15704028738791608758819907)
      ·
        refine ⟨23556043108187413138229861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15704028738791608758819907 23556043108187413138229861)
        ·
          refine ⟨4416758082785139963418099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23556043108187413138229861 4416758082785139963418099)
          ·
            refine ⟨6625137124177709945127149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4416758082785139963418099 6625137124177709945127149)
            ·
              refine ⟨2484426421566641229422681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6625137124177709945127149 2484426421566641229422681)
              ·
                refine ⟨1863319816174980922067011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2484426421566641229422681 1863319816174980922067011)
                ·
                  refine ⟨2794979724262471383100517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863319816174980922067011 2794979724262471383100517)
                  ·
                    refine ⟨524058698299213384331347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2794979724262471383100517 524058698299213384331347)
                    ·
                      rfl

theorem cell22_1530901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_1530901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530901 prefixEnd_1530901 := by exact prefixLift 1530901
  have htrace : WordTrace (prefixWord ++ tailWord_1530901) baseStart_1530901 baseEnd_1530901 := by
    simpa [prefixWord, tailWord_1530901, baseEnd_1530901] using wordTrace_append hprefix tailTrace_1530901
  have hstable : (prefixWord ++ tailWord_1530901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530901).length < 2 ^ (prefixWord ++ tailWord_1530901).sum := by decide
  have hdescent : baseEnd_1530901 < baseStart_1530901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530914 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1530914 : Nat := 118140960795 + 1530914 * 2 ^ 59
def prefixEnd_1530914 : Nat := 4983230072969 + 3 ^ 40 * 1530914 * 2
def baseEnd_1530914 : Nat := 524063148464885683756307

theorem tailTrace_1530914 : CollatzResearch.WordTrace tailWord_1530914 prefixEnd_1530914 524063148464885683756307 := by
  unfold tailWord_1530914
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959255193941878035117949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37224680517178341426981197 13959255193941878035117949)
  ·
    refine ⟨5234720697728204263169231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13959255193941878035117949 5234720697728204263169231)
    ·
      refine ⟨7852081046592306394753847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234720697728204263169231 7852081046592306394753847)
      ·
        refine ⟨11778121569888459592130771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7852081046592306394753847 11778121569888459592130771)
        ·
          refine ⟨17667182354832689388196157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778121569888459592130771 17667182354832689388196157)
          ·
            refine ⟨6625193383062258520573559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17667182354832689388196157 6625193383062258520573559)
            ·
              refine ⟨9937790074593387780860339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6625193383062258520573559 9937790074593387780860339)
              ·
                refine ⟨14906685111890081671290509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9937790074593387780860339 14906685111890081671290509)
                ·
                  refine ⟨5590006916958780626733941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14906685111890081671290509 5590006916958780626733941)
                  ·
                    refine ⟨524063148464885683756307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5590006916958780626733941 524063148464885683756307)
                    ·
                      rfl

theorem cell22_1530914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1530914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530914 prefixEnd_1530914 := by exact prefixLift 1530914
  have htrace : WordTrace (prefixWord ++ tailWord_1530914) baseStart_1530914 baseEnd_1530914 := by
    simpa [prefixWord, tailWord_1530914, baseEnd_1530914] using wordTrace_append hprefix tailTrace_1530914
  have hstable : (prefixWord ++ tailWord_1530914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530914).length < 2 ^ (prefixWord ++ tailWord_1530914).sum := by decide
  have hdescent : baseEnd_1530914 < baseStart_1530914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1530929 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 2, 4]
def baseStart_1530929 : Nat := 118140960795 + 1530929 * 2 ^ 59
def prefixEnd_1530929 : Nat := 4983230072969 + 3 ^ 40 * 1530929 * 2
def baseEnd_1530929 : Nat := 524068283271430644631261

theorem tailTrace_1530929 : CollatzResearch.WordTrace tailWord_1530929 prefixEnd_1530929 524068283271430644631261 := by
  unfold tailWord_1530929
  simp only [CollatzResearch.WordTrace]
  refine ⟨55837567870713169702267841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37225045247142113134845227 55837567870713169702267841)
  ·
    refine ⟨41878175903034877276700881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55837567870713169702267841 41878175903034877276700881)
    ·
      refine ⟨31408631927276157957525661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41878175903034877276700881 31408631927276157957525661)
      ·
        refine ⟨11778236972728559234072123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31408631927276157957525661 11778236972728559234072123)
        ·
          refine ⟨17667355459092838851108185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11778236972728559234072123 17667355459092838851108185)
          ·
            refine ⟨13250516594319629138331139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17667355459092838851108185 13250516594319629138331139)
            ·
              refine ⟨19875774891479443707496709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13250516594319629138331139 19875774891479443707496709)
              ·
                refine ⟨3726707792152395695155633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19875774891479443707496709 3726707792152395695155633)
                ·
                  refine ⟨2795030844114296771366725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3726707792152395695155633 2795030844114296771366725)
                  ·
                    refine ⟨524068283271430644631261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2795030844114296771366725 524068283271430644631261)
                    ·
                      rfl

theorem cell22_1530929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_1530929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1530929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1530929 prefixEnd_1530929 := by exact prefixLift 1530929
  have htrace : WordTrace (prefixWord ++ tailWord_1530929) baseStart_1530929 baseEnd_1530929 := by
    simpa [prefixWord, tailWord_1530929, baseEnd_1530929] using wordTrace_append hprefix tailTrace_1530929
  have hstable : (prefixWord ++ tailWord_1530929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1530929).length < 2 ^ (prefixWord ++ tailWord_1530929).sum := by decide
  have hdescent : baseEnd_1530929 < baseStart_1530929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1530929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531004 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1531004 : Nat := 118140960795 + 1531004 * 2 ^ 59
def prefixEnd_1531004 : Nat := 4983230072969 + 3 ^ 40 * 1531004 * 2
def baseEnd_1531004 : Nat := 524093957304155449006031

theorem tailTrace_1531004 : CollatzResearch.WordTrace tailWord_1531004 prefixEnd_1531004 524093957304155449006031 := by
  unfold tailWord_1531004
  simp only [CollatzResearch.WordTrace]
  refine ⟨27920151672720728755624033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37226868896960971674165377 27920151672720728755624033)
  ·
    refine ⟨20940113754540546566718025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27920151672720728755624033 20940113754540546566718025)
    ·
      refine ⟨15705085315905409925038519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20940113754540546566718025 15705085315905409925038519)
      ·
        refine ⟨23557627973858114887557779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15705085315905409925038519 23557627973858114887557779)
        ·
          refine ⟨35336441960787172331336669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23557627973858114887557779 35336441960787172331336669)
          ·
            refine ⟨13251165735295189624251251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35336441960787172331336669 13251165735295189624251251)
            ·
              refine ⟨19876748602942784436376877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13251165735295189624251251 19876748602942784436376877)
              ·
                refine ⟨7453780726103544163641329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19876748602942784436376877 7453780726103544163641329)
                ·
                  refine ⟨5590335544577658122730997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7453780726103544163641329 5590335544577658122730997)
                  ·
                    refine ⟨524093957304155449006031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5590335544577658122730997 524093957304155449006031)
                    ·
                      rfl

theorem cell22_1531004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1531004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531004 prefixEnd_1531004 := by exact prefixLift 1531004
  have htrace : WordTrace (prefixWord ++ tailWord_1531004) baseStart_1531004 baseEnd_1531004 := by
    simpa [prefixWord, tailWord_1531004, baseEnd_1531004] using wordTrace_append hprefix tailTrace_1531004
  have hstable : (prefixWord ++ tailWord_1531004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531004).length < 2 ^ (prefixWord ++ tailWord_1531004).sum := by decide
  have hdescent : baseEnd_1531004 < baseStart_1531004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531019 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 3, 4]
def baseStart_1531019 : Nat := 118140960795 + 1531019 * 2 ^ 59
def prefixEnd_1531019 : Nat := 4983230072969 + 3 ^ 40 * 1531019 * 2
def baseEnd_1531019 : Nat := 524099092110700409880985

theorem tailTrace_1531019 : CollatzResearch.WordTrace tailWord_1531019 prefixEnd_1531019 524099092110700409880985 := by
  unfold tailWord_1531019
  simp only [CollatzResearch.WordTrace]
  refine ⟨55840850440387115073044111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37227233626924743382029407 55840850440387115073044111)
  ·
    refine ⟨83761275660580672609566167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55840850440387115073044111 83761275660580672609566167)
    ·
      refine ⟨125641913490871008914349251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83761275660580672609566167 125641913490871008914349251)
      ·
        refine ⟨188462870236306513371523877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125641913490871008914349251 188462870236306513371523877)
        ·
          refine ⟨35336788169307471257160727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188462870236306513371523877 35336788169307471257160727)
          ·
            refine ⟨53005182253961206885741091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35336788169307471257160727 53005182253961206885741091)
            ·
              refine ⟨79507773380941810328611637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53005182253961206885741091 79507773380941810328611637)
              ·
                refine ⟨7453853754463294718307341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79507773380941810328611637 7453853754463294718307341)
                ·
                  refine ⟨2795195157923735519365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7453853754463294718307341 2795195157923735519365253)
                  ·
                    refine ⟨524099092110700409880985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2795195157923735519365253 524099092110700409880985)
                    ·
                      rfl

theorem cell22_1531019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 3, 4].length) (baseStart_1531019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531019 prefixEnd_1531019 := by exact prefixLift 1531019
  have htrace : WordTrace (prefixWord ++ tailWord_1531019) baseStart_1531019 baseEnd_1531019 := by
    simpa [prefixWord, tailWord_1531019, baseEnd_1531019] using wordTrace_append hprefix tailTrace_1531019
  have hstable : (prefixWord ++ tailWord_1531019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531019).length < 2 ^ (prefixWord ++ tailWord_1531019).sum := by decide
  have hdescent : baseEnd_1531019 < baseStart_1531019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531064 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 1, 6]
def baseStart_1531064 : Nat := 118140960795 + 1531064 * 2 ^ 59
def prefixEnd_1531064 : Nat := 4983230072969 + 3 ^ 40 * 1531064 * 2
def baseEnd_1531064 : Nat := 524114496530335292505847

theorem tailTrace_1531064 : CollatzResearch.WordTrace tailWord_1531064 prefixEnd_1531064 524114496530335292505847 := by
  unfold tailWord_1531064
  simp only [CollatzResearch.WordTrace]
  refine ⟨27921245862612043879216123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37228327816816058505621497 27921245862612043879216123)
  ·
    refine ⟨41881868793918065818824185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27921245862612043879216123 41881868793918065818824185)
    ·
      refine ⟨31411401595438549364118139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41881868793918065818824185 31411401595438549364118139)
      ·
        refine ⟨47117102393157824046177209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31411401595438549364118139 47117102393157824046177209)
        ·
          refine ⟨35337826794868368034632907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47117102393157824046177209 35337826794868368034632907)
          ·
            refine ⟨53006740192302552051949361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35337826794868368034632907 53006740192302552051949361)
            ·
              refine ⟨39755055144226914038962021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53006740192302552051949361 39755055144226914038962021)
              ·
                refine ⟨7454072839542546382305379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39755055144226914038962021 7454072839542546382305379)
                ·
                  refine ⟨11181109259313819573458069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7454072839542546382305379 11181109259313819573458069)
                  ·
                    refine ⟨524114496530335292505847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11181109259313819573458069 524114496530335292505847)
                    ·
                      rfl

theorem cell22_1531064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_1531064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531064 prefixEnd_1531064 := by exact prefixLift 1531064
  have htrace : WordTrace (prefixWord ++ tailWord_1531064) baseStart_1531064 baseEnd_1531064 := by
    simpa [prefixWord, tailWord_1531064, baseEnd_1531064] using wordTrace_append hprefix tailTrace_1531064
  have hstable : (prefixWord ++ tailWord_1531064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531064).length < 2 ^ (prefixWord ++ tailWord_1531064).sum := by decide
  have hdescent : baseEnd_1531064 < baseStart_1531064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531070 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_1531070 : Nat := 118140960795 + 1531070 * 2 ^ 59
def prefixEnd_1531070 : Nat := 4983230072969 + 3 ^ 40 * 1531070 * 2
def baseEnd_1531070 : Nat := 524116550452953276855829

theorem tailTrace_1531070 : CollatzResearch.WordTrace tailWord_1531070 prefixEnd_1531070 524116550452953276855829 := by
  unfold tailWord_1531070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6980338820400293847893833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37228473708801567188767109 6980338820400293847893833)
  ·
    refine ⟨5235254115300220385920375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6980338820400293847893833 5235254115300220385920375)
    ·
      refine ⟨7852881172950330578880563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235254115300220385920375 7852881172950330578880563)
      ·
        refine ⟨11779321759425495868320845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7852881172950330578880563 11779321759425495868320845)
        ·
          refine ⟨4417245659784560950620317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11779321759425495868320845 4417245659784560950620317)
          ·
            refine ⟨1656467122419210356482619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4417245659784560950620317 1656467122419210356482619)
            ·
              refine ⟨2484700683628815534723929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656467122419210356482619 2484700683628815534723929)
              ·
                refine ⟨1863525512721611651042947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2484700683628815534723929 1863525512721611651042947)
                ·
                  refine ⟨2795288269082417476564421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863525512721611651042947 2795288269082417476564421)
                  ·
                    refine ⟨524116550452953276855829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2795288269082417476564421 524116550452953276855829)
                    ·
                      rfl

theorem cell22_1531070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_1531070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531070 prefixEnd_1531070 := by exact prefixLift 1531070
  have htrace : WordTrace (prefixWord ++ tailWord_1531070) baseStart_1531070 baseEnd_1531070 := by
    simpa [prefixWord, tailWord_1531070, baseEnd_1531070] using wordTrace_append hprefix tailTrace_1531070
  have hstable : (prefixWord ++ tailWord_1531070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531070).length < 2 ^ (prefixWord ++ tailWord_1531070).sum := by decide
  have hdescent : baseEnd_1531070 < baseStart_1531070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531096 : List Nat := [2, 1, 2, 2, 6, 9]
def baseStart_1531096 : Nat := 118140960795 + 1531096 * 2 ^ 59
def prefixEnd_1531096 : Nat := 4983230072969 + 3 ^ 40 * 1531096 * 2
def baseEnd_1531096 : Nat := 6470684577583924391429

theorem tailTrace_1531096 : CollatzResearch.WordTrace tailWord_1531096 prefixEnd_1531096 6470684577583924391429 := by
  unfold tailWord_1531096
  simp only [CollatzResearch.WordTrace]
  refine ⟨27921829430554078611798571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37229105907405438149064761 27921829430554078611798571)
  ·
    refine ⟨41882744145831117917697857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27921829430554078611798571 41882744145831117917697857)
    ·
      refine ⟨31412058109373338438273393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41882744145831117917697857 31412058109373338438273393)
      ·
        refine ⟨23559043582030003828705045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31412058109373338438273393 23559043582030003828705045)
        ·
          refine ⟨1104330167907656429470549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23559043582030003828705045 1104330167907656429470549)
          ·
            refine ⟨6470684577583924391429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1104330167907656429470549 6470684577583924391429)
            ·
              rfl

theorem cell22_1531096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 9].length) (baseStart_1531096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531096 prefixEnd_1531096 := by exact prefixLift 1531096
  have htrace : WordTrace (prefixWord ++ tailWord_1531096) baseStart_1531096 baseEnd_1531096 := by
    simpa [prefixWord, tailWord_1531096, baseEnd_1531096] using wordTrace_append hprefix tailTrace_1531096
  have hstable : (prefixWord ++ tailWord_1531096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531096).length < 2 ^ (prefixWord ++ tailWord_1531096).sum := by decide
  have hdescent : baseEnd_1531096 < baseStart_1531096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531126 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_1531126 : Nat := 118140960795 + 1531126 * 2 ^ 59
def prefixEnd_1531126 : Nat := 4983230072969 + 3 ^ 40 * 1531126 * 2
def baseEnd_1531126 : Nat := 524135720397387797455657

theorem tailTrace_1531126 : CollatzResearch.WordTrace tailWord_1531126 prefixEnd_1531126 524135720397387797455657 := by
  unfold tailWord_1531126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3490297065687467021699327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37229835367332981564792821 3490297065687467021699327)
  ·
    refine ⟨5235445598531200532548991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3490297065687467021699327 5235445598531200532548991)
    ·
      refine ⟨7853168397796800798823487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5235445598531200532548991 7853168397796800798823487)
      ·
        refine ⟨11779752596695201198235231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7853168397796800798823487 11779752596695201198235231)
        ·
          refine ⟨17669628895042801797352847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11779752596695201198235231 17669628895042801797352847)
          ·
            refine ⟨26504443342564202696029271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17669628895042801797352847 26504443342564202696029271)
            ·
              refine ⟨39756665013846304044043907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26504443342564202696029271 39756665013846304044043907)
              ·
                refine ⟨59634997520769456066065861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39756665013846304044043907 59634997520769456066065861)
                ·
                  refine ⟨11181562035144273012387349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59634997520769456066065861 11181562035144273012387349)
                  ·
                    refine ⟨524135720397387797455657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11181562035144273012387349 524135720397387797455657)
                    ·
                      rfl

theorem cell22_1531126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_1531126 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531126 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531126 prefixEnd_1531126 := by exact prefixLift 1531126
  have htrace : WordTrace (prefixWord ++ tailWord_1531126) baseStart_1531126 baseEnd_1531126 := by
    simpa [prefixWord, tailWord_1531126, baseEnd_1531126] using wordTrace_append hprefix tailTrace_1531126
  have hstable : (prefixWord ++ tailWord_1531126).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531126).length < 2 ^ (prefixWord ++ tailWord_1531126).sum := by decide
  have hdescent : baseEnd_1531126 < baseStart_1531126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531145 : List Nat := [1, 2, 1, 1, 3, 3, 4, 3, 1, 3]
def baseStart_1531145 : Nat := 118140960795 + 1531145 * 2 ^ 59
def prefixEnd_1531145 : Nat := 4983230072969 + 3 ^ 40 * 1531145 * 2
def baseEnd_1531145 : Nat := 524142224485678081230599

theorem tailTrace_1531145 : CollatzResearch.WordTrace tailWord_1531145 prefixEnd_1531145 524142224485678081230599 := by
  unfold tailWord_1531145
  simp only [CollatzResearch.WordTrace]
  refine ⟨55845446037930638592130889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37230297358620425728087259 55845446037930638592130889)
  ·
    refine ⟨41884084528447978944098167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55845446037930638592130889 41884084528447978944098167)
    ·
      refine ⟨62826126792671968416147251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41884084528447978944098167 62826126792671968416147251)
      ·
        refine ⟨94239190189007952624220877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62826126792671968416147251 94239190189007952624220877)
        ·
          refine ⟨35339696320877982234082829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94239190189007952624220877 35339696320877982234082829)
          ·
            refine ⟨13252386120329243337781061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35339696320877982234082829 13252386120329243337781061)
            ·
              refine ⟨2484822397561733125833949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13252386120329243337781061 2484822397561733125833949)
              ·
                refine ⟨931808399085649922187731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2484822397561733125833949 931808399085649922187731)
                ·
                  refine ⟨1397712598628474883281597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931808399085649922187731 1397712598628474883281597)
                  ·
                    refine ⟨524142224485678081230599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397712598628474883281597 524142224485678081230599)
                    ·
                      rfl

theorem cell22_1531145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 1, 3].length) (baseStart_1531145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531145 prefixEnd_1531145 := by exact prefixLift 1531145
  have htrace : WordTrace (prefixWord ++ tailWord_1531145) baseStart_1531145 baseEnd_1531145 := by
    simpa [prefixWord, tailWord_1531145, baseEnd_1531145] using wordTrace_append hprefix tailTrace_1531145
  have hstable : (prefixWord ++ tailWord_1531145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531145).length < 2 ^ (prefixWord ++ tailWord_1531145).sum := by decide
  have hdescent : baseEnd_1531145 < baseStart_1531145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531235 : List Nat := [1, 1, 1, 5, 2, 3, 1, 3, 2, 3]
def baseStart_1531235 : Nat := 118140960795 + 1531235 * 2 ^ 59
def prefixEnd_1531235 : Nat := 4983230072969 + 3 ^ 40 * 1531235 * 2
def baseEnd_1531235 : Nat := 524173033324947846480323

theorem tailTrace_1531235 : CollatzResearch.WordTrace tailWord_1531235 prefixEnd_1531235 524173033324947846480323 := by
  unfold tailWord_1531235
  simp only [CollatzResearch.WordTrace]
  refine ⟨55848728607604583962907159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37232485738403055975271439 55848728607604583962907159)
  ·
    refine ⟨83773092911406875944360739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55848728607604583962907159 83773092911406875944360739)
    ·
      refine ⟨125659639367110313916541109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83773092911406875944360739 125659639367110313916541109)
      ·
        refine ⟨11780591190666591929675729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125659639367110313916541109 11780591190666591929675729)
        ·
          refine ⟨8835443392999943947256797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11780591190666591929675729 8835443392999943947256797)
          ·
            refine ⟨3313291272374978980221299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8835443392999943947256797 3313291272374978980221299)
            ·
              refine ⟨4969936908562468470331949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313291272374978980221299 4969936908562468470331949)
              ·
                refine ⟨1863726340710925676374481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4969936908562468470331949 1863726340710925676374481)
                ·
                  refine ⟨1397794755533194257280861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1863726340710925676374481 1397794755533194257280861)
                  ·
                    refine ⟨524173033324947846480323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397794755533194257280861 524173033324947846480323)
                    ·
                      rfl

theorem cell22_1531235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 2, 3].length) (baseStart_1531235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531235 prefixEnd_1531235 := by exact prefixLift 1531235
  have htrace : WordTrace (prefixWord ++ tailWord_1531235) baseStart_1531235 baseEnd_1531235 := by
    simpa [prefixWord, tailWord_1531235, baseEnd_1531235] using wordTrace_append hprefix tailTrace_1531235
  have hstable : (prefixWord ++ tailWord_1531235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531235).length < 2 ^ (prefixWord ++ tailWord_1531235).sum := by decide
  have hdescent : baseEnd_1531235 < baseStart_1531235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531282 : List Nat := [3, 2, 3, 3, 1, 2, 1, 7]
def baseStart_1531282 : Nat := 118140960795 + 1531282 * 2 ^ 59
def prefixEnd_1531282 : Nat := 4983230072969 + 3 ^ 40 * 1531282 * 2
def baseEnd_1531282 : Nat := 58243235820606154506131

theorem tailTrace_1531282 : CollatzResearch.WordTrace tailWord_1531282 prefixEnd_1531282 58243235820606154506131 := by
  unfold tailWord_1531282
  simp only [CollatzResearch.WordTrace]
  refine ⟨13962610709608577747467025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37233628558956207326578733 13962610709608577747467025)
  ·
    refine ⟨10471958032206433310600269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13962610709608577747467025 10471958032206433310600269)
    ·
      refine ⟨3926984262077412491475101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10471958032206433310600269 3926984262077412491475101)
      ·
        refine ⟨1472619098279029684303163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3926984262077412491475101 1472619098279029684303163)
        ·
          refine ⟨2208928647418544526454745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1472619098279029684303163 2208928647418544526454745)
          ·
            refine ⟨1656696485563908394841059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208928647418544526454745 1656696485563908394841059)
            ·
              refine ⟨2485044728345862592261589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656696485563908394841059 2485044728345862592261589)
              ·
                refine ⟨58243235820606154506131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2485044728345862592261589 58243235820606154506131)
                ·
                  rfl

theorem cell22_1531282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_1531282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531282 prefixEnd_1531282 := by exact prefixLift 1531282
  have htrace : WordTrace (prefixWord ++ tailWord_1531282) baseStart_1531282 baseEnd_1531282 := by
    simpa [prefixWord, tailWord_1531282, baseEnd_1531282] using wordTrace_append hprefix tailTrace_1531282
  have hstable : (prefixWord ++ tailWord_1531282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531282).length < 2 ^ (prefixWord ++ tailWord_1531282).sum := by decide
  have hdescent : baseEnd_1531282 < baseStart_1531282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531291 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 8, 5]
def baseStart_1531291 : Nat := 118140960795 + 1531291 * 2 ^ 59
def prefixEnd_1531291 : Nat := 4983230072969 + 3 ^ 40 * 1531291 * 2
def baseEnd_1531291 : Nat := 524192203269382367080151

theorem tailTrace_1531291 : CollatzResearch.WordTrace tailWord_1531291 prefixEnd_1531291 524192203269382367080151 := by
  unfold tailWord_1531291
  simp only [CollatzResearch.WordTrace]
  refine ⟨55850771095401705526945727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37233847396934470351297151 55850771095401705526945727)
  ·
    refine ⟨83776156643102558290418591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55850771095401705526945727 83776156643102558290418591)
    ·
      refine ⟨125664234964653837435627887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83776156643102558290418591 125664234964653837435627887)
      ·
        refine ⟨188496352446980756153441831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125664234964653837435627887 188496352446980756153441831)
        ·
          refine ⟨282744528670471134230162747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188496352446980756153441831 282744528670471134230162747)
          ·
            refine ⟨424116793005706701345244121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282744528670471134230162747 424116793005706701345244121)
            ·
              refine ⟨318087594754280026008933091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424116793005706701345244121 318087594754280026008933091)
              ·
                refine ⟨477131392131420039013399637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318087594754280026008933091 477131392131420039013399637)
                ·
                  refine ⟨5591383501540078582188277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 477131392131420039013399637 5591383501540078582188277)
                  ·
                    refine ⟨524192203269382367080151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5591383501540078582188277 524192203269382367080151)
                    ·
                      rfl

theorem cell22_1531291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 5].length) (baseStart_1531291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531291 prefixEnd_1531291 := by exact prefixLift 1531291
  have htrace : WordTrace (prefixWord ++ tailWord_1531291) baseStart_1531291 baseEnd_1531291 := by
    simpa [prefixWord, tailWord_1531291, baseEnd_1531291] using wordTrace_append hprefix tailTrace_1531291
  have hstable : (prefixWord ++ tailWord_1531291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531291).length < 2 ^ (prefixWord ++ tailWord_1531291).sum := by decide
  have hdescent : baseEnd_1531291 < baseStart_1531291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531338 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 6]
def baseStart_1531338 : Nat := 118140960795 + 1531338 * 2 ^ 59
def prefixEnd_1531338 : Nat := 4983230072969 + 3 ^ 40 * 1531338 * 2
def baseEnd_1531338 : Nat := 174736097443296637051669

theorem tailTrace_1531338 : CollatzResearch.WordTrace tailWord_1531338 prefixEnd_1531338 174736097443296637051669 := by
  unfold tailWord_1531338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963121331557858138476667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37234990217487621702604445 13963121331557858138476667)
  ·
    refine ⟨20944681997336787207715001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13963121331557858138476667 20944681997336787207715001)
    ·
      refine ⟨15708511498002590405786251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20944681997336787207715001 15708511498002590405786251)
      ·
        refine ⟨23562767247003885608679377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15708511498002590405786251 23562767247003885608679377)
        ·
          refine ⟨17672075435252914206509533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23562767247003885608679377 17672075435252914206509533)
          ·
            refine ⟨6627028288219842827441075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17672075435252914206509533 6627028288219842827441075)
            ·
              refine ⟨9940542432329764241161613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627028288219842827441075 9940542432329764241161613)
              ·
                refine ⟨3727703412123661590435605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9940542432329764241161613 3727703412123661590435605)
                ·
                  refine ⟨174736097443296637051669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3727703412123661590435605 174736097443296637051669)
                  ·
                    rfl

theorem cell22_1531338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_1531338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531338 prefixEnd_1531338 := by exact prefixLift 1531338
  have htrace : WordTrace (prefixWord ++ tailWord_1531338) baseStart_1531338 baseEnd_1531338 := by
    simpa [prefixWord, tailWord_1531338, baseEnd_1531338] using wordTrace_append hprefix tailTrace_1531338
  have hstable : (prefixWord ++ tailWord_1531338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531338).length < 2 ^ (prefixWord ++ tailWord_1531338).sum := by decide
  have hdescent : baseEnd_1531338 < baseStart_1531338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531357 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1531357 : Nat := 118140960795 + 1531357 * 2 ^ 59
def prefixEnd_1531357 : Nat := 4983230072969 + 3 ^ 40 * 1531357 * 2
def baseEnd_1531357 : Nat := 524214796418180194929949

theorem tailTrace_1531357 : CollatzResearch.WordTrace tailWord_1531357 prefixEnd_1531357 524214796418180194929949 := by
  unfold tailWord_1531357
  simp only [CollatzResearch.WordTrace]
  refine ⟨55853178313162598798848325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37235452208775065865898883 55853178313162598798848325)
  ·
    refine ⟨10472470933717987274784061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55853178313162598798848325 10472470933717987274784061)
    ·
      refine ⟨3927176600144245228044023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10472470933717987274784061 3927176600144245228044023)
      ·
        refine ⟨5890764900216367842066035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3927176600144245228044023 5890764900216367842066035)
        ·
          refine ⟨8836147350324551763099053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890764900216367842066035 8836147350324551763099053)
          ·
            refine ⟨3313555256371706911162145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8836147350324551763099053 3313555256371706911162145)
            ·
              refine ⟨2485166442278780183371609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3313555256371706911162145 2485166442278780183371609)
              ·
                refine ⟨1863874831709085137528707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2485166442278780183371609 1863874831709085137528707)
                ·
                  refine ⟨2795812247563627706293061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863874831709085137528707 2795812247563627706293061)
                  ·
                    refine ⟨524214796418180194929949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2795812247563627706293061 524214796418180194929949)
                    ·
                      rfl

theorem cell22_1531357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1531357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531357 prefixEnd_1531357 := by exact prefixLift 1531357
  have htrace : WordTrace (prefixWord ++ tailWord_1531357) baseStart_1531357 baseEnd_1531357 := by
    simpa [prefixWord, tailWord_1531357, baseEnd_1531357] using wordTrace_append hprefix tailTrace_1531357
  have hstable : (prefixWord ++ tailWord_1531357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531357).length < 2 ^ (prefixWord ++ tailWord_1531357).sum := by decide
  have hdescent : baseEnd_1531357 < baseStart_1531357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531368 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1531368 : Nat := 118140960795 + 1531368 * 2 ^ 59
def prefixEnd_1531368 : Nat := 4983230072969 + 3 ^ 40 * 1531368 * 2
def baseEnd_1531368 : Nat := 524218561942979832904915

theorem tailTrace_1531368 : CollatzResearch.WordTrace tailWord_1531368 prefixEnd_1531368 524218561942979832904915 := by
  unfold tailWord_1531368
  simp only [CollatzResearch.WordTrace]
  refine ⟨27926789758061373838749379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37235719677415165118332505 27926789758061373838749379)
  ·
    refine ⟨41890184637092060758124069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27926789758061373838749379 41890184637092060758124069)
    ·
      refine ⟨7854409619454761392148263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41890184637092060758124069 7854409619454761392148263)
      ·
        refine ⟨11781614429182142088222395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7854409619454761392148263 11781614429182142088222395)
        ·
          refine ⟨17672421643773213132333593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11781614429182142088222395 17672421643773213132333593)
          ·
            refine ⟨13254316232829909849250195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17672421643773213132333593 13254316232829909849250195)
            ·
              refine ⟨19881474349244864773875293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13254316232829909849250195 19881474349244864773875293)
              ·
                refine ⟨7455552880966824290203235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19881474349244864773875293 7455552880966824290203235)
                ·
                  refine ⟨11183329321450236435304853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7455552880966824290203235 11183329321450236435304853)
                  ·
                    refine ⟨524218561942979832904915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11183329321450236435304853 524218561942979832904915)
                    ·
                      rfl

theorem cell22_1531368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1531368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531368 prefixEnd_1531368 := by exact prefixLift 1531368
  have htrace : WordTrace (prefixWord ++ tailWord_1531368) baseStart_1531368 baseEnd_1531368 := by
    simpa [prefixWord, tailWord_1531368, baseEnd_1531368] using wordTrace_append hprefix tailTrace_1531368
  have hstable : (prefixWord ++ tailWord_1531368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531368).length < 2 ^ (prefixWord ++ tailWord_1531368).sum := by decide
  have hdescent : baseEnd_1531368 < baseStart_1531368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531445 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 5]
def baseStart_1531445 : Nat := 118140960795 + 1531445 * 2 ^ 59
def prefixEnd_1531445 : Nat := 4983230072969 + 3 ^ 40 * 1531445 * 2
def baseEnd_1531445 : Nat := 174748306872192432909893

theorem tailTrace_1531445 : CollatzResearch.WordTrace tailWord_1531445 prefixEnd_1531445 174748306872192432909893 := by
  unfold tailWord_1531445
  simp only [CollatzResearch.WordTrace]
  refine ⟨55856387936843789828051789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37237591957895859885367859 55856387936843789828051789)
  ·
    refine ⟨20946145476316421185519421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55856387936843789828051789 20946145476316421185519421)
    ·
      refine ⟨7854804553618657944569783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20946145476316421185519421 7854804553618657944569783)
      ·
        refine ⟨11782206830427986916854675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7854804553618657944569783 11782206830427986916854675)
        ·
          refine ⟨17673310245641980375282013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11782206830427986916854675 17673310245641980375282013)
          ·
            refine ⟨6627491342115742640730755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17673310245641980375282013 6627491342115742640730755)
            ·
              refine ⟨9941237013173613961096133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627491342115742640730755 9941237013173613961096133)
              ·
                refine ⟨1863981939970052617705525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9941237013173613961096133 1863981939970052617705525)
                ·
                  refine ⟨174748306872192432909893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1863981939970052617705525 174748306872192432909893)
                  ·
                    rfl

theorem cell22_1531445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_1531445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531445 prefixEnd_1531445 := by exact prefixLift 1531445
  have htrace : WordTrace (prefixWord ++ tailWord_1531445) baseStart_1531445 baseEnd_1531445 := by
    simpa [prefixWord, tailWord_1531445, baseEnd_1531445] using wordTrace_append hprefix tailTrace_1531445
  have hstable : (prefixWord ++ tailWord_1531445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531445).length < 2 ^ (prefixWord ++ tailWord_1531445).sum := by decide
  have hdescent : baseEnd_1531445 < baseStart_1531445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531449 : List Nat := [1, 2, 1, 5, 1, 3, 1, 4, 1, 3]
def baseStart_1531449 : Nat := 118140960795 + 1531449 * 2 ^ 59
def prefixEnd_1531449 : Nat := 4983230072969 + 3 ^ 40 * 1531449 * 2
def baseEnd_1531449 : Nat := 524246289898322621629667

theorem tailTrace_1531449 : CollatzResearch.WordTrace tailWord_1531449 prefixEnd_1531449 524246289898322621629667 := by
  unfold tailWord_1531449
  simp only [CollatzResearch.WordTrace]
  refine ⟨55856533828829298511197401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37237689219219532340798267 55856533828829298511197401)
  ·
    refine ⟨41892400371621973883398051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55856533828829298511197401 41892400371621973883398051)
    ·
      refine ⟨62838600557432960825097077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41892400371621973883398051 62838600557432960825097077)
      ·
        refine ⟨5891118802259340077352851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62838600557432960825097077 5891118802259340077352851)
        ·
          refine ⟨8836678203389010116029277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5891118802259340077352851 8836678203389010116029277)
          ·
            refine ⟨3313754326270878793510979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8836678203389010116029277 3313754326270878793510979)
            ·
              refine ⟨4970631489406318190266469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313754326270878793510979 4970631489406318190266469)
              ·
                refine ⟨931993404263684660674963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4970631489406318190266469 931993404263684660674963)
                ·
                  refine ⟨1397990106395526991012445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931993404263684660674963 1397990106395526991012445)
                  ·
                    refine ⟨524246289898322621629667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1397990106395526991012445 524246289898322621629667)
                    ·
                      rfl

theorem cell22_1531449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 4, 1, 3].length) (baseStart_1531449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531449 prefixEnd_1531449 := by exact prefixLift 1531449
  have htrace : WordTrace (prefixWord ++ tailWord_1531449) baseStart_1531449 baseEnd_1531449 := by
    simpa [prefixWord, tailWord_1531449, baseEnd_1531449] using wordTrace_append hprefix tailTrace_1531449
  have hstable : (prefixWord ++ tailWord_1531449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531449).length < 2 ^ (prefixWord ++ tailWord_1531449).sum := by decide
  have hdescent : baseEnd_1531449 < baseStart_1531449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531492 : List Nat := [2, 3, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_1531492 : Nat := 118140960795 + 1531492 * 2 ^ 59
def prefixEnd_1531492 : Nat := 4983230072969 + 3 ^ 40 * 1531492 * 2
def baseEnd_1531492 : Nat := 524261009677084842804535

theorem tailTrace_1531492 : CollatzResearch.WordTrace tailWord_1531492 prefixEnd_1531492 524261009677084842804535 := by
  unfold tailWord_1531492
  simp only [CollatzResearch.WordTrace]
  refine ⟨27929051083836758427506365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37238734778449011236675153 27929051083836758427506365)
  ·
    refine ⟨10473394156438784410314887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27929051083836758427506365 10473394156438784410314887)
    ·
      refine ⟨15710091234658176615472331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10473394156438784410314887 15710091234658176615472331)
      ·
        refine ⟨23565136851987264923208497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15710091234658176615472331 23565136851987264923208497)
        ·
          refine ⟨17673852638990448692406373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23565136851987264923208497 17673852638990448692406373)
          ·
            refine ⟨3313847369810709129826195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17673852638990448692406373 3313847369810709129826195)
            ·
              refine ⟨4970771054716063694739293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3313847369810709129826195 4970771054716063694739293)
              ·
                refine ⟨1864039145518523885527235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4970771054716063694739293 1864039145518523885527235)
                ·
                  refine ⟨2796058718277785828290853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864039145518523885527235 2796058718277785828290853)
                  ·
                    refine ⟨524261009677084842804535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796058718277785828290853 524261009677084842804535)
                    ·
                      rfl

theorem cell22_1531492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_1531492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531492 prefixEnd_1531492 := by exact prefixLift 1531492
  have htrace : WordTrace (prefixWord ++ tailWord_1531492) baseStart_1531492 baseEnd_1531492 := by
    simpa [prefixWord, tailWord_1531492, baseEnd_1531492] using wordTrace_append hprefix tailTrace_1531492
  have hstable : (prefixWord ++ tailWord_1531492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531492).length < 2 ^ (prefixWord ++ tailWord_1531492).sum := by decide
  have hdescent : baseEnd_1531492 < baseStart_1531492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531573 : List Nat := [1, 3, 3, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1531573 : Nat := 118140960795 + 1531573 * 2 ^ 59
def prefixEnd_1531573 : Nat := 4983230072969 + 3 ^ 40 * 1531573 * 2
def baseEnd_1531573 : Nat := 524288737632427631529287

theorem tailTrace_1531573 : CollatzResearch.WordTrace tailWord_1531573 prefixEnd_1531573 524288737632427631529287 := by
  unfold tailWord_1531573
  simp only [CollatzResearch.WordTrace]
  refine ⟨55861056480380067688711373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37240704320253378459140915 55861056480380067688711373)
  ·
    refine ⟨20947896180142525383266765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55861056480380067688711373 20947896180142525383266765)
    ·
      refine ⟨7855461067553447018725037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20947896180142525383266765 7855461067553447018725037)
      ·
        refine ⟨2945797900332542632021889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7855461067553447018725037 2945797900332542632021889)
        ·
          refine ⟨2209348425249406974016417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2945797900332542632021889 2209348425249406974016417)
          ·
            refine ⟨1657011318937055230512313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2209348425249406974016417 1657011318937055230512313)
            ·
              refine ⟨1242758489202791422884235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657011318937055230512313 1242758489202791422884235)
              ·
                refine ⟨1864137733804187134326353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242758489202791422884235 1864137733804187134326353)
                ·
                  refine ⟨1398103300353140350744765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864137733804187134326353 1398103300353140350744765)
                  ·
                    refine ⟨524288737632427631529287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398103300353140350744765 524288737632427631529287)
                    ·
                      rfl

theorem cell22_1531573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1531573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531573 prefixEnd_1531573 := by exact prefixLift 1531573
  have htrace : WordTrace (prefixWord ++ tailWord_1531573) baseStart_1531573 baseEnd_1531573 := by
    simpa [prefixWord, tailWord_1531573, baseEnd_1531573] using wordTrace_append hprefix tailTrace_1531573
  have hstable : (prefixWord ++ tailWord_1531573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531573).length < 2 ^ (prefixWord ++ tailWord_1531573).sum := by decide
  have hdescent : baseEnd_1531573 < baseStart_1531573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531625 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 6]
def baseStart_1531625 : Nat := 118140960795 + 1531625 * 2 ^ 59
def prefixEnd_1531625 : Nat := 4983230072969 + 3 ^ 40 * 1531625 * 2
def baseEnd_1531625 : Nat := 174768846098372276409709

theorem tailTrace_1531625 : CollatzResearch.WordTrace tailWord_1531625 prefixEnd_1531625 174768846098372276409709 := by
  unfold tailWord_1531625
  simp only [CollatzResearch.WordTrace]
  refine ⟨55862953076191680569604329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37241968717461120379736219 55862953076191680569604329)
  ·
    refine ⟨41897214807143760427203247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55862953076191680569604329 41897214807143760427203247)
    ·
      refine ⟨62845822210715640640804871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41897214807143760427203247 62845822210715640640804871)
      ·
        refine ⟨94268733316073460961207307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62845822210715640640804871 94268733316073460961207307)
        ·
          refine ⟨141403099974110191441810961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94268733316073460961207307 141403099974110191441810961)
          ·
            refine ⟨106052324980582643581358221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141403099974110191441810961 106052324980582643581358221)
            ·
              refine ⟨39769621867718491343009333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106052324980582643581358221 39769621867718491343009333)
              ·
                refine ⟨3728402050098608563407125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39769621867718491343009333 3728402050098608563407125)
                ·
                  refine ⟨174768846098372276409709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3728402050098608563407125 174768846098372276409709)
                  ·
                    rfl

theorem cell22_1531625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 6].length) (baseStart_1531625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531625 prefixEnd_1531625 := by exact prefixLift 1531625
  have htrace : WordTrace (prefixWord ++ tailWord_1531625) baseStart_1531625 baseEnd_1531625 := by
    simpa [prefixWord, tailWord_1531625, baseEnd_1531625] using wordTrace_append hprefix tailTrace_1531625
  have hstable : (prefixWord ++ tailWord_1531625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531625).length < 2 ^ (prefixWord ++ tailWord_1531625).sum := by decide
  have hdescent : baseEnd_1531625 < baseStart_1531625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531657 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 4, 3]
def baseStart_1531657 : Nat := 118140960795 + 1531657 * 2 ^ 59
def prefixEnd_1531657 : Nat := 4983230072969 + 3 ^ 40 * 1531657 * 2
def baseEnd_1531657 : Nat := 524317492549079412429029

theorem tailTrace_1531657 : CollatzResearch.WordTrace tailWord_1531657 prefixEnd_1531657 524317492549079412429029 := by
  unfold tailWord_1531657
  simp only [CollatzResearch.WordTrace]
  refine ⟨55864120212075750034769225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37242746808050500023179483 55864120212075750034769225)
  ·
    refine ⟨41898090159056812526076919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55864120212075750034769225 41898090159056812526076919)
    ·
      refine ⟨62847135238585218789115379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41898090159056812526076919 62847135238585218789115379)
      ·
        refine ⟨94270702857877828183673069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62847135238585218789115379 94270702857877828183673069)
        ·
          refine ⟨35351513571704185568877401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94270702857877828183673069 35351513571704185568877401)
          ·
            refine ⟨26513635178778139176658051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35351513571704185568877401 26513635178778139176658051)
            ·
              refine ⟨39770452768167208764987077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26513635178778139176658051 39770452768167208764987077)
              ·
                refine ⟨7456959894031351643435077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39770452768167208764987077 7456959894031351643435077)
                ·
                  refine ⟨1398179980130878433144077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7456959894031351643435077 1398179980130878433144077)
                  ·
                    refine ⟨524317492549079412429029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398179980130878433144077 524317492549079412429029)
                    ·
                      rfl

theorem cell22_1531657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 4, 3].length) (baseStart_1531657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531657 prefixEnd_1531657 := by exact prefixLift 1531657
  have htrace : WordTrace (prefixWord ++ tailWord_1531657) baseStart_1531657 baseEnd_1531657 := by
    simpa [prefixWord, tailWord_1531657, baseEnd_1531657] using wordTrace_append hprefix tailTrace_1531657
  have hstable : (prefixWord ++ tailWord_1531657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531657).length < 2 ^ (prefixWord ++ tailWord_1531657).sum := by decide
  have hdescent : baseEnd_1531657 < baseStart_1531657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531672 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_1531672 : Nat := 118140960795 + 1531672 * 2 ^ 59
def prefixEnd_1531672 : Nat := 4983230072969 + 3 ^ 40 * 1531672 * 2
def baseEnd_1531672 : Nat := 524322627355624373303983

theorem tailTrace_1531672 : CollatzResearch.WordTrace tailWord_1531672 prefixEnd_1531672 524322627355624373303983 := by
  unfold tailWord_1531672
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932333653510703798282635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37243111538014271731043513 27932333653510703798282635)
  ·
    refine ⟨41898500480266055697423953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27932333653510703798282635 41898500480266055697423953)
    ·
      refine ⟨31423875360199541773067965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41898500480266055697423953 31423875360199541773067965)
      ·
        refine ⟨11783953260074828164900487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31423875360199541773067965 11783953260074828164900487)
        ·
          refine ⟨17675929890112242247350731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11783953260074828164900487 17675929890112242247350731)
          ·
            refine ⟨26513894835168363371026097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17675929890112242247350731 26513894835168363371026097)
            ·
              refine ⟨19885421126376272528269573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26513894835168363371026097 19885421126376272528269573)
              ·
                refine ⟨3728516461195551099050545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19885421126376272528269573 3728516461195551099050545)
                ·
                  refine ⟨2796387345896663324287909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728516461195551099050545 2796387345896663324287909)
                  ·
                    refine ⟨524322627355624373303983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2796387345896663324287909 524322627355624373303983)
                    ·
                      rfl

theorem cell22_1531672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_1531672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531672 prefixEnd_1531672 := by exact prefixLift 1531672
  have htrace : WordTrace (prefixWord ++ tailWord_1531672) baseStart_1531672 baseEnd_1531672 := by
    simpa [prefixWord, tailWord_1531672, baseEnd_1531672] using wordTrace_append hprefix tailTrace_1531672
  have hstable : (prefixWord ++ tailWord_1531672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531672).length < 2 ^ (prefixWord ++ tailWord_1531672).sum := by decide
  have hdescent : baseEnd_1531672 < baseStart_1531672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531674 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_1531674 : Nat := 118140960795 + 1531674 * 2 ^ 59
def prefixEnd_1531674 : Nat := 4983230072969 + 3 ^ 40 * 1531674 * 2
def baseEnd_1531674 : Nat := 524323311996497034753977

theorem tailTrace_1531674 : CollatzResearch.WordTrace tailWord_1531674 prefixEnd_1531674 524323311996497034753977 := by
  unfold tailWord_1531674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13966185063253540484534519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37243160168676107958758717 13966185063253540484534519)
  ·
    refine ⟨20949277594880310726801779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13966185063253540484534519 20949277594880310726801779)
    ·
      refine ⟨31423916392320466090202669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20949277594880310726801779 31423916392320466090202669)
      ·
        refine ⟨11783968647120174783826001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31423916392320466090202669 11783968647120174783826001)
        ·
          refine ⟨8837976485340131087869501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11783968647120174783826001 8837976485340131087869501)
          ·
            refine ⟨3314241182002549157951063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8837976485340131087869501 3314241182002549157951063)
            ·
              refine ⟨4971361773003823736926595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314241182002549157951063 4971361773003823736926595)
              ·
                refine ⟨7457042659505735605389893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4971361773003823736926595 7457042659505735605389893)
                ·
                  refine ⟨1398195498657325426010605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7457042659505735605389893 1398195498657325426010605)
                  ·
                    refine ⟨524323311996497034753977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398195498657325426010605 524323311996497034753977)
                    ·
                      rfl

theorem cell22_1531674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_1531674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531674 prefixEnd_1531674 := by exact prefixLift 1531674
  have htrace : WordTrace (prefixWord ++ tailWord_1531674) baseStart_1531674 baseEnd_1531674 := by
    simpa [prefixWord, tailWord_1531674, baseEnd_1531674] using wordTrace_append hprefix tailTrace_1531674
  have hstable : (prefixWord ++ tailWord_1531674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531674).length < 2 ^ (prefixWord ++ tailWord_1531674).sum := by decide
  have hdescent : baseEnd_1531674 < baseStart_1531674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531704 : List Nat := [2, 1, 2, 1, 3, 5, 2, 6]
def baseStart_1531704 : Nat := 118140960795 + 1531704 * 2 ^ 59
def prefixEnd_1531704 : Nat := 4983230072969 + 3 ^ 40 * 1531704 * 2
def baseEnd_1531704 : Nat := 58259286845509661833765

theorem tailTrace_1531704 : CollatzResearch.WordTrace tailWord_1531704 prefixEnd_1531704 58259286845509661833765 := by
  unfold tailWord_1531704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27932917221452738530865083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37243889628603651374486777 27932917221452738530865083)
  ·
    refine ⟨41899375832179107796297625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27932917221452738530865083 41899375832179107796297625)
    ·
      refine ⟨31424531874134330847223219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41899375832179107796297625 31424531874134330847223219)
      ·
        refine ⟨47136797811201496270834829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31424531874134330847223219 47136797811201496270834829)
        ·
          refine ⟨17676299179200561101563061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47136797811201496270834829 17676299179200561101563061)
          ·
            refine ⟨1657153048050052603271537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17676299179200561101563061 1657153048050052603271537)
            ·
              refine ⟨1242864786037539452453653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657153048050052603271537 1242864786037539452453653)
              ·
                refine ⟨58259286845509661833765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1242864786037539452453653 58259286845509661833765)
                ·
                  rfl

theorem cell22_1531704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 6].length) (baseStart_1531704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531704 prefixEnd_1531704 := by exact prefixLift 1531704
  have htrace : WordTrace (prefixWord ++ tailWord_1531704) baseStart_1531704 baseEnd_1531704 := by
    simpa [prefixWord, tailWord_1531704, baseEnd_1531704] using wordTrace_append hprefix tailTrace_1531704
  have hstable : (prefixWord ++ tailWord_1531704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531704).length < 2 ^ (prefixWord ++ tailWord_1531704).sum := by decide
  have hdescent : baseEnd_1531704 < baseStart_1531704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531871 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 3, 3]
def baseStart_1531871 : Nat := 118140960795 + 1531871 * 2 ^ 59
def prefixEnd_1531871 : Nat := 4983230072969 + 3 ^ 40 * 1531871 * 2
def baseEnd_1531871 : Nat := 524390749122454187578373

theorem tailTrace_1531871 : CollatzResearch.WordTrace tailWord_1531871 prefixEnd_1531871 524390749122454187578373 := by
  unfold tailWord_1531871
  simp only [CollatzResearch.WordTrace]
  refine ⟨55871925433300464583059467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37247950288866976388706311 55871925433300464583059467)
  ·
    refine ⟨83807888149950696874589201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55871925433300464583059467 83807888149950696874589201)
    ·
      refine ⟨62855916112463022655941901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83807888149950696874589201 62855916112463022655941901)
      ·
        refine ⟨23570968542173633495978213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62855916112463022655941901 23570968542173633495978213)
        ·
          refine ⟨4419556601657556280495915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23570968542173633495978213 4419556601657556280495915)
          ·
            refine ⟨6629334902486334420743873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419556601657556280495915 6629334902486334420743873)
            ·
              refine ⟨4972001176864750815557905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6629334902486334420743873 4972001176864750815557905)
              ·
                refine ⟨3729000882648563111668429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4972001176864750815557905 3729000882648563111668429)
                ·
                  refine ⟨1398375330993211166875661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729000882648563111668429 1398375330993211166875661)
                  ·
                    refine ⟨524390749122454187578373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398375330993211166875661 524390749122454187578373)
                    ·
                      rfl

theorem cell22_1531871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_1531871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531871 prefixEnd_1531871 := by exact prefixLift 1531871
  have htrace : WordTrace (prefixWord ++ tailWord_1531871) baseStart_1531871 baseEnd_1531871 := by
    simpa [prefixWord, tailWord_1531871, baseEnd_1531871] using wordTrace_append hprefix tailTrace_1531871
  have hstable : (prefixWord ++ tailWord_1531871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531871).length < 2 ^ (prefixWord ++ tailWord_1531871).sum := by decide
  have hdescent : baseEnd_1531871 < baseStart_1531871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531888 : List Nat := [2, 1, 1, 1, 3, 2, 5, 3, 1, 3]
def baseStart_1531888 : Nat := 118140960795 + 1531888 * 2 ^ 59
def prefixEnd_1531888 : Nat := 4983230072969 + 3 ^ 40 * 1531888 * 2
def baseEnd_1531888 : Nat := 524396568569871809903321

theorem tailTrace_1531888 : CollatzResearch.WordTrace tailWord_1531888 prefixEnd_1531888 524396568569871809903321 := by
  unfold tailWord_1531888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27936272737119438243214159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37248363649492584324285545 27936272737119438243214159)
  ·
    refine ⟨41904409105679157364821239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27936272737119438243214159 41904409105679157364821239)
    ·
      refine ⟨62856613658518736047231859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41904409105679157364821239 62856613658518736047231859)
      ·
        refine ⟨94284920487778104070847789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62856613658518736047231859 94284920487778104070847789)
        ·
          refine ⟨35356845182916789026567921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94284920487778104070847789 35356845182916789026567921)
          ·
            refine ⟨26517633887187591769925941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35356845182916789026567921 26517633887187591769925941)
            ·
              refine ⟨2486028176923836728430557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26517633887187591769925941 2486028176923836728430557)
              ·
                refine ⟨932260566346438773161459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2486028176923836728430557 932260566346438773161459)
                ·
                  refine ⟨1398390849519658159742189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932260566346438773161459 1398390849519658159742189)
                  ·
                    refine ⟨524396568569871809903321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398390849519658159742189 524396568569871809903321)
                    ·
                      rfl

theorem cell22_1531888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_1531888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531888 prefixEnd_1531888 := by exact prefixLift 1531888
  have htrace : WordTrace (prefixWord ++ tailWord_1531888) baseStart_1531888 baseEnd_1531888 := by
    simpa [prefixWord, tailWord_1531888, baseEnd_1531888] using wordTrace_append hprefix tailTrace_1531888
  have hstable : (prefixWord ++ tailWord_1531888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531888).length < 2 ^ (prefixWord ++ tailWord_1531888).sum := by decide
  have hdescent : baseEnd_1531888 < baseStart_1531888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531905 : List Nat := [1, 2, 4, 1, 2, 1, 5, 2, 1, 3]
def baseStart_1531905 : Nat := 118140960795 + 1531905 * 2 ^ 59
def prefixEnd_1531905 : Nat := 4983230072969 + 3 ^ 40 * 1531905 * 2
def baseEnd_1531905 : Nat := 524402388017289432228269

theorem tailTrace_1531905 : CollatzResearch.WordTrace tailWord_1531905 prefixEnd_1531905 524402388017289432228269 := by
  unfold tailWord_1531905
  simp only [CollatzResearch.WordTrace]
  refine ⟨55873165515177288389797169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37248777010118192259864779 55873165515177288389797169)
  ·
    refine ⟨41904874136382966292347877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55873165515177288389797169 41904874136382966292347877)
    ·
      refine ⟨7857163900571806179815227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41904874136382966292347877 7857163900571806179815227)
      ·
        refine ⟨11785745850857709269722841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857163900571806179815227 11785745850857709269722841)
        ·
          refine ⟨8839309388143281952292131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11785745850857709269722841 8839309388143281952292131)
          ·
            refine ⟨13258964082214922928438197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8839309388143281952292131 13258964082214922928438197)
            ·
              refine ⟨1243027882707649024541081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13258964082214922928438197 1243027882707649024541081)
              ·
                refine ⟨932270912030736768405811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243027882707649024541081 932270912030736768405811)
                ·
                  refine ⟨1398406368046105152608717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932270912030736768405811 1398406368046105152608717)
                  ·
                    refine ⟨524402388017289432228269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398406368046105152608717 524402388017289432228269)
                    ·
                      rfl

theorem cell22_1531905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_1531905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531905 prefixEnd_1531905 := by exact prefixLift 1531905
  have htrace : WordTrace (prefixWord ++ tailWord_1531905) baseStart_1531905 baseEnd_1531905 := by
    simpa [prefixWord, tailWord_1531905, baseEnd_1531905] using wordTrace_append hprefix tailTrace_1531905
  have hstable : (prefixWord ++ tailWord_1531905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531905).length < 2 ^ (prefixWord ++ tailWord_1531905).sum := by decide
  have hdescent : baseEnd_1531905 < baseStart_1531905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1531956 : List Nat := [2, 5, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_1531956 : Nat := 118140960795 + 1531956 * 2 ^ 59
def prefixEnd_1531956 : Nat := 4983230072969 + 3 ^ 40 * 1531956 * 2
def baseEnd_1531956 : Nat := 524419846359542299203113

theorem tailTrace_1531956 : CollatzResearch.WordTrace tailWord_1531956 prefixEnd_1531956 524419846359542299203113 := by
  unfold tailWord_1531956
  simp only [CollatzResearch.WordTrace]
  refine ⟨27937512818996262049951861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37250017091995016066602481 27937512818996262049951861)
  ·
    refine ⟨2619141826780899567182987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27937512818996262049951861 2619141826780899567182987)
    ·
      refine ⟨3928712740171349350774481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619141826780899567182987 3928712740171349350774481)
      ·
        refine ⟨2946534555128512013080861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3928712740171349350774481 2946534555128512013080861)
        ·
          refine ⟨1104950458173192004905323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2946534555128512013080861 1104950458173192004905323)
          ·
            refine ⟨1657425687259788007357985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104950458173192004905323 1657425687259788007357985)
            ·
              refine ⟨1243069265444841005518489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1657425687259788007357985 1243069265444841005518489)
              ·
                refine ⟨932301949083630754138867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1243069265444841005518489 932301949083630754138867)
                ·
                  refine ⟨1398452923625446131208301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932301949083630754138867 1398452923625446131208301)
                  ·
                    refine ⟨524419846359542299203113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398452923625446131208301 524419846359542299203113)
                    ·
                      rfl

theorem cell22_1531956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_1531956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1531956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1531956 prefixEnd_1531956 := by exact prefixLift 1531956
  have htrace : WordTrace (prefixWord ++ tailWord_1531956) baseStart_1531956 baseEnd_1531956 := by
    simpa [prefixWord, tailWord_1531956, baseEnd_1531956] using wordTrace_append hprefix tailTrace_1531956
  have hstable : (prefixWord ++ tailWord_1531956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1531956).length < 2 ^ (prefixWord ++ tailWord_1531956).sum := by decide
  have hdescent : baseEnd_1531956 < baseStart_1531956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1531956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532023 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 3, 3]
def baseStart_1532023 : Nat := 118140960795 + 1532023 * 2 ^ 59
def prefixEnd_1532023 : Nat := 4983230072969 + 3 ^ 40 * 1532023 * 2
def baseEnd_1532023 : Nat := 524442781828776457777907

theorem tailTrace_1532023 : CollatzResearch.WordTrace tailWord_1532023 prefixEnd_1532023 524442781828776457777907 := by
  unfold tailWord_1532023
  simp only [CollatzResearch.WordTrace]
  refine ⟨55877469328749794542592723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37251646219166529695061815 55877469328749794542592723)
  ·
    refine ⟨83816203993124691813889085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55877469328749794542592723 83816203993124691813889085)
    ·
      refine ⟨31431076497421759430208407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83816203993124691813889085 31431076497421759430208407)
      ·
        refine ⟨47146614746132639145312611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31431076497421759430208407 47146614746132639145312611)
        ·
          refine ⟨70719922119198958717968917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47146614746132639145312611 70719922119198958717968917)
          ·
            refine ⟨3314996349337451189904793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 70719922119198958717968917 3314996349337451189904793)
            ·
              refine ⟨2486247262003088392428595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3314996349337451189904793 2486247262003088392428595)
              ·
                refine ⟨3729370893004632588642893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486247262003088392428595 3729370893004632588642893)
                ·
                  refine ⟨1398514084876737220741085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729370893004632588642893 1398514084876737220741085)
                  ·
                    refine ⟨524442781828776457777907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398514084876737220741085 524442781828776457777907)
                    ·
                      rfl

theorem cell22_1532023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 3, 3].length) (baseStart_1532023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532023 prefixEnd_1532023 := by exact prefixLift 1532023
  have htrace : WordTrace (prefixWord ++ tailWord_1532023) baseStart_1532023 baseEnd_1532023 := by
    simpa [prefixWord, tailWord_1532023, baseEnd_1532023] using wordTrace_append hprefix tailTrace_1532023
  have hstable : (prefixWord ++ tailWord_1532023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532023).length < 2 ^ (prefixWord ++ tailWord_1532023).sum := by decide
  have hdescent : baseEnd_1532023 < baseStart_1532023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532049 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1532049 : Nat := 118140960795 + 1532049 * 2 ^ 59
def prefixEnd_1532049 : Nat := 4983230072969 + 3 ^ 40 * 1532049 * 2
def baseEnd_1532049 : Nat := 524451682160121056627827

theorem tailTrace_1532049 : CollatzResearch.WordTrace tailWord_1532049 prefixEnd_1532049 524451682160121056627827 := by
  unfold tailWord_1532049
  simp only [CollatzResearch.WordTrace]
  refine ⟨55878417626655600983039201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37252278417770400655359467 55878417626655600983039201)
  ·
    refine ⟨41908813219991700737279401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55878417626655600983039201 41908813219991700737279401)
    ·
      refine ⟨31431609914993775552959551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41908813219991700737279401 31431609914993775552959551)
      ·
        refine ⟨47147414872490663329439327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31431609914993775552959551 47147414872490663329439327)
        ·
          refine ⟨70721122308735994994158991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47147414872490663329439327 70721122308735994994158991)
          ·
            refine ⟨106081683463103992491238487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70721122308735994994158991 106081683463103992491238487)
            ·
              refine ⟨159122525194655988736857731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106081683463103992491238487 159122525194655988736857731)
              ·
                refine ⟨238683787791983983105286597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159122525194655988736857731 238683787791983983105286597)
                ·
                  refine ⟨44753210210996996832241237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 238683787791983983105286597 44753210210996996832241237)
                  ·
                    refine ⟨524451682160121056627827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44753210210996996832241237 524451682160121056627827)
                    ·
                      rfl

theorem cell22_1532049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1532049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532049 prefixEnd_1532049 := by exact prefixLift 1532049
  have htrace : WordTrace (prefixWord ++ tailWord_1532049) baseStart_1532049 baseEnd_1532049 := by
    simpa [prefixWord, tailWord_1532049, baseEnd_1532049] using wordTrace_append hprefix tailTrace_1532049
  have hstable : (prefixWord ++ tailWord_1532049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532049).length < 2 ^ (prefixWord ++ tailWord_1532049).sum := by decide
  have hdescent : baseEnd_1532049 < baseStart_1532049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532074 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_1532074 : Nat := 118140960795 + 1532074 * 2 ^ 59
def prefixEnd_1532074 : Nat := 4983230072969 + 3 ^ 40 * 1532074 * 2
def baseEnd_1532074 : Nat := 524460240171029324752751

theorem tailTrace_1532074 : CollatzResearch.WordTrace tailWord_1532074 prefixEnd_1532074 524460240171029324752751 := by
  unfold tailWord_1532074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13969832362891257563174819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37252886301043353501799517 13969832362891257563174819)
  ·
    refine ⟨20954748544336886344762229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13969832362891257563174819 20954748544336886344762229)
    ·
      refine ⟨1964507676031583094821459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20954748544336886344762229 1964507676031583094821459)
      ·
        refine ⟨2946761514047374642232189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964507676031583094821459 2946761514047374642232189)
        ·
          refine ⟨1105035567767765490837071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2946761514047374642232189 1105035567767765490837071)
          ·
            refine ⟨1657553351651648236255607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105035567767765490837071 1657553351651648236255607)
            ·
              refine ⟨2486330027477472354383411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657553351651648236255607 2486330027477472354383411)
              ·
                refine ⟨3729495041216208531575117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486330027477472354383411 3729495041216208531575117)
                ·
                  refine ⟨1398560640456078199340669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729495041216208531575117 1398560640456078199340669)
                  ·
                    refine ⟨524460240171029324752751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398560640456078199340669 524460240171029324752751)
                    ·
                      rfl

theorem cell22_1532074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_1532074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532074 prefixEnd_1532074 := by exact prefixLift 1532074
  have htrace : WordTrace (prefixWord ++ tailWord_1532074) baseStart_1532074 baseEnd_1532074 := by
    simpa [prefixWord, tailWord_1532074, baseEnd_1532074] using wordTrace_append hprefix tailTrace_1532074
  have hstable : (prefixWord ++ tailWord_1532074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532074).length < 2 ^ (prefixWord ++ tailWord_1532074).sum := by decide
  have hdescent : baseEnd_1532074 < baseStart_1532074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532100 : List Nat := [2, 3, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_1532100 : Nat := 118140960795 + 1532100 * 2 ^ 59
def prefixEnd_1532100 : Nat := 4983230072969 + 3 ^ 40 * 1532100 * 2
def baseEnd_1532100 : Nat := 524469140502373923602671

theorem tailTrace_1532100 : CollatzResearch.WordTrace tailWord_1532100 prefixEnd_1532100 524469140502373923602671 := by
  unfold tailWord_1532100
  simp only [CollatzResearch.WordTrace]
  refine ⟨27940138874735418346572877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37253518499647224462097169 27940138874735418346572877)
  ·
    refine ⟨10477552078025781879964829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27940138874735418346572877 10477552078025781879964829)
    ·
      refine ⟨3929082029259668204986811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10477552078025781879964829 3929082029259668204986811)
      ·
        refine ⟨5893623043889502307480217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929082029259668204986811 5893623043889502307480217)
        ·
          refine ⟨4420217282917126730610163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893623043889502307480217 4420217282917126730610163)
          ·
            refine ⟨6630325924375690095915245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420217282917126730610163 6630325924375690095915245)
            ·
              refine ⟨2486372221640883785968217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6630325924375690095915245 2486372221640883785968217)
              ·
                refine ⟨1864779166230662839476163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486372221640883785968217 1864779166230662839476163)
                ·
                  refine ⟨2797168749345994259214245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864779166230662839476163 2797168749345994259214245)
                  ·
                    refine ⟨524469140502373923602671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797168749345994259214245 524469140502373923602671)
                    ·
                      rfl

theorem cell22_1532100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_1532100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532100 prefixEnd_1532100 := by exact prefixLift 1532100
  have htrace : WordTrace (prefixWord ++ tailWord_1532100) baseStart_1532100 baseEnd_1532100 := by
    simpa [prefixWord, tailWord_1532100, baseEnd_1532100] using wordTrace_append hprefix tailTrace_1532100
  have hstable : (prefixWord ++ tailWord_1532100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532100).length < 2 ^ (prefixWord ++ tailWord_1532100).sum := by decide
  have hdescent : baseEnd_1532100 < baseStart_1532100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532117 : List Nat := [1, 3, 2, 4, 2, 1, 3, 1, 1, 4]
def baseStart_1532117 : Nat := 118140960795 + 1532117 * 2 ^ 59
def prefixEnd_1532117 : Nat := 4983230072969 + 3 ^ 40 * 1532117 * 2
def baseEnd_1532117 : Nat := 524474959949791545927619

theorem tailTrace_1532117 : CollatzResearch.WordTrace tailWord_1532117 prefixEnd_1532117 524474959949791545927619 := by
  unfold tailWord_1532117
  simp only [CollatzResearch.WordTrace]
  refine ⟨55880897790409248596514605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37253931860272832397676403 55880897790409248596514605)
  ·
    refine ⟨20955336671403468223692977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55880897790409248596514605 20955336671403468223692977)
    ·
      refine ⟨15716502503552601167769733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20955336671403468223692977 15716502503552601167769733)
      ·
        refine ⟨2946844219416112718956825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15716502503552601167769733 2946844219416112718956825)
        ·
          refine ⟨2210133164562084539217619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2946844219416112718956825 2210133164562084539217619)
          ·
            refine ⟨3315199746843126808826429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210133164562084539217619 3315199746843126808826429)
            ·
              refine ⟨1243199905066172553309911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3315199746843126808826429 1243199905066172553309911)
              ·
                refine ⟨1864799857599258829964867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243199905066172553309911 1864799857599258829964867)
                ·
                  refine ⟨2797199786398888244947301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1864799857599258829964867 2797199786398888244947301)
                  ·
                    refine ⟨524474959949791545927619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797199786398888244947301 524474959949791545927619)
                    ·
                      rfl

theorem cell22_1532117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_1532117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532117 prefixEnd_1532117 := by exact prefixLift 1532117
  have htrace : WordTrace (prefixWord ++ tailWord_1532117) baseStart_1532117 baseEnd_1532117 := by
    simpa [prefixWord, tailWord_1532117, baseEnd_1532117] using wordTrace_append hprefix tailTrace_1532117
  have hstable : (prefixWord ++ tailWord_1532117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532117).length < 2 ^ (prefixWord ++ tailWord_1532117).sum := by decide
  have hdescent : baseEnd_1532117 < baseStart_1532117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532143 : List Nat := [1, 1, 2, 1, 6, 3, 1, 7]
def baseStart_1532143 : Nat := 118140960795 + 1532143 * 2 ^ 59
def prefixEnd_1532143 : Nat := 4983230072969 + 3 ^ 40 * 1532143 * 2
def baseEnd_1532143 : Nat := 58275984475681793864171

theorem tailTrace_1532143 : CollatzResearch.WordTrace tailWord_1532143 prefixEnd_1532143 58275984475681793864171 := by
  unfold tailWord_1532143
  simp only [CollatzResearch.WordTrace]
  refine ⟨55881846088315055036961083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37254564058876703357974055 55881846088315055036961083)
  ·
    refine ⟨83822769132472582555441625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55881846088315055036961083 83822769132472582555441625)
    ·
      refine ⟨62867076849354436916581219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83822769132472582555441625 62867076849354436916581219)
      ·
        refine ⟨94300615274031655374871829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62867076849354436916581219 94300615274031655374871829)
        ·
          refine ⟨4420341340970233845697117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94300615274031655374871829 4420341340970233845697117)
          ·
            refine ⟨1657628002863837692136419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4420341340970233845697117 1657628002863837692136419)
            ·
              refine ⟨2486442004295756538204629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657628002863837692136419 2486442004295756538204629)
              ·
                refine ⟨58275984475681793864171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2486442004295756538204629 58275984475681793864171)
                ·
                  rfl

theorem cell22_1532143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 7].length) (baseStart_1532143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532143 prefixEnd_1532143 := by exact prefixLift 1532143
  have htrace : WordTrace (prefixWord ++ tailWord_1532143) baseStart_1532143 baseEnd_1532143 := by
    simpa [prefixWord, tailWord_1532143, baseEnd_1532143] using wordTrace_append hprefix tailTrace_1532143
  have hstable : (prefixWord ++ tailWord_1532143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532143).length < 2 ^ (prefixWord ++ tailWord_1532143).sum := by decide
  have hdescent : baseEnd_1532143 < baseStart_1532143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532162 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1532162 : Nat := 118140960795 + 1532162 * 2 ^ 59
def prefixEnd_1532162 : Nat := 4983230072969 + 3 ^ 40 * 1532162 * 2
def baseEnd_1532162 : Nat := 524490364369426428552481

theorem tailTrace_1532162 : CollatzResearch.WordTrace tailWord_1532162 prefixEnd_1532162 524490364369426428552481 := by
  unfold tailWord_1532162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970634768811555320475685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37255026050164147521268493 13970634768811555320475685)
  ·
    refine ⟨2619494019152166622589191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13970634768811555320475685 2619494019152166622589191)
    ·
      refine ⟨3929241028728249933883787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619494019152166622589191 3929241028728249933883787)
      ·
        refine ⟨5893861543092374900825681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929241028728249933883787 5893861543092374900825681)
        ·
          refine ⟨4420396157319281175619261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893861543092374900825681 4420396157319281175619261)
          ·
            refine ⟨1657648558994730440857223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4420396157319281175619261 1657648558994730440857223)
            ·
              refine ⟨2486472838492095661285835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657648558994730440857223 2486472838492095661285835)
              ·
                refine ⟨3729709257738143491928753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2486472838492095661285835 3729709257738143491928753)
                ·
                  refine ⟨2797281943303607618946565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3729709257738143491928753 2797281943303607618946565)
                  ·
                    refine ⟨524490364369426428552481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797281943303607618946565 524490364369426428552481)
                    ·
                      rfl

theorem cell22_1532162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1532162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532162 prefixEnd_1532162 := by exact prefixLift 1532162
  have htrace : WordTrace (prefixWord ++ tailWord_1532162) baseStart_1532162 baseEnd_1532162 := by
    simpa [prefixWord, tailWord_1532162, baseEnd_1532162] using wordTrace_append hprefix tailTrace_1532162
  have hstable : (prefixWord ++ tailWord_1532162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532162).length < 2 ^ (prefixWord ++ tailWord_1532162).sum := by decide
  have hdescent : baseEnd_1532162 < baseStart_1532162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532171 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 7]
def baseStart_1532171 : Nat := 118140960795 + 1532171 * 2 ^ 59
def prefixEnd_1532171 : Nat := 4983230072969 + 3 ^ 40 * 1532171 * 2
def baseEnd_1532171 : Nat := 174831148417784468359151

theorem tailTrace_1532171 : CollatzResearch.WordTrace tailWord_1532171 prefixEnd_1532171 174831148417784468359151 := by
  unfold tailWord_1532171
  simp only [CollatzResearch.WordTrace]
  refine ⟨55882867332213615818980367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37255244888142410545986911 55882867332213615818980367)
  ·
    refine ⟨83824300998320423728470551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55882867332213615818980367 83824300998320423728470551)
    ·
      refine ⟨125736451497480635592705827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83824300998320423728470551 125736451497480635592705827)
      ·
        refine ⟨188604677246220953389058741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125736451497480635592705827 188604677246220953389058741)
        ·
          refine ⟨17681688491833214380224257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 188604677246220953389058741 17681688491833214380224257)
          ·
            refine ⟨13261266368874910785168193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17681688491833214380224257 13261266368874910785168193)
            ·
              refine ⟨9945949776656183088876145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13261266368874910785168193 9945949776656183088876145)
              ·
                refine ⟨7459462332492137316657109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9945949776656183088876145 7459462332492137316657109)
                ·
                  refine ⟨174831148417784468359151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7459462332492137316657109 174831148417784468359151)
                  ·
                    rfl

theorem cell22_1532171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 7].length) (baseStart_1532171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532171 prefixEnd_1532171 := by exact prefixLift 1532171
  have htrace : WordTrace (prefixWord ++ tailWord_1532171) baseStart_1532171 baseEnd_1532171 := by
    simpa [prefixWord, tailWord_1532171, baseEnd_1532171] using wordTrace_append hprefix tailTrace_1532171
  have hstable : (prefixWord ++ tailWord_1532171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532171).length < 2 ^ (prefixWord ++ tailWord_1532171).sum := by decide
  have hdescent : baseEnd_1532171 < baseStart_1532171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532192 : List Nat := [2, 1, 1, 5, 2, 1, 2, 4, 1, 3]
def baseStart_1532192 : Nat := 118140960795 + 1532192 * 2 ^ 59
def prefixEnd_1532192 : Nat := 4983230072969 + 3 ^ 40 * 1532192 * 2
def baseEnd_1532192 : Nat := 524500633982516350302389

theorem tailTrace_1532192 : CollatzResearch.WordTrace tailWord_1532192 prefixEnd_1532192 524500633982516350302389 := by
  unfold tailWord_1532192
  simp only [CollatzResearch.WordTrace]
  refine ⟨27941816632568768202747415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37255755510091690936996553 27941816632568768202747415)
  ·
    refine ⟨41912724948853152304121123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27941816632568768202747415 41912724948853152304121123)
    ·
      refine ⟨62869087423279728456181685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41912724948853152304121123 62869087423279728456181685)
      ·
        refine ⟨5893976945932474542767033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 62869087423279728456181685 5893976945932474542767033)
        ·
          refine ⟨4420482709449355907075275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5893976945932474542767033 4420482709449355907075275)
          ·
            refine ⟨6630724064174033860612913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420482709449355907075275 6630724064174033860612913)
            ·
              refine ⟨4973043048130525395459685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6630724064174033860612913 4973043048130525395459685)
              ·
                refine ⟨932445571524473511648691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4973043048130525395459685 932445571524473511648691)
                ·
                  refine ⟨1398668357286710267473037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932445571524473511648691 1398668357286710267473037)
                  ·
                    refine ⟨524500633982516350302389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398668357286710267473037 524500633982516350302389)
                    ·
                      rfl

theorem cell22_1532192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 1, 3].length) (baseStart_1532192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532192 prefixEnd_1532192 := by exact prefixLift 1532192
  have htrace : WordTrace (prefixWord ++ tailWord_1532192) baseStart_1532192 baseEnd_1532192 := by
    simpa [prefixWord, tailWord_1532192, baseEnd_1532192] using wordTrace_append hprefix tailTrace_1532192
  have hstable : (prefixWord ++ tailWord_1532192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532192).length < 2 ^ (prefixWord ++ tailWord_1532192).sum := by decide
  have hdescent : baseEnd_1532192 < baseStart_1532192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532265 : List Nat := [1, 2, 1, 1, 1, 3, 5, 3, 2, 3]
def baseStart_1532265 : Nat := 118140960795 + 1532265 * 2 ^ 59
def prefixEnd_1532265 : Nat := 4983230072969 + 3 ^ 40 * 1532265 * 2
def baseEnd_1532265 : Nat := 524525623374368493227165

theorem tailTrace_1532265 : CollatzResearch.WordTrace tailWord_1532265 prefixEnd_1532265 524525623374368493227165 := by
  unfold tailWord_1532265
  simp only [CollatzResearch.WordTrace]
  refine ⟨55886295793873069872902249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37257530529248713248601499 55886295793873069872902249)
  ·
    refine ⟨41914721845404802404676687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55886295793873069872902249 41914721845404802404676687)
    ·
      refine ⟨62872082768107203607015031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41914721845404802404676687 62872082768107203607015031)
      ·
        refine ⟨94308124152160805410522547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62872082768107203607015031 94308124152160805410522547)
        ·
          refine ⟨141462186228241208115783821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94308124152160805410522547 141462186228241208115783821)
          ·
            refine ⟨53048319835590453043418933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141462186228241208115783821 53048319835590453043418933)
            ·
              refine ⟨4973279984586604972820525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53048319835590453043418933 4973279984586604972820525)
              ·
                refine ⟨1864979994219976864807697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4973279984586604972820525 1864979994219976864807697)
                ·
                  refine ⟨1398734995664982648605773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1864979994219976864807697 1398734995664982648605773)
                  ·
                    refine ⟨524525623374368493227165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398734995664982648605773 524525623374368493227165)
                    ·
                      rfl

theorem cell22_1532265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 3, 2, 3].length) (baseStart_1532265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532265 prefixEnd_1532265 := by exact prefixLift 1532265
  have htrace : WordTrace (prefixWord ++ tailWord_1532265) baseStart_1532265 baseEnd_1532265 := by
    simpa [prefixWord, tailWord_1532265, baseEnd_1532265] using wordTrace_append hprefix tailTrace_1532265
  have hstable : (prefixWord ++ tailWord_1532265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532265).length < 2 ^ (prefixWord ++ tailWord_1532265).sum := by decide
  have hdescent : baseEnd_1532265 < baseStart_1532265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532327 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1532327 : Nat := 118140960795 + 1532327 * 2 ^ 59
def prefixEnd_1532327 : Nat := 4983230072969 + 3 ^ 40 * 1532327 * 2
def baseEnd_1532327 : Nat := 524546847241420998176975

theorem tailTrace_1532327 : CollatzResearch.WordTrace tailWord_1532327 prefixEnd_1532327 524546847241420998176975 := by
  unfold tailWord_1532327
  simp only [CollatzResearch.WordTrace]
  refine ⟨55888557119648454461659235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37259038079765636307772823 55888557119648454461659235)
  ·
    refine ⟨83832835679472681692488853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55888557119648454461659235 83832835679472681692488853)
    ·
      refine ⟨3929664172475281954335415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83832835679472681692488853 3929664172475281954335415)
      ·
        refine ⟨5894496258712922931503123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929664172475281954335415 5894496258712922931503123)
        ·
          refine ⟨8841744388069384397254685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894496258712922931503123 8841744388069384397254685)
          ·
            refine ⟨3315654145526019148970507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8841744388069384397254685 3315654145526019148970507)
            ·
              refine ⟨4973481218289028723455761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315654145526019148970507 4973481218289028723455761)
              ·
                refine ⟨3730110913716771542591821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4973481218289028723455761 3730110913716771542591821)
                ·
                  refine ⟨1398791592643789328471933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3730110913716771542591821 1398791592643789328471933)
                  ·
                    refine ⟨524546847241420998176975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398791592643789328471933 524546847241420998176975)
                    ·
                      rfl

theorem cell22_1532327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1532327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532327 prefixEnd_1532327 := by exact prefixLift 1532327
  have htrace : WordTrace (prefixWord ++ tailWord_1532327) baseStart_1532327 baseEnd_1532327 := by
    simpa [prefixWord, tailWord_1532327, baseEnd_1532327] using wordTrace_append hprefix tailTrace_1532327
  have hstable : (prefixWord ++ tailWord_1532327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532327).length < 2 ^ (prefixWord ++ tailWord_1532327).sum := by decide
  have hdescent : baseEnd_1532327 < baseStart_1532327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532338 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1532338 : Nat := 118140960795 + 1532338 * 2 ^ 59
def prefixEnd_1532338 : Nat := 4983230072969 + 3 ^ 40 * 1532338 * 2
def baseEnd_1532338 : Nat := 524550612766220636151941

theorem tailTrace_1532338 : CollatzResearch.WordTrace tailWord_1532338 prefixEnd_1532338 524550612766220636151941 := by
  unfold tailWord_1532338
  simp only [CollatzResearch.WordTrace]
  refine ⟨13972239580652150835077417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37259305548405735560206445 13972239580652150835077417)
  ·
    refine ⟨10479179685489113126308063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13972239580652150835077417 10479179685489113126308063)
    ·
      refine ⟨15718769528233669689462095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479179685489113126308063 15718769528233669689462095)
      ·
        refine ⟨23578154292350504534193143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15718769528233669689462095 23578154292350504534193143)
        ·
          refine ⟨35367231438525756801289715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23578154292350504534193143 35367231438525756801289715)
          ·
            refine ⟨53050847157788635201934573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35367231438525756801289715 53050847157788635201934573)
            ·
              refine ⟨19894067684170738200725465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53050847157788635201934573 19894067684170738200725465)
              ·
                refine ⟨14920550763128053650544099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19894067684170738200725465 14920550763128053650544099)
                ·
                  refine ⟨22380826144692080475816149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14920550763128053650544099 22380826144692080475816149)
                  ·
                    refine ⟨524550612766220636151941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22380826144692080475816149 524550612766220636151941)
                    ·
                      rfl

theorem cell22_1532338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1532338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532338 prefixEnd_1532338 := by exact prefixLift 1532338
  have htrace : WordTrace (prefixWord ++ tailWord_1532338) baseStart_1532338 baseEnd_1532338 := by
    simpa [prefixWord, tailWord_1532338, baseEnd_1532338] using wordTrace_append hprefix tailTrace_1532338
  have hstable : (prefixWord ++ tailWord_1532338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532338).length < 2 ^ (prefixWord ++ tailWord_1532338).sum := by decide
  have hdescent : baseEnd_1532338 < baseStart_1532338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532374 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_1532374 : Nat := 118140960795 + 1532374 * 2 ^ 59
def prefixEnd_1532374 : Nat := 4983230072969 + 3 ^ 40 * 1532374 * 2
def baseEnd_1532374 : Nat := 174854312100642847417277

theorem tailTrace_1532374 : CollatzResearch.WordTrace tailWord_1532374 prefixEnd_1532374 174854312100642847417277 := by
  unfold tailWord_1532374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493141959404886343038761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37260180900318787659080117 3493141959404886343038761)
  ·
    refine ⟨2619856469553664757279071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3493141959404886343038761 2619856469553664757279071)
    ·
      refine ⟨3929784704330497135918607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619856469553664757279071 3929784704330497135918607)
      ·
        refine ⟨5894677056495745703877911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929784704330497135918607 5894677056495745703877911)
        ·
          refine ⟨8842015584743618555816867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5894677056495745703877911 8842015584743618555816867)
          ·
            refine ⟨13263023377115427833725301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8842015584743618555816867 13263023377115427833725301)
            ·
              refine ⟨1243408441604571359411747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13263023377115427833725301 1243408441604571359411747)
              ·
                refine ⟨1865112662406857039117621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243408441604571359411747 1865112662406857039117621)
                ·
                  refine ⟨174854312100642847417277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1865112662406857039117621 174854312100642847417277)
                  ·
                    rfl

theorem cell22_1532374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_1532374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532374 prefixEnd_1532374 := by exact prefixLift 1532374
  have htrace : WordTrace (prefixWord ++ tailWord_1532374) baseStart_1532374 baseEnd_1532374 := by
    simpa [prefixWord, tailWord_1532374, baseEnd_1532374] using wordTrace_append hprefix tailTrace_1532374
  have hstable : (prefixWord ++ tailWord_1532374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532374).length < 2 ^ (prefixWord ++ tailWord_1532374).sum := by decide
  have hdescent : baseEnd_1532374 < baseStart_1532374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532400 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 6, 3]
def baseStart_1532400 : Nat := 118140960795 + 1532400 * 2 ^ 59
def prefixEnd_1532400 : Nat := 4983230072969 + 3 ^ 40 * 1532400 * 2
def baseEnd_1532400 : Nat := 524571836633273141101751

theorem tailTrace_1532400 : CollatzResearch.WordTrace tailWord_1532400 prefixEnd_1532400 524571836633273141101751 := by
  unfold tailWord_1532400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27945609824191993964533327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37260813098922658619377769 27945609824191993964533327)
  ·
    refine ⟨41918414736287990946799991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27945609824191993964533327 41918414736287990946799991)
    ·
      refine ⟨62877622104431986420199987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41918414736287990946799991 62877622104431986420199987)
      ·
        refine ⟨94316433156647979630299981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62877622104431986420199987 94316433156647979630299981)
        ·
          refine ⟨35368662433742992361362493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94316433156647979630299981 35368662433742992361362493)
          ·
            refine ⟨13263248412653622135510935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35368662433742992361362493 13263248412653622135510935)
            ·
              refine ⟨19894872618980433203266403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13263248412653622135510935 19894872618980433203266403)
              ·
                refine ⟨29842308928470649804899605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19894872618980433203266403 29842308928470649804899605)
                ·
                  refine ⟨1398858231022061709604669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29842308928470649804899605 1398858231022061709604669)
                  ·
                    refine ⟨524571836633273141101751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398858231022061709604669 524571836633273141101751)
                    ·
                      rfl

theorem cell22_1532400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_1532400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532400 prefixEnd_1532400 := by exact prefixLift 1532400
  have htrace : WordTrace (prefixWord ++ tailWord_1532400) baseStart_1532400 baseEnd_1532400 := by
    simpa [prefixWord, tailWord_1532400, baseEnd_1532400] using wordTrace_append hprefix tailTrace_1532400
  have hstable : (prefixWord ++ tailWord_1532400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532400).length < 2 ^ (prefixWord ++ tailWord_1532400).sum := by decide
  have hdescent : baseEnd_1532400 < baseStart_1532400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532415 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 2, 4]
def baseStart_1532415 : Nat := 118140960795 + 1532415 * 2 ^ 59
def prefixEnd_1532415 : Nat := 4983230072969 + 3 ^ 40 * 1532415 * 2
def baseEnd_1532415 : Nat := 524576971439818101976705

theorem tailTrace_1532415 : CollatzResearch.WordTrace tailWord_1532415 prefixEnd_1532415 524576971439818101976705 := by
  unfold tailWord_1532415
  simp only [CollatzResearch.WordTrace]
  refine ⟨55891766743329645490862699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37261177828886430327241799 55891766743329645490862699)
  ·
    refine ⟨83837650114994468236294049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55891766743329645490862699 83837650114994468236294049)
    ·
      refine ⟨62878237586245851177220537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83837650114994468236294049 62878237586245851177220537)
      ·
        refine ⟨47158678189684388382915403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62878237586245851177220537 47158678189684388382915403)
        ·
          refine ⟨70738017284526582574373105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47158678189684388382915403 70738017284526582574373105)
          ·
            refine ⟨53053512963394936930779829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70738017284526582574373105 53053512963394936930779829)
            ·
              refine ⟨4973766840318275337260609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53053512963394936930779829 4973766840318275337260609)
              ·
                refine ⟨3730325130238706502945457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4973766840318275337260609 3730325130238706502945457)
                ·
                  refine ⟨2797743847679029877209093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730325130238706502945457 2797743847679029877209093)
                  ·
                    refine ⟨524576971439818101976705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2797743847679029877209093 524576971439818101976705)
                    ·
                      rfl

theorem cell22_1532415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_1532415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532415 prefixEnd_1532415 := by exact prefixLift 1532415
  have htrace : WordTrace (prefixWord ++ tailWord_1532415) baseStart_1532415 baseEnd_1532415 := by
    simpa [prefixWord, tailWord_1532415, baseEnd_1532415] using wordTrace_append hprefix tailTrace_1532415
  have hstable : (prefixWord ++ tailWord_1532415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532415).length < 2 ^ (prefixWord ++ tailWord_1532415).sum := by decide
  have hdescent : baseEnd_1532415 < baseStart_1532415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532417 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 4, 3]
def baseStart_1532417 : Nat := 118140960795 + 1532417 * 2 ^ 59
def prefixEnd_1532417 : Nat := 4983230072969 + 3 ^ 40 * 1532417 * 2
def baseEnd_1532417 : Nat := 524577656080690763426699

theorem tailTrace_1532417 : CollatzResearch.WordTrace tailWord_1532417 prefixEnd_1532417 524577656080690763426699 := by
  unfold tailWord_1532417
  simp only [CollatzResearch.WordTrace]
  refine ⟨55891839689322399832435505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37261226459548266554957003 55891839689322399832435505)
  ·
    refine ⟨41918879766991799874326629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55891839689322399832435505 41918879766991799874326629)
    ·
      refine ⟨7859789956310962476436243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41918879766991799874326629 7859789956310962476436243)
      ·
        refine ⟨11789684934466443714654365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7859789956310962476436243 11789684934466443714654365)
        ·
          refine ⟨4421131850424916392995387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11789684934466443714654365 4421131850424916392995387)
          ·
            refine ⟨6631697775637374589493081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421131850424916392995387 6631697775637374589493081)
            ·
              refine ⟨4973773331728030942119811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6631697775637374589493081 4973773331728030942119811)
              ·
                refine ⟨7460659997592046413179717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4973773331728030942119811 7460659997592046413179717)
                ·
                  refine ⟨1398873749548508702471197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7460659997592046413179717 1398873749548508702471197)
                  ·
                    refine ⟨524577656080690763426699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398873749548508702471197 524577656080690763426699)
                    ·
                      rfl

theorem cell22_1532417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_1532417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532417 prefixEnd_1532417 := by exact prefixLift 1532417
  have htrace : WordTrace (prefixWord ++ tailWord_1532417) baseStart_1532417 baseEnd_1532417 := by
    simpa [prefixWord, tailWord_1532417, baseEnd_1532417] using wordTrace_append hprefix tailTrace_1532417
  have hstable : (prefixWord ++ tailWord_1532417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532417).length < 2 ^ (prefixWord ++ tailWord_1532417).sum := by decide
  have hdescent : baseEnd_1532417 < baseStart_1532417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532430 : List Nat := [4, 1, 1, 2, 3, 1, 1, 9]
def baseStart_1532430 : Nat := 118140960795 + 1532430 * 2 ^ 59
def prefixEnd_1532430 : Nat := 4983230072969 + 3 ^ 40 * 1532430 * 2
def baseEnd_1532430 : Nat := 58286900694040340316851

theorem tailTrace_1532430 : CollatzResearch.WordTrace tailWord_1532430 prefixEnd_1532430 58286900694040340316851 := by
  unfold tailWord_1532430
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986539229784412881582343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37261542558850202035105829 6986539229784412881582343)
  ·
    refine ⟨10479808844676619322373515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6986539229784412881582343 10479808844676619322373515)
    ·
      refine ⟨15719713267014928983560273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10479808844676619322373515 15719713267014928983560273)
      ·
        refine ⟨11789784950261196737670205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15719713267014928983560273 11789784950261196737670205)
        ·
          refine ⟨4421169356347948776626327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11789784950261196737670205 4421169356347948776626327)
          ·
            refine ⟨6631754034521923164939491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4421169356347948776626327 6631754034521923164939491)
            ·
              refine ⟨9947631051782884747409237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6631754034521923164939491 9947631051782884747409237)
              ·
                refine ⟨58286900694040340316851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9947631051782884747409237 58286900694040340316851)
                ·
                  rfl

theorem cell22_1532430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 9].length) (baseStart_1532430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532430 prefixEnd_1532430 := by exact prefixLift 1532430
  have htrace : WordTrace (prefixWord ++ tailWord_1532430) baseStart_1532430 baseEnd_1532430 := by
    simpa [prefixWord, tailWord_1532430, baseEnd_1532430] using wordTrace_append hprefix tailTrace_1532430
  have hstable : (prefixWord ++ tailWord_1532430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532430).length < 2 ^ (prefixWord ++ tailWord_1532430).sum := by decide
  have hdescent : baseEnd_1532430 < baseStart_1532430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532468 : List Nat := [2, 5, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1532468 : Nat := 118140960795 + 1532468 * 2 ^ 59
def prefixEnd_1532468 : Nat := 4983230072969 + 3 ^ 40 * 1532468 * 2
def baseEnd_1532468 : Nat := 524595114422943630401543

theorem tailTrace_1532468 : CollatzResearch.WordTrace tailWord_1532468 prefixEnd_1532468 524595114422943630401543 := by
  unfold tailWord_1532468
  simp only [CollatzResearch.WordTrace]
  refine ⟨27946849906068817771271029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37262466541425090361694705 27946849906068817771271029)
  ·
    refine ⟨2620017178693951666056659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27946849906068817771271029 2620017178693951666056659)
    ·
      refine ⟨3930025768040927499084989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620017178693951666056659 3930025768040927499084989)
      ·
        refine ⟨1473759663015347812156871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3930025768040927499084989 1473759663015347812156871)
        ·
          refine ⟨2210639494523021718235307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473759663015347812156871 2210639494523021718235307)
          ·
            refine ⟨3315959241784532577352961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210639494523021718235307 3315959241784532577352961)
            ·
              refine ⟨2486969431338399433014721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3315959241784532577352961 2486969431338399433014721)
              ·
                refine ⟨1865227073503799574761041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2486969431338399433014721 1865227073503799574761041)
                ·
                  refine ⟨1398920305127849681070781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1865227073503799574761041 1398920305127849681070781)
                  ·
                    refine ⟨524595114422943630401543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398920305127849681070781 524595114422943630401543)
                    ·
                      rfl

theorem cell22_1532468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1532468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532468 prefixEnd_1532468 := by exact prefixLift 1532468
  have htrace : WordTrace (prefixWord ++ tailWord_1532468) baseStart_1532468 baseEnd_1532468 := by
    simpa [prefixWord, tailWord_1532468, baseEnd_1532468] using wordTrace_append hprefix tailTrace_1532468
  have hstable : (prefixWord ++ tailWord_1532468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532468).length < 2 ^ (prefixWord ++ tailWord_1532468).sum := by decide
  have hdescent : baseEnd_1532468 < baseStart_1532468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532479 : List Nat := [1, 1, 2, 2, 3, 2, 3, 4, 1, 3]
def baseStart_1532479 : Nat := 118140960795 + 1532479 * 2 ^ 59
def prefixEnd_1532479 : Nat := 4983230072969 + 3 ^ 40 * 1532479 * 2
def baseEnd_1532479 : Nat := 524598879947743268376509

theorem tailTrace_1532479 : CollatzResearch.WordTrace tailWord_1532479 prefixEnd_1532479 524598879947743268376509 := by
  unfold tailWord_1532479
  simp only [CollatzResearch.WordTrace]
  refine ⟨55894101015097784421192491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37262734010065189614128327 55894101015097784421192491)
  ·
    refine ⟨83841151522646676631788737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55894101015097784421192491 83841151522646676631788737)
    ·
      refine ⟨62880863641985007473841553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83841151522646676631788737 62880863641985007473841553)
      ·
        refine ⟨47160647731488755605381165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62880863641985007473841553 47160647731488755605381165)
        ·
          refine ⟨17685242899308283352017937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47160647731488755605381165 17685242899308283352017937)
          ·
            refine ⟨13263932174481212514013453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17685242899308283352017937 13263932174481212514013453)
            ·
              refine ⟨4973974565430454692755045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13263932174481212514013453 4973974565430454692755045)
              ·
                refine ⟨932620231018210254891571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4973974565430454692755045 932620231018210254891571)
                ·
                  refine ⟨1398930346527315382337357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932620231018210254891571 1398930346527315382337357)
                  ·
                    refine ⟨524598879947743268376509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398930346527315382337357 524598879947743268376509)
                    ·
                      rfl

theorem cell22_1532479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 1, 3].length) (baseStart_1532479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532479 prefixEnd_1532479 := by exact prefixLift 1532479
  have htrace : WordTrace (prefixWord ++ tailWord_1532479) baseStart_1532479 baseEnd_1532479 := by
    simpa [prefixWord, tailWord_1532479, baseEnd_1532479] using wordTrace_append hprefix tailTrace_1532479
  have hstable : (prefixWord ++ tailWord_1532479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532479).length < 2 ^ (prefixWord ++ tailWord_1532479).sum := by decide
  have hdescent : baseEnd_1532479 < baseStart_1532479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532490 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1532490 : Nat := 118140960795 + 1532490 * 2 ^ 59
def prefixEnd_1532490 : Nat := 4983230072969 + 3 ^ 40 * 1532490 * 2
def baseEnd_1532490 : Nat := 524602645472542906351475

theorem tailTrace_1532490 : CollatzResearch.WordTrace tailWord_1532490 prefixEnd_1532490 524602645472542906351475 := by
  unfold tailWord_1532490
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973625554514483324960731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37263001478705288866561949 13973625554514483324960731)
  ·
    refine ⟨20960438331771724987441097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13973625554514483324960731 20960438331771724987441097)
    ·
      refine ⟨15720328748828793740580823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20960438331771724987441097 15720328748828793740580823)
      ·
        refine ⟨23580493123243190610871235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15720328748828793740580823 23580493123243190610871235)
        ·
          refine ⟨35370739684864785916306853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23580493123243190610871235 35370739684864785916306853)
          ·
            refine ⟨6632013690912147359307535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35370739684864785916306853 6632013690912147359307535)
            ·
              refine ⟨9948020536368221038961303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6632013690912147359307535 9948020536368221038961303)
              ·
                refine ⟨14922030804552331558441955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948020536368221038961303 14922030804552331558441955)
                ·
                  refine ⟨22383046206828497337662933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14922030804552331558441955 22383046206828497337662933)
                  ·
                    refine ⟨524602645472542906351475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22383046206828497337662933 524602645472542906351475)
                    ·
                      rfl

theorem cell22_1532490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1532490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532490 prefixEnd_1532490 := by exact prefixLift 1532490
  have htrace : WordTrace (prefixWord ++ tailWord_1532490) baseStart_1532490 baseEnd_1532490 := by
    simpa [prefixWord, tailWord_1532490, baseEnd_1532490] using wordTrace_append hprefix tailTrace_1532490
  have hstable : (prefixWord ++ tailWord_1532490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532490).length < 2 ^ (prefixWord ++ tailWord_1532490).sum := by decide
  have hdescent : baseEnd_1532490 < baseStart_1532490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532535 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1532535 : Nat := 118140960795 + 1532535 * 2 ^ 59
def prefixEnd_1532535 : Nat := 4983230072969 + 3 ^ 40 * 1532535 * 2
def baseEnd_1532535 : Nat := 524618049892177788976337

theorem tailTrace_1532535 : CollatzResearch.WordTrace tailWord_1532535 prefixEnd_1532535 524618049892177788976337 := by
  unfold tailWord_1532535
  simp only [CollatzResearch.WordTrace]
  refine ⟨55896143502894905985231059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37264095668596603990154039 55896143502894905985231059)
  ·
    refine ⟨83844215254342358977846589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55896143502894905985231059 83844215254342358977846589)
    ·
      refine ⟨31441580720378384616692471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83844215254342358977846589 31441580720378384616692471)
      ·
        refine ⟨47162371080567576925038707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31441580720378384616692471 47162371080567576925038707)
        ·
          refine ⟨70743556620851365387558061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47162371080567576925038707 70743556620851365387558061)
          ·
            refine ⟨26528833732819262020334273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70743556620851365387558061 26528833732819262020334273)
            ·
              refine ⟨19896625299614446515250705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26528833732819262020334273 19896625299614446515250705)
              ·
                refine ⟨14922468974710834886438029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19896625299614446515250705 14922468974710834886438029)
                ·
                  refine ⟨5595925865516563082414261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14922468974710834886438029 5595925865516563082414261)
                  ·
                    refine ⟨524618049892177788976337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5595925865516563082414261 524618049892177788976337)
                    ·
                      rfl

theorem cell22_1532535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1532535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532535 prefixEnd_1532535 := by exact prefixLift 1532535
  have htrace : WordTrace (prefixWord ++ tailWord_1532535) baseStart_1532535 baseEnd_1532535 := by
    simpa [prefixWord, tailWord_1532535, baseEnd_1532535] using wordTrace_append hprefix tailTrace_1532535
  have hstable : (prefixWord ++ tailWord_1532535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532535).length < 2 ^ (prefixWord ++ tailWord_1532535).sum := by decide
  have hdescent : baseEnd_1532535 < baseStart_1532535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532537 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 6]
def baseStart_1532537 : Nat := 118140960795 + 1532537 * 2 ^ 59
def prefixEnd_1532537 : Nat := 4983230072969 + 3 ^ 40 * 1532537 * 2
def baseEnd_1532537 : Nat := 174872911511016816808777

theorem tailTrace_1532537 : CollatzResearch.WordTrace tailWord_1532537 prefixEnd_1532537 174872911511016816808777 := by
  unfold tailWord_1532537
  simp only [CollatzResearch.WordTrace]
  refine ⟨55896216448887660326803865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37264144299258440217869243 55896216448887660326803865)
  ·
    refine ⟨41922162336665745245102899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55896216448887660326803865 41922162336665745245102899)
    ·
      refine ⟨62883243504998617867654349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41922162336665745245102899 62883243504998617867654349)
      ·
        refine ⟨23581216314374481700370381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62883243504998617867654349 23581216314374481700370381)
        ·
          refine ⟨8842956117890430637638893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23581216314374481700370381 8842956117890430637638893)
          ·
            refine ⟨3316108544208911489114585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8842956117890430637638893 3316108544208911489114585)
            ·
              refine ⟨2487081408156683616835939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3316108544208911489114585 2487081408156683616835939)
              ·
                refine ⟨3730622112235025425253909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2487081408156683616835939 3730622112235025425253909)
                ·
                  refine ⟨174872911511016816808777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3730622112235025425253909 174872911511016816808777)
                  ·
                    rfl

theorem cell22_1532537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 6].length) (baseStart_1532537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532537 prefixEnd_1532537 := by exact prefixLift 1532537
  have htrace : WordTrace (prefixWord ++ tailWord_1532537) baseStart_1532537 baseEnd_1532537 := by
    simpa [prefixWord, tailWord_1532537, baseEnd_1532537] using wordTrace_append hprefix tailTrace_1532537
  have hstable : (prefixWord ++ tailWord_1532537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532537).length < 2 ^ (prefixWord ++ tailWord_1532537).sum := by decide
  have hdescent : baseEnd_1532537 < baseStart_1532537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532567 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1532567 : Nat := 118140960795 + 1532567 * 2 ^ 59
def prefixEnd_1532567 : Nat := 4983230072969 + 3 ^ 40 * 1532567 * 2
def baseEnd_1532567 : Nat := 524629004146140372176239

theorem tailTrace_1532567 : CollatzResearch.WordTrace tailWord_1532567 prefixEnd_1532567 524629004146140372176239 := by
  unfold tailWord_1532567
  simp only [CollatzResearch.WordTrace]
  refine ⟨55897310638778975450395955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37264873759185983633597303 55897310638778975450395955)
  ·
    refine ⟨83845965958168463175593933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55897310638778975450395955 83845965958168463175593933)
    ·
      refine ⟨31442237234313173690847725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83845965958168463175593933 31442237234313173690847725)
      ·
        refine ⟨11790838962867440134067897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31442237234313173690847725 11790838962867440134067897)
        ·
          refine ⟨8843129222150580100550923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11790838962867440134067897 8843129222150580100550923)
          ·
            refine ⟨13264693833225870150826385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8843129222150580100550923 13264693833225870150826385)
            ·
              refine ⟨9948520374919402613119789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13264693833225870150826385 9948520374919402613119789)
              ·
                refine ⟨3730695140594775979919921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9948520374919402613119789 3730695140594775979919921)
                ·
                  refine ⟨2798021355446081984939941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3730695140594775979919921 2798021355446081984939941)
                  ·
                    refine ⟨524629004146140372176239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798021355446081984939941 524629004146140372176239)
                    ·
                      rfl

theorem cell22_1532567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1532567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532567 prefixEnd_1532567 := by exact prefixLift 1532567
  have htrace : WordTrace (prefixWord ++ tailWord_1532567) baseStart_1532567 baseEnd_1532567 := by
    simpa [prefixWord, tailWord_1532567, baseEnd_1532567] using wordTrace_append hprefix tailTrace_1532567
  have hstable : (prefixWord ++ tailWord_1532567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532567).length < 2 ^ (prefixWord ++ tailWord_1532567).sum := by decide
  have hdescent : baseEnd_1532567 < baseStart_1532567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532644 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_1532644 : Nat := 118140960795 + 1532644 * 2 ^ 59
def prefixEnd_1532644 : Nat := 4983230072969 + 3 ^ 40 * 1532644 * 2
def baseEnd_1532644 : Nat := 174885120939912612667001

theorem tailTrace_1532644 : CollatzResearch.WordTrace tailWord_1532644 prefixEnd_1532644 174885120939912612667001 := by
  unfold tailWord_1532644
  simp only [CollatzResearch.WordTrace]
  refine ⟨27950059529750008800474493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37266746039666678400632657 27950059529750008800474493)
  ·
    refine ⟨10481272323656253300177935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27950059529750008800474493 10481272323656253300177935)
    ·
      refine ⟨15721908485484379950266903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10481272323656253300177935 15721908485484379950266903)
      ·
        refine ⟨23582862728226569925400355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15721908485484379950266903 23582862728226569925400355)
        ·
          refine ⟨35374294092339854888100533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23582862728226569925400355 35374294092339854888100533)
          ·
            refine ⟨3316340071156861395759425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35374294092339854888100533 3316340071156861395759425)
            ·
              refine ⟨2487255053367646046819569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3316340071156861395759425 2487255053367646046819569)
              ·
                refine ⟨1865441290025734535114677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2487255053367646046819569 1865441290025734535114677)
                ·
                  refine ⟨174885120939912612667001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1865441290025734535114677 174885120939912612667001)
                  ·
                    rfl

theorem cell22_1532644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_1532644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532644 prefixEnd_1532644 := by exact prefixLift 1532644
  have htrace : WordTrace (prefixWord ++ tailWord_1532644) baseStart_1532644 baseEnd_1532644 := by
    simpa [prefixWord, tailWord_1532644, baseEnd_1532644] using wordTrace_append hprefix tailTrace_1532644
  have hstable : (prefixWord ++ tailWord_1532644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532644).length < 2 ^ (prefixWord ++ tailWord_1532644).sum := by decide
  have hdescent : baseEnd_1532644 < baseStart_1532644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532648 : List Nat := [2, 1, 4, 1, 4, 1, 1, 4, 1, 3]
def baseStart_1532648 : Nat := 118140960795 + 1532648 * 2 ^ 59
def prefixEnd_1532648 : Nat := 4983230072969 + 3 ^ 40 * 1532648 * 2
def baseEnd_1532648 : Nat := 524656732101483160900991

theorem tailTrace_1532648 : CollatzResearch.WordTrace tailWord_1532648 prefixEnd_1532648 524656732101483160900991 := by
  unfold tailWord_1532648
  simp only [CollatzResearch.WordTrace]
  refine ⟨27950132475742763142047299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37266843300990350856063065 27950132475742763142047299)
  ·
    refine ⟨41925198713614144713070949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27950132475742763142047299 41925198713614144713070949)
    ·
      refine ⟨7860974758802652133700803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41925198713614144713070949 7860974758802652133700803)
      ·
        refine ⟨11791462138203978200551205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860974758802652133700803 11791462138203978200551205)
        ·
          refine ⟨2210899150913245912603351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11791462138203978200551205 2210899150913245912603351)
          ·
            refine ⟨3316348726369868868905027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2210899150913245912603351 3316348726369868868905027)
            ·
              refine ⟨4974523089554803303357541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3316348726369868868905027 4974523089554803303357541)
              ·
                refine ⟨932723079291525619379539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4974523089554803303357541 932723079291525619379539)
                ·
                  refine ⟨1399084618937288429069309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932723079291525619379539 1399084618937288429069309)
                  ·
                    refine ⟨524656732101483160900991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1399084618937288429069309 524656732101483160900991)
                    ·
                      rfl

theorem cell22_1532648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_1532648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532648 prefixEnd_1532648 := by exact prefixLift 1532648
  have htrace : WordTrace (prefixWord ++ tailWord_1532648) baseStart_1532648 baseEnd_1532648 := by
    simpa [prefixWord, tailWord_1532648, baseEnd_1532648] using wordTrace_append hprefix tailTrace_1532648
  have hstable : (prefixWord ++ tailWord_1532648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532648).length < 2 ^ (prefixWord ++ tailWord_1532648).sum := by decide
  have hdescent : baseEnd_1532648 < baseStart_1532648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532657 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 5, 4]
def baseStart_1532657 : Nat := 118140960795 + 1532657 * 2 ^ 59
def prefixEnd_1532657 : Nat := 4983230072969 + 3 ^ 40 * 1532657 * 2
def baseEnd_1532657 : Nat := 524659812985410137425963

theorem tailTrace_1532657 : CollatzResearch.WordTrace tailWord_1532657 prefixEnd_1532657 524659812985410137425963 := by
  unfold tailWord_1532657
  simp only [CollatzResearch.WordTrace]
  refine ⟨55900593208452920821172225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37267062138968613880781483 55900593208452920821172225)
  ·
    refine ⟨41925444906339690615879169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55900593208452920821172225 41925444906339690615879169)
    ·
      refine ⟨31444083679754767961909377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41925444906339690615879169 31444083679754767961909377)
      ·
        refine ⟨23583062759816075971432033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31444083679754767961909377 23583062759816075971432033)
        ·
          refine ⟨17687297069862056978574025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23583062759816075971432033 17687297069862056978574025)
          ·
            refine ⟨13265472802396542733930519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17687297069862056978574025 13265472802396542733930519)
            ·
              refine ⟨19898209203594814100895779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13265472802396542733930519 19898209203594814100895779)
              ·
                refine ⟨29847313805392221151343669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19898209203594814100895779 29847313805392221151343669)
                ·
                  refine ⟨2798185669255520732938469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29847313805392221151343669 2798185669255520732938469)
                  ·
                    refine ⟨524659812985410137425963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2798185669255520732938469 524659812985410137425963)
                    ·
                      rfl

theorem cell22_1532657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 5, 4].length) (baseStart_1532657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532657 prefixEnd_1532657 := by exact prefixLift 1532657
  have htrace : WordTrace (prefixWord ++ tailWord_1532657) baseStart_1532657 baseEnd_1532657 := by
    simpa [prefixWord, tailWord_1532657, baseEnd_1532657] using wordTrace_append hprefix tailTrace_1532657
  have hstable : (prefixWord ++ tailWord_1532657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532657).length < 2 ^ (prefixWord ++ tailWord_1532657).sum := by decide
  have hdescent : baseEnd_1532657 < baseStart_1532657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532687 : List Nat := [1, 1, 2, 1, 1, 1, 5, 4, 1, 5]
def baseStart_1532687 : Nat := 118140960795 + 1532687 * 2 ^ 59
def prefixEnd_1532687 : Nat := 4983230072969 + 3 ^ 40 * 1532687 * 2
def baseEnd_1532687 : Nat := 524670082598500059175871

theorem tailTrace_1532687 : CollatzResearch.WordTrace tailWord_1532687 prefixEnd_1532687 524670082598500059175871 := by
  unfold tailWord_1532687
  simp only [CollatzResearch.WordTrace]
  refine ⟨55901687398344235944764315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37267791598896157296509543 55901687398344235944764315)
  ·
    refine ⟨83852531097516353917146473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55901687398344235944764315 83852531097516353917146473)
    ·
      refine ⟨62889398323137265437859855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83852531097516353917146473 62889398323137265437859855)
      ·
        refine ⟨94334097484705898156789783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62889398323137265437859855 94334097484705898156789783)
        ·
          refine ⟨141501146227058847235184675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94334097484705898156789783 141501146227058847235184675)
          ·
            refine ⟨212251719340588270852777013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141501146227058847235184675 212251719340588270852777013)
            ·
              refine ⟨19898598688180150392447845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212251719340588270852777013 19898598688180150392447845)
              ·
                refine ⟨3730987254033778198583971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19898598688180150392447845 3730987254033778198583971)
                ·
                  refine ⟨5596480881050667297875957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3730987254033778198583971 5596480881050667297875957)
                  ·
                    refine ⟨524670082598500059175871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5596480881050667297875957 524670082598500059175871)
                    ·
                      rfl

theorem cell22_1532687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_1532687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532687 prefixEnd_1532687 := by exact prefixLift 1532687
  have htrace : WordTrace (prefixWord ++ tailWord_1532687) baseStart_1532687 baseEnd_1532687 := by
    simpa [prefixWord, tailWord_1532687, baseEnd_1532687] using wordTrace_append hprefix tailTrace_1532687
  have hstable : (prefixWord ++ tailWord_1532687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532687).length < 2 ^ (prefixWord ++ tailWord_1532687).sum := by decide
  have hdescent : baseEnd_1532687 < baseStart_1532687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532689 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 4]
def baseStart_1532689 : Nat := 118140960795 + 1532689 * 2 ^ 59
def prefixEnd_1532689 : Nat := 4983230072969 + 3 ^ 40 * 1532689 * 2
def baseEnd_1532689 : Nat := 174890255746457573541955

theorem tailTrace_1532689 : CollatzResearch.WordTrace tailWord_1532689 prefixEnd_1532689 174890255746457573541955 := by
  unfold tailWord_1532689
  simp only [CollatzResearch.WordTrace]
  refine ⟨55901760344336990286337121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37267840229557993524224747 55901760344336990286337121)
  ·
    refine ⟨41926320258252742714752841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55901760344336990286337121 41926320258252742714752841)
    ·
      refine ⟨31444740193689557036064631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41926320258252742714752841 31444740193689557036064631)
      ·
        refine ⟨47167110290534335554096947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31444740193689557036064631 47167110290534335554096947)
        ·
          refine ⟨70750665435801503331145421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47167110290534335554096947 70750665435801503331145421)
          ·
            refine ⟨26531499538425563749179533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70750665435801503331145421 26531499538425563749179533)
            ·
              refine ⟨9949312326909586405942325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26531499538425563749179533 9949312326909586405942325)
              ·
                refine ⟨932748030647773725557093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9949312326909586405942325 932748030647773725557093)
                ·
                  refine ⟨174890255746457573541955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932748030647773725557093 174890255746457573541955)
                  ·
                    rfl

theorem cell22_1532689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 4].length) (baseStart_1532689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532689 prefixEnd_1532689 := by exact prefixLift 1532689
  have htrace : WordTrace (prefixWord ++ tailWord_1532689) baseStart_1532689 baseEnd_1532689 := by
    simpa [prefixWord, tailWord_1532689, baseEnd_1532689] using wordTrace_append hprefix tailTrace_1532689
  have hstable : (prefixWord ++ tailWord_1532689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532689).length < 2 ^ (prefixWord ++ tailWord_1532689).sum := by decide
  have hdescent : baseEnd_1532689 < baseStart_1532689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532706 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 4]
def baseStart_1532706 : Nat := 118140960795 + 1532706 * 2 ^ 59
def prefixEnd_1532706 : Nat := 4983230072969 + 3 ^ 40 * 1532706 * 2
def baseEnd_1532706 : Nat := 174892195562263447650271

theorem tailTrace_1532706 : CollatzResearch.WordTrace tailWord_1532706 prefixEnd_1532706 174892195562263447650271 := by
  unfold tailWord_1532706
  simp only [CollatzResearch.WordTrace]
  refine ⟨13975595096318850547426493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37268253590183601459803981 13975595096318850547426493)
  ·
    refine ⟨5240848161119568955284935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13975595096318850547426493 5240848161119568955284935)
    ·
      refine ⟨7861272241679353432927403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5240848161119568955284935 7861272241679353432927403)
      ·
        refine ⟨11791908362519030149391105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7861272241679353432927403 11791908362519030149391105)
        ·
          refine ⟨8843931271889272612043329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791908362519030149391105 8843931271889272612043329)
          ·
            refine ⟨6632948453916954459032497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8843931271889272612043329 6632948453916954459032497)
            ·
              refine ⟨4974711340437715844274373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6632948453916954459032497 4974711340437715844274373)
              ·
                refine ⟨932758376332071720801445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4974711340437715844274373 932758376332071720801445)
                ·
                  refine ⟨174892195562263447650271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 932758376332071720801445 174892195562263447650271)
                  ·
                    rfl

theorem cell22_1532706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 4].length) (baseStart_1532706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532706 prefixEnd_1532706 := by exact prefixLift 1532706
  have htrace : WordTrace (prefixWord ++ tailWord_1532706) baseStart_1532706 baseEnd_1532706 := by
    simpa [prefixWord, tailWord_1532706, baseEnd_1532706] using wordTrace_append hprefix tailTrace_1532706
  have hstable : (prefixWord ++ tailWord_1532706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532706).length < 2 ^ (prefixWord ++ tailWord_1532706).sum := by decide
  have hdescent : baseEnd_1532706 < baseStart_1532706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532732 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1532732 : Nat := 118140960795 + 1532732 * 2 ^ 59
def prefixEnd_1532732 : Nat := 4983230072969 + 3 ^ 40 * 1532732 * 2
def baseEnd_1532732 : Nat := 524685487018134941800733

theorem tailTrace_1532732 : CollatzResearch.WordTrace tailWord_1532732 prefixEnd_1532732 524685487018134941800733 := by
  unfold tailWord_1532732
  simp only [CollatzResearch.WordTrace]
  refine ⟨27951664341590604315076225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37268885788787472420101633 27951664341590604315076225)
  ·
    refine ⟨20963748256192953236307169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27951664341590604315076225 20963748256192953236307169)
    ·
      refine ⟨15722811192144714927230377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20963748256192953236307169 15722811192144714927230377)
      ·
        refine ⟨11792108394108536195422783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15722811192144714927230377 11792108394108536195422783)
        ·
          refine ⟨17688162591162804293134175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11792108394108536195422783 17688162591162804293134175)
          ·
            refine ⟨26532243886744206439701263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17688162591162804293134175 26532243886744206439701263)
            ·
              refine ⟨39798365830116309659551895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26532243886744206439701263 39798365830116309659551895)
              ·
                refine ⟨59697548745174464489327843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39798365830116309659551895 59697548745174464489327843)
                ·
                  refine ⟨89546323117761696733991765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59697548745174464489327843 89546323117761696733991765)
                  ·
                    refine ⟨524685487018134941800733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 89546323117761696733991765 524685487018134941800733)
                    ·
                      rfl

theorem cell22_1532732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1532732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532732 prefixEnd_1532732 := by exact prefixLift 1532732
  have htrace : WordTrace (prefixWord ++ tailWord_1532732) baseStart_1532732 baseEnd_1532732 := by
    simpa [prefixWord, tailWord_1532732, baseEnd_1532732] using wordTrace_append hprefix tailTrace_1532732
  have hstable : (prefixWord ++ tailWord_1532732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532732).length < 2 ^ (prefixWord ++ tailWord_1532732).sum := by decide
  have hdescent : baseEnd_1532732 < baseStart_1532732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532890 : List Nat := [3, 1, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_1532890 : Nat := 118140960795 + 1532890 * 2 ^ 59
def prefixEnd_1532890 : Nat := 4983230072969 + 3 ^ 40 * 1532890 * 2
def baseEnd_1532890 : Nat := 524739573647075196350249

theorem tailTrace_1532890 : CollatzResearch.WordTrace tailWord_1532890 prefixEnd_1532890 524739573647075196350249 := by
  unfold tailWord_1532890
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977272854152200403601031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37272727611072534409602749 13977272854152200403601031)
  ·
    refine ⟨20965909281228300605401547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13977272854152200403601031 20965909281228300605401547)
    ·
      refine ⟨31448863921842450908102321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20965909281228300605401547 31448863921842450908102321)
      ·
        refine ⟨23586647941381838181076741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31448863921842450908102321 23586647941381838181076741)
        ·
          refine ⟨4422496489009094658951889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23586647941381838181076741 4422496489009094658951889)
          ·
            refine ⟨3316872366756820994213917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4422496489009094658951889 3316872366756820994213917)
            ·
              refine ⟨1243827137533807872830219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3316872366756820994213917 1243827137533807872830219)
              ·
                refine ⟨1865740706300711809245329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1243827137533807872830219 1865740706300711809245329)
                ·
                  refine ⟨1399305529725533856933997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1865740706300711809245329 1399305529725533856933997)
                  ·
                    refine ⟨524739573647075196350249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1399305529725533856933997 524739573647075196350249)
                    ·
                      rfl

theorem cell22_1532890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_1532890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532890 prefixEnd_1532890 := by exact prefixLift 1532890
  have htrace : WordTrace (prefixWord ++ tailWord_1532890) baseStart_1532890 baseEnd_1532890 := by
    simpa [prefixWord, tailWord_1532890, baseEnd_1532890] using wordTrace_append hprefix tailTrace_1532890
  have hstable : (prefixWord ++ tailWord_1532890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532890).length < 2 ^ (prefixWord ++ tailWord_1532890).sum := by decide
  have hdescent : baseEnd_1532890 < baseStart_1532890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1532903 : List Nat := [1, 1, 5, 2, 2, 3, 2, 6]
def baseStart_1532903 : Nat := 118140960795 + 1532903 * 2 ^ 59
def prefixEnd_1532903 : Nat := 4983230072969 + 3 ^ 40 * 1532903 * 2
def baseEnd_1532903 : Nat := 58304891534749721752801

theorem tailTrace_1532903 : CollatzResearch.WordTrace tailWord_1532903 prefixEnd_1532903 58304891534749721752801 := by
  unfold tailWord_1532903
  simp only [CollatzResearch.WordTrace]
  refine ⟨55909565565561704834627363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37273043710374469889751575 55909565565561704834627363)
  ·
    refine ⟨83864348348342557251941045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55909565565561704834627363 83864348348342557251941045)
    ·
      refine ⟨7862282657657114742369473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83864348348342557251941045 7862282657657114742369473)
      ·
        refine ⟨5896711993242836056777105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7862282657657114742369473 5896711993242836056777105)
        ·
          refine ⟨4422533994932127042582829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5896711993242836056777105 4422533994932127042582829)
          ·
            refine ⟨1658450248099547640968561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4422533994932127042582829 1658450248099547640968561)
            ·
              refine ⟨1243837686074660730726421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1658450248099547640968561 1243837686074660730726421)
              ·
                refine ⟨58304891534749721752801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1243837686074660730726421 58304891534749721752801)
                ·
                  rfl

theorem cell22_1532903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 6].length) (baseStart_1532903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1532903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1532903 prefixEnd_1532903 := by exact prefixLift 1532903
  have htrace : WordTrace (prefixWord ++ tailWord_1532903) baseStart_1532903 baseEnd_1532903 := by
    simpa [prefixWord, tailWord_1532903, baseEnd_1532903] using wordTrace_append hprefix tailTrace_1532903
  have hstable : (prefixWord ++ tailWord_1532903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1532903).length < 2 ^ (prefixWord ++ tailWord_1532903).sum := by decide
  have hdescent : baseEnd_1532903 < baseStart_1532903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1532903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533006 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1533006 : Nat := 118140960795 + 1533006 * 2 ^ 59
def prefixEnd_1533006 : Nat := 4983230072969 + 3 ^ 40 * 1533006 * 2
def baseEnd_1533006 : Nat := 524779282817689560449893

theorem tailTrace_1533006 : CollatzResearch.WordTrace tailWord_1533006 prefixEnd_1533006 524779282817689560449893 := by
  unfold tailWord_1533006
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989165285523569178203359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37275548189459035617084581 6989165285523569178203359)
  ·
    refine ⟨10483747928285353767305039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6989165285523569178203359 10483747928285353767305039)
    ·
      refine ⟨15725621892428030650957559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10483747928285353767305039 15725621892428030650957559)
      ·
        refine ⟨23588432838642045976436339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15725621892428030650957559 23588432838642045976436339)
        ·
          refine ⟨35382649257963068964654509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23588432838642045976436339 35382649257963068964654509)
          ·
            refine ⟨13268493471736150861745441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35382649257963068964654509 13268493471736150861745441)
            ·
              refine ⟨9951370103802113146309081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13268493471736150861745441 9951370103802113146309081)
              ·
                refine ⟨7463527577851584859731811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9951370103802113146309081 7463527577851584859731811)
                ·
                  refine ⟨11195291366777377289597717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7463527577851584859731811 11195291366777377289597717)
                  ·
                    refine ⟨524779282817689560449893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11195291366777377289597717 524779282817689560449893)
                    ·
                      rfl

theorem cell22_1533006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1533006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533006 prefixEnd_1533006 := by exact prefixLift 1533006
  have htrace : WordTrace (prefixWord ++ tailWord_1533006) baseStart_1533006 baseEnd_1533006 := by
    simpa [prefixWord, tailWord_1533006, baseEnd_1533006] using wordTrace_append hprefix tailTrace_1533006
  have hstable : (prefixWord ++ tailWord_1533006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533006).length < 2 ^ (prefixWord ++ tailWord_1533006).sum := by decide
  have hdescent : baseEnd_1533006 < baseStart_1533006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533070 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_1533070 : Nat := 118140960795 + 1533070 * 2 ^ 59
def prefixEnd_1533070 : Nat := 4983230072969 + 3 ^ 40 * 1533070 * 2
def baseEnd_1533070 : Nat := 524801191325614726849697

theorem tailTrace_1533070 : CollatzResearch.WordTrace tailWord_1533070 prefixEnd_1533070 524801191325614726849697 := by
  unfold tailWord_1533070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989457069494586544494583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37277104370637794903971109 6989457069494586544494583)
  ·
    refine ⟨10484185604241879816741875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6989457069494586544494583 10484185604241879816741875)
    ·
      refine ⟨15726278406362819725112813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10484185604241879816741875 15726278406362819725112813)
      ·
        refine ⟨5897354402386057396917305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15726278406362819725112813 5897354402386057396917305)
        ·
          refine ⟨4423015801789543047687979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5897354402386057396917305 4423015801789543047687979)
          ·
            refine ⟨6634523702684314571531969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423015801789543047687979 6634523702684314571531969)
            ·
              refine ⟨4975892777013235928648977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6634523702684314571531969 4975892777013235928648977)
              ·
                refine ⟨3731919582759926946486733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4975892777013235928648977 3731919582759926946486733)
                ·
                  refine ⟨1399469843534972604932525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3731919582759926946486733 1399469843534972604932525)
                  ·
                    refine ⟨524801191325614726849697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1399469843534972604932525 524801191325614726849697)
                    ·
                      rfl

theorem cell22_1533070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_1533070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533070 prefixEnd_1533070 := by exact prefixLift 1533070
  have htrace : WordTrace (prefixWord ++ tailWord_1533070) baseStart_1533070 baseEnd_1533070 := by
    simpa [prefixWord, tailWord_1533070, baseEnd_1533070] using wordTrace_append hprefix tailTrace_1533070
  have hstable : (prefixWord ++ tailWord_1533070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533070).length < 2 ^ (prefixWord ++ tailWord_1533070).sum := by decide
  have hdescent : baseEnd_1533070 < baseStart_1533070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533130 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1533130 : Nat := 118140960795 + 1533130 * 2 ^ 59
def prefixEnd_1533130 : Nat := 4983230072969 + 3 ^ 40 * 1533130 * 2
def baseEnd_1533130 : Nat := 524821730551794570349513

theorem tailTrace_1533130 : CollatzResearch.WordTrace tailWord_1533130 prefixEnd_1533130 524821730551794570349513 := by
  unfold tailWord_1533130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13979461233934830650785211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37278563290492881735427229 13979461233934830650785211)
  ·
    refine ⟨20969191850902245976177817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13979461233934830650785211 20969191850902245976177817)
    ·
      refine ⟨15726893888176684482133363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20969191850902245976177817 15726893888176684482133363)
      ·
        refine ⟨23590340832265026723200045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15726893888176684482133363 23590340832265026723200045)
        ·
          refine ⟨8846377812099385021200017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23590340832265026723200045 8846377812099385021200017)
          ·
            refine ⟨6634783359074538765900013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8846377812099385021200017 6634783359074538765900013)
            ·
              refine ⟨2488043759652952037212505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6634783359074538765900013 2488043759652952037212505)
              ·
                refine ⟨1866032819739714027909379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488043759652952037212505 1866032819739714027909379)
                ·
                  refine ⟨2799049229609571041864069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866032819739714027909379 2799049229609571041864069)
                  ·
                    refine ⟨524821730551794570349513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799049229609571041864069 524821730551794570349513)
                    ·
                      rfl

theorem cell22_1533130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1533130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533130 prefixEnd_1533130 := by exact prefixLift 1533130
  have htrace : WordTrace (prefixWord ++ tailWord_1533130) baseStart_1533130 baseEnd_1533130 := by
    simpa [prefixWord, tailWord_1533130, baseEnd_1533130] using wordTrace_append hprefix tailTrace_1533130
  have hstable : (prefixWord ++ tailWord_1533130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533130).length < 2 ^ (prefixWord ++ tailWord_1533130).sum := by decide
  have hdescent : baseEnd_1533130 < baseStart_1533130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533143 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 6, 3]
def baseStart_1533143 : Nat := 118140960795 + 1533143 * 2 ^ 59
def prefixEnd_1533143 : Nat := 4983230072969 + 3 ^ 40 * 1533143 * 2
def baseEnd_1533143 : Nat := 524826180717466869774473

theorem tailTrace_1533143 : CollatzResearch.WordTrace tailWord_1533143 prefixEnd_1533143 524826180717466869774473 := by
  unfold tailWord_1533143
  simp only [CollatzResearch.WordTrace]
  refine ⟨55918319084692225823364083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37278879389794817215576055 55918319084692225823364083)
  ·
    refine ⟨83877478627038338735046125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55918319084692225823364083 83877478627038338735046125)
    ·
      refine ⟨31454054485139377025642297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83877478627038338735046125 31454054485139377025642297)
      ·
        refine ⟨23590540863854532769231723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31454054485139377025642297 23590540863854532769231723)
        ·
          refine ⟨35385811295781799153847585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23590540863854532769231723 35385811295781799153847585)
          ·
            refine ⟨26539358471836349365385689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35385811295781799153847585 26539358471836349365385689)
            ·
              refine ⟨19904518853877262024039267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26539358471836349365385689 19904518853877262024039267)
              ·
                refine ⟨29856778280815893036058901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19904518853877262024039267 29856778280815893036058901)
                ·
                  refine ⟨1399536481913244986065261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29856778280815893036058901 1399536481913244986065261)
                  ·
                    refine ⟨524826180717466869774473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1399536481913244986065261 524826180717466869774473)
                    ·
                      rfl

theorem cell22_1533143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_1533143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533143 prefixEnd_1533143 := by exact prefixLift 1533143
  have htrace : WordTrace (prefixWord ++ tailWord_1533143) baseStart_1533143 baseEnd_1533143 := by
    simpa [prefixWord, tailWord_1533143, baseEnd_1533143] using wordTrace_append hprefix tailTrace_1533143
  have hstable : (prefixWord ++ tailWord_1533143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533143).length < 2 ^ (prefixWord ++ tailWord_1533143).sum := by decide
  have hdescent : baseEnd_1533143 < baseStart_1533143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533162 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_1533162 : Nat := 118140960795 + 1533162 * 2 ^ 59
def prefixEnd_1533162 : Nat := 4983230072969 + 3 ^ 40 * 1533162 * 2
def baseEnd_1533162 : Nat := 174944228268585717849805

theorem tailTrace_1533162 : CollatzResearch.WordTrace tailWord_1533162 prefixEnd_1533162 174944228268585717849805 := by
  unfold tailWord_1533162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13979753017905848017076435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37279341381082261378870493 13979753017905848017076435)
  ·
    refine ⟨20969629526858772025614653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13979753017905848017076435 20969629526858772025614653)
    ·
      refine ⟨7863611072572039509605495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20969629526858772025614653 7863611072572039509605495)
      ·
        refine ⟨11795416608858059264408243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7863611072572039509605495 11795416608858059264408243)
        ·
          refine ⟨17693124913287088896612365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11795416608858059264408243 17693124913287088896612365)
          ·
            refine ⟨6634921842482658336229637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17693124913287088896612365 6634921842482658336229637)
            ·
              refine ⟨1244047845465498438043057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6634921842482658336229637 1244047845465498438043057)
              ·
                refine ⟨933035884099123828532293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244047845465498438043057 933035884099123828532293)
                ·
                  refine ⟨174944228268585717849805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933035884099123828532293 174944228268585717849805)
                  ·
                    rfl

theorem cell22_1533162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_1533162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533162 prefixEnd_1533162 := by exact prefixLift 1533162
  have htrace : WordTrace (prefixWord ++ tailWord_1533162) baseStart_1533162 baseEnd_1533162 := by
    simpa [prefixWord, tailWord_1533162, baseEnd_1533162] using wordTrace_append hprefix tailTrace_1533162
  have hstable : (prefixWord ++ tailWord_1533162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533162).length < 2 ^ (prefixWord ++ tailWord_1533162).sum := by decide
  have hdescent : baseEnd_1533162 < baseStart_1533162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533192 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 2, 4]
def baseStart_1533192 : Nat := 118140960795 + 1533192 * 2 ^ 59
def prefixEnd_1533192 : Nat := 4983230072969 + 3 ^ 40 * 1533192 * 2
def baseEnd_1533192 : Nat := 524842954418847075299323

theorem tailTrace_1533192 : CollatzResearch.WordTrace tailWord_1533192 prefixEnd_1533192 524842954418847075299323 := by
  unfold tailWord_1533192
  simp only [CollatzResearch.WordTrace]
  refine ⟨27960053130757353595948915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37280070841009804794598553 27960053130757353595948915)
  ·
    refine ⟨41940079696136030393923373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27960053130757353595948915 41940079696136030393923373)
    ·
      refine ⟨15727529886051011397721265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41940079696136030393923373 15727529886051011397721265)
      ·
        refine ⟨11795647414538258548290949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15727529886051011397721265 11795647414538258548290949)
        ·
          refine ⟨2211683890225923477804553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11795647414538258548290949 2211683890225923477804553)
          ·
            refine ⟨1658762917669442608353415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2211683890225923477804553 1658762917669442608353415)
            ·
              refine ⟨2488144376504163912530123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658762917669442608353415 2488144376504163912530123)
              ·
                refine ⟨3732216564756245868795185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2488144376504163912530123 3732216564756245868795185)
                ·
                  refine ⟨2799162423567184401596389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3732216564756245868795185 2799162423567184401596389)
                  ·
                    refine ⟨524842954418847075299323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799162423567184401596389 524842954418847075299323)
                    ·
                      rfl

theorem cell22_1533192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_1533192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533192 prefixEnd_1533192 := by exact prefixLift 1533192
  have htrace : WordTrace (prefixWord ++ tailWord_1533192) baseStart_1533192 baseEnd_1533192 := by
    simpa [prefixWord, tailWord_1533192, baseEnd_1533192] using wordTrace_append hprefix tailTrace_1533192
  have hstable : (prefixWord ++ tailWord_1533192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533192).length < 2 ^ (prefixWord ++ tailWord_1533192).sum := by decide
  have hdescent : baseEnd_1533192 < baseStart_1533192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533265 : List Nat := [1, 2, 2, 1, 4, 1, 1, 5, 1, 4]
def baseStart_1533265 : Nat := 118140960795 + 1533265 * 2 ^ 59
def prefixEnd_1533265 : Nat := 4983230072969 + 3 ^ 40 * 1533265 * 2
def baseEnd_1533265 : Nat := 524867943810699218224099

theorem tailTrace_1533265 : CollatzResearch.WordTrace tailWord_1533265 prefixEnd_1533265 524867943810699218224099 := by
  unfold tailWord_1533265
  simp only [CollatzResearch.WordTrace]
  refine ⟨55922768790250240659305249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37281845860166827106203499 55922768790250240659305249)
  ·
    refine ⟨41942076592687680494478937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55922768790250240659305249 41942076592687680494478937)
    ·
      refine ⟨31456557444515760370859203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41942076592687680494478937 31456557444515760370859203)
      ·
        refine ⟨47184836166773640556288805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31456557444515760370859203 47184836166773640556288805)
        ·
          refine ⟨8847156781270057604304151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47184836166773640556288805 8847156781270057604304151)
          ·
            refine ⟨13270735171905086406456227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8847156781270057604304151 13270735171905086406456227)
            ·
              refine ⟨19906102757857629609684341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13270735171905086406456227 19906102757857629609684341)
              ·
                refine ⟨1866197133549152775907907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19906102757857629609684341 1866197133549152775907907)
                ·
                  refine ⟨2799295700323729163861861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866197133549152775907907 2799295700323729163861861)
                  ·
                    refine ⟨524867943810699218224099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799295700323729163861861 524867943810699218224099)
                    ·
                      rfl

theorem cell22_1533265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 5, 1, 4].length) (baseStart_1533265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533265 prefixEnd_1533265 := by exact prefixLift 1533265
  have htrace : WordTrace (prefixWord ++ tailWord_1533265) baseStart_1533265 baseEnd_1533265 := by
    simpa [prefixWord, tailWord_1533265, baseEnd_1533265] using wordTrace_append hprefix tailTrace_1533265
  have hstable : (prefixWord ++ tailWord_1533265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533265).length < 2 ^ (prefixWord ++ tailWord_1533265).sum := by decide
  have hdescent : baseEnd_1533265 < baseStart_1533265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533280 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_1533280 : Nat := 118140960795 + 1533280 * 2 ^ 59
def prefixEnd_1533280 : Nat := 4983230072969 + 3 ^ 40 * 1533280 * 2
def baseEnd_1533280 : Nat := 174957692872414726366351

theorem tailTrace_1533280 : CollatzResearch.WordTrace tailWord_1533280 prefixEnd_1533280 174957692872414726366351 := by
  unfold tailWord_1533280
  simp only [CollatzResearch.WordTrace]
  refine ⟨27961657942597949110550647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37282210590130598814067529 27961657942597949110550647)
  ·
    refine ⟨41942486913896923665825971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27961657942597949110550647 41942486913896923665825971)
    ·
      refine ⟨62913730370845385498738957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41942486913896923665825971 62913730370845385498738957)
      ·
        refine ⟨23592648889067019562027109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62913730370845385498738957 23592648889067019562027109)
        ·
          refine ⟨4423621666700066167880083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23592648889067019562027109 4423621666700066167880083)
          ·
            refine ⟨6635432500050099251820125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4423621666700066167880083 6635432500050099251820125)
            ·
              refine ⟨2488287187518787219432547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6635432500050099251820125 2488287187518787219432547)
              ·
                refine ⟨3732430781278180829148821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2488287187518787219432547 3732430781278180829148821)
                ·
                  refine ⟨174957692872414726366351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3732430781278180829148821 174957692872414726366351)
                  ·
                    rfl

theorem cell22_1533280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_1533280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533280 prefixEnd_1533280 := by exact prefixLift 1533280
  have htrace : WordTrace (prefixWord ++ tailWord_1533280) baseStart_1533280 baseEnd_1533280 := by
    simpa [prefixWord, tailWord_1533280, baseEnd_1533280] using wordTrace_append hprefix tailTrace_1533280
  have hstable : (prefixWord ++ tailWord_1533280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533280).length < 2 ^ (prefixWord ++ tailWord_1533280).sum := by decide
  have hdescent : baseEnd_1533280 < baseStart_1533280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533308 : List Nat := [2, 2, 2, 1, 1, 1, 3, 10]
def baseStart_1533308 : Nat := 118140960795 + 1533308 * 2 ^ 59
def prefixEnd_1533308 : Nat := 4983230072969 + 3 ^ 40 * 1533308 * 2
def baseEnd_1533308 : Nat := 58320295954384604377663

theorem tailTrace_1533308 : CollatzResearch.WordTrace tailWord_1533308 prefixEnd_1533308 58320295954384604377663 := by
  unfold tailWord_1533308
  simp only [CollatzResearch.WordTrace]
  refine ⟨27962168564547229501560289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37282891419396306002080385 27962168564547229501560289)
  ·
    refine ⟨20971626423410422126170217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27962168564547229501560289 20971626423410422126170217)
    ·
      refine ⟨15728719817557816594627663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20971626423410422126170217 15728719817557816594627663)
      ·
        refine ⟨23593079726336724891941495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15728719817557816594627663 23593079726336724891941495)
        ·
          refine ⟨35389619589505087337912243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23593079726336724891941495 35389619589505087337912243)
          ·
            refine ⟨53084429384257631006868365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35389619589505087337912243 53084429384257631006868365)
            ·
              refine ⟨19906661019096611627575637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53084429384257631006868365 19906661019096611627575637)
              ·
                refine ⟨58320295954384604377663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19906661019096611627575637 58320295954384604377663)
                ·
                  rfl

theorem cell22_1533308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 10].length) (baseStart_1533308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533308 prefixEnd_1533308 := by exact prefixLift 1533308
  have htrace : WordTrace (prefixWord ++ tailWord_1533308) baseStart_1533308 baseEnd_1533308 := by
    simpa [prefixWord, tailWord_1533308, baseEnd_1533308] using wordTrace_append hprefix tailTrace_1533308
  have hstable : (prefixWord ++ tailWord_1533308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533308).length < 2 ^ (prefixWord ++ tailWord_1533308).sum := by decide
  have hdescent : baseEnd_1533308 < baseStart_1533308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533353 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 11]
def baseStart_1533353 : Nat := 118140960795 + 1533353 * 2 ^ 59
def prefixEnd_1533353 : Nat := 4983230072969 + 3 ^ 40 * 1533353 * 2
def baseEnd_1533353 : Nat := 174966022669698774007943

theorem tailTrace_1533353 : CollatzResearch.WordTrace tailWord_1533353 prefixEnd_1533353 174966022669698774007943 := by
  unfold tailWord_1533353
  simp only [CollatzResearch.WordTrace]
  refine ⟨55925978413931431688508713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37283985609287621125672475 55925978413931431688508713)
  ·
    refine ⟨41944483810448573766381535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55925978413931431688508713 41944483810448573766381535)
    ·
      refine ⟨62916725715672860649572303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41944483810448573766381535 62916725715672860649572303)
      ·
        refine ⟨94375088573509290974358455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62916725715672860649572303 94375088573509290974358455)
        ·
          refine ⟨141562632860263936461537683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94375088573509290974358455 141562632860263936461537683)
          ·
            refine ⟨212343949290395904692306525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141562632860263936461537683 212343949290395904692306525)
            ·
              refine ⟨79628980983898464259614947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212343949290395904692306525 79628980983898464259614947)
              ·
                refine ⟨119443471475847696389422421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79628980983898464259614947 119443471475847696389422421)
                ·
                  refine ⟨174966022669698774007943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 119443471475847696389422421 174966022669698774007943)
                  ·
                    rfl

theorem cell22_1533353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 11].length) (baseStart_1533353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533353 prefixEnd_1533353 := by exact prefixLift 1533353
  have htrace : WordTrace (prefixWord ++ tailWord_1533353) baseStart_1533353 baseEnd_1533353 := by
    simpa [prefixWord, tailWord_1533353, baseEnd_1533353] using wordTrace_append hprefix tailTrace_1533353
  have hstable : (prefixWord ++ tailWord_1533353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533353).length < 2 ^ (prefixWord ++ tailWord_1533353).sum := by decide
  have hdescent : baseEnd_1533353 < baseStart_1533353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533400 : List Nat := [2, 1, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_1533400 : Nat := 118140960795 + 1533400 * 2 ^ 59
def prefixEnd_1533400 : Nat := 4983230072969 + 3 ^ 40 * 1533400 * 2
def baseEnd_1533400 : Nat := 524914157069603866098685

theorem tailTrace_1533400 : CollatzResearch.WordTrace tailWord_1533400 prefixEnd_1533400 524914157069603866098685 := by
  unfold tailWord_1533400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27963846322380579357734827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37285128429840772476979769 27963846322380579357734827)
  ·
    refine ⟨41945769483570869036602241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27963846322380579357734827 41945769483570869036602241)
    ·
      refine ⟨31459327112678151777451681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41945769483570869036602241 31459327112678151777451681)
      ·
        refine ⟨23594495334508613833088761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31459327112678151777451681 23594495334508613833088761)
        ·
          refine ⟨17695871500881460374816571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23594495334508613833088761 17695871500881460374816571)
          ·
            refine ⟨26543807251322190562224857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17695871500881460374816571 26543807251322190562224857)
            ·
              refine ⟨19907855438491642921668643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26543807251322190562224857 19907855438491642921668643)
              ·
                refine ⟨29861783157737464382502965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19907855438491642921668643 29861783157737464382502965)
                ·
                  refine ⟨2799542171037887285859653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29861783157737464382502965 2799542171037887285859653)
                  ·
                    refine ⟨524914157069603866098685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2799542171037887285859653 524914157069603866098685)
                    ·
                      rfl

theorem cell22_1533400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_1533400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533400 prefixEnd_1533400 := by exact prefixLift 1533400
  have htrace : WordTrace (prefixWord ++ tailWord_1533400) baseStart_1533400 baseEnd_1533400 := by
    simpa [prefixWord, tailWord_1533400, baseEnd_1533400] using wordTrace_append hprefix tailTrace_1533400
  have hstable : (prefixWord ++ tailWord_1533400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533400).length < 2 ^ (prefixWord ++ tailWord_1533400).sum := by decide
  have hdescent : baseEnd_1533400 < baseStart_1533400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533449 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 4]
def baseStart_1533449 : Nat := 118140960795 + 1533449 * 2 ^ 59
def prefixEnd_1533449 : Nat := 4983230072969 + 3 ^ 40 * 1533449 * 2
def baseEnd_1533449 : Nat := 174976976923661357207845

theorem tailTrace_1533449 : CollatzResearch.WordTrace tailWord_1533449 prefixEnd_1533449 174976976923661357207845 := by
  unfold tailWord_1533449
  simp only [CollatzResearch.WordTrace]
  refine ⟨55929479821583640084003401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37286319881055760056002267 55929479821583640084003401)
  ·
    refine ⟨41947109866187730063002551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55929479821583640084003401 41947109866187730063002551)
    ·
      refine ⟨62920664799281595094503827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41947109866187730063002551 62920664799281595094503827)
      ·
        refine ⟨94380997198922392641755741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62920664799281595094503827 94380997198922392641755741)
        ·
          refine ⟨35392873949595897240658403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94380997198922392641755741 35392873949595897240658403)
          ·
            refine ⟨53089310924393845860987605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35392873949595897240658403 53089310924393845860987605)
            ·
              refine ⟨1244280724790480762366897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53089310924393845860987605 1244280724790480762366897)
              ·
                refine ⟨933210543592860571775173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244280724790480762366897 933210543592860571775173)
                ·
                  refine ⟨174976976923661357207845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933210543592860571775173 174976976923661357207845)
                  ·
                    rfl

theorem cell22_1533449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 4].length) (baseStart_1533449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533449 prefixEnd_1533449 := by exact prefixLift 1533449
  have htrace : WordTrace (prefixWord ++ tailWord_1533449) baseStart_1533449 baseEnd_1533449 := by
    simpa [prefixWord, tailWord_1533449, baseEnd_1533449] using wordTrace_append hprefix tailTrace_1533449
  have hstable : (prefixWord ++ tailWord_1533449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533449).length < 2 ^ (prefixWord ++ tailWord_1533449).sum := by decide
  have hdescent : baseEnd_1533449 < baseStart_1533449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533494 : List Nat := [5, 1, 2, 1, 4, 9]
def baseStart_1533494 : Nat := 118140960795 + 1533494 * 2 ^ 59
def prefixEnd_1533494 : Nat := 4983230072969 + 3 ^ 40 * 1533494 * 2
def baseEnd_1533494 : Nat := 6480818952970604373437

theorem tailTrace_1533494 : CollatzResearch.WordTrace tailWord_1533494 prefixEnd_1533494 6480818952970604373437 := by
  unfold tailWord_1533494
  simp only [CollatzResearch.WordTrace]
  refine ⟨3495695069151288298086971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37287414070947075179594357 3495695069151288298086971)
  ·
    refine ⟨5243542603726932447130457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3495695069151288298086971 5243542603726932447130457)
    ·
      refine ⟨3932656952795199335347843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5243542603726932447130457 3932656952795199335347843)
      ·
        refine ⟨5898985429192799003021765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3932656952795199335347843 5898985429192799003021765)
        ·
          refine ⟨1106059767973649813066581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5898985429192799003021765 1106059767973649813066581)
          ·
            refine ⟨6480818952970604373437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1106059767973649813066581 6480818952970604373437)
            ·
              rfl

theorem cell22_1533494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 9].length) (baseStart_1533494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533494 prefixEnd_1533494 := by exact prefixLift 1533494
  have htrace : WordTrace (prefixWord ++ tailWord_1533494) baseStart_1533494 baseEnd_1533494 := by
    simpa [prefixWord, tailWord_1533494, baseEnd_1533494] using wordTrace_append hprefix tailTrace_1533494
  have hstable : (prefixWord ++ tailWord_1533494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533494).length < 2 ^ (prefixWord ++ tailWord_1533494).sum := by decide
  have hdescent : baseEnd_1533494 < baseStart_1533494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533601 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 4]
def baseStart_1533601 : Nat := 118140960795 + 1533601 * 2 ^ 59
def prefixEnd_1533601 : Nat := 4983230072969 + 3 ^ 40 * 1533601 * 2
def baseEnd_1533601 : Nat := 174994321159102113941023

theorem tailTrace_1533601 : CollatzResearch.WordTrace tailWord_1533601 prefixEnd_1533601 174994321159102113941023 := by
  unfold tailWord_1533601
  simp only [CollatzResearch.WordTrace]
  refine ⟨55935023717032970043536657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37290015811355313362357771 55935023717032970043536657)
  ·
    refine ⟨41951267787774727532652493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55935023717032970043536657 41951267787774727532652493)
    ·
      refine ⟨15731725420415522824744685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41951267787774727532652493 15731725420415522824744685)
      ·
        refine ⟨5899397032655821059279257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15731725420415522824744685 5899397032655821059279257)
        ·
          refine ⟨4424547774491865794459443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5899397032655821059279257 4424547774491865794459443)
          ·
            refine ⟨6636821661737798691689165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4424547774491865794459443 6636821661737798691689165)
            ·
              refine ⟨2488808123151674509383437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6636821661737798691689165 2488808123151674509383437)
              ·
                refine ⟨933303046181877941018789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2488808123151674509383437 933303046181877941018789)
                ·
                  refine ⟨174994321159102113941023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933303046181877941018789 174994321159102113941023)
                  ·
                    rfl

theorem cell22_1533601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 4].length) (baseStart_1533601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533601 prefixEnd_1533601 := by exact prefixLift 1533601
  have htrace : WordTrace (prefixWord ++ tailWord_1533601) baseStart_1533601 baseEnd_1533601 := by
    simpa [prefixWord, tailWord_1533601, baseEnd_1533601] using wordTrace_append hprefix tailTrace_1533601
  have hstable : (prefixWord ++ tailWord_1533601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533601).length < 2 ^ (prefixWord ++ tailWord_1533601).sum := by decide
  have hdescent : baseEnd_1533601 < baseStart_1533601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533674 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 5]
def baseStart_1533674 : Nat := 118140960795 + 1533674 * 2 ^ 59
def prefixEnd_1533674 : Nat := 4983230072969 + 3 ^ 40 * 1533674 * 2
def baseEnd_1533674 : Nat := 175002650956386161582615

theorem tailTrace_1533674 : CollatzResearch.WordTrace tailWord_1533674 prefixEnd_1533674 175002650956386161582615 := by
  unfold tailWord_1533674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13984421561442125877736019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37291790830512335673962717 13984421561442125877736019)
  ·
    refine ⟨20976632342163188816604029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13984421561442125877736019 20976632342163188816604029)
    ·
      refine ⟨7866237128311195806226511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20976632342163188816604029 7866237128311195806226511)
      ·
        refine ⟨11799355692466793709339767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7866237128311195806226511 11799355692466793709339767)
        ·
          refine ⟨17699033538700190564009651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11799355692466793709339767 17699033538700190564009651)
          ·
            refine ⟨26548550308050285846014477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17699033538700190564009651 26548550308050285846014477)
            ·
              refine ⟨9955706365518857192255429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26548550308050285846014477 9955706365518857192255429)
              ·
                refine ⟨1866694943534785723547893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9955706365518857192255429 1866694943534785723547893)
                ·
                  refine ⟨175002650956386161582615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1866694943534785723547893 175002650956386161582615)
                  ·
                    rfl

theorem cell22_1533674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_1533674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533674 prefixEnd_1533674 := by exact prefixLift 1533674
  have htrace : WordTrace (prefixWord ++ tailWord_1533674) baseStart_1533674 baseEnd_1533674 := by
    simpa [prefixWord, tailWord_1533674, baseEnd_1533674] using wordTrace_append hprefix tailTrace_1533674
  have hstable : (prefixWord ++ tailWord_1533674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533674).length < 2 ^ (prefixWord ++ tailWord_1533674).sum := by decide
  have hdescent : baseEnd_1533674 < baseStart_1533674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533678 : List Nat := [4, 1, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1533678 : Nat := 118140960795 + 1533678 * 2 ^ 59
def prefixEnd_1533678 : Nat := 4983230072969 + 3 ^ 40 * 1533678 * 2
def baseEnd_1533678 : Nat := 525009322150903807647833

theorem tailTrace_1533678 : CollatzResearch.WordTrace tailWord_1533678 prefixEnd_1533678 525009322150903807647833 := by
  unfold tailWord_1533678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992229017219251524261211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37291888091836008129393125 6992229017219251524261211)
  ·
    refine ⟨10488343525828877286391817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6992229017219251524261211 10488343525828877286391817)
    ·
      refine ⟨7866257644371657964793863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10488343525828877286391817 7866257644371657964793863)
      ·
        refine ⟨11799386466557486947190795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7866257644371657964793863 11799386466557486947190795)
        ·
          refine ⟨17699079699836230420786193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11799386466557486947190795 17699079699836230420786193)
          ·
            refine ⟨13274309774877172815589645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17699079699836230420786193 13274309774877172815589645)
            ·
              refine ⟨4977866165578939805846117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13274309774877172815589645 4977866165578939805846117)
              ·
                refine ⟨933349906046051213596147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4977866165578939805846117 933349906046051213596147)
                ·
                  refine ⟨1400024859069076820394221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933349906046051213596147 1400024859069076820394221)
                  ·
                    refine ⟨525009322150903807647833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1400024859069076820394221 525009322150903807647833)
                    ·
                      rfl

theorem cell22_1533678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1533678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533678 prefixEnd_1533678 := by exact prefixLift 1533678
  have htrace : WordTrace (prefixWord ++ tailWord_1533678) baseStart_1533678 baseEnd_1533678 := by
    simpa [prefixWord, tailWord_1533678, baseEnd_1533678] using wordTrace_append hprefix tailTrace_1533678
  have hstable : (prefixWord ++ tailWord_1533678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533678).length < 2 ^ (prefixWord ++ tailWord_1533678).sum := by decide
  have hdescent : baseEnd_1533678 < baseStart_1533678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533704 : List Nat := [2, 1, 3, 2, 2, 1, 1, 3, 3, 4]
def baseStart_1533704 : Nat := 118140960795 + 1533704 * 2 ^ 59
def prefixEnd_1533704 : Nat := 4983230072969 + 3 ^ 40 * 1533704 * 2
def baseEnd_1533704 : Nat := 525018222482248406497753

theorem tailTrace_1533704 : CollatzResearch.WordTrace tailWord_1533704 prefixEnd_1533704 525018222482248406497753 := by
  unfold tailWord_1533704
  simp only [CollatzResearch.WordTrace]
  refine ⟨27969390217829909317268083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37292520290439879089690777 27969390217829909317268083)
  ·
    refine ⟨41954085326744863975902125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27969390217829909317268083 41954085326744863975902125)
    ·
      refine ⟨15732781997529323990963297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41954085326744863975902125 15732781997529323990963297)
      ·
        refine ⟨11799586498146992993222473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15732781997529323990963297 11799586498146992993222473)
        ·
          refine ⟨8849689873610244744916855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11799586498146992993222473 8849689873610244744916855)
          ·
            refine ⟨13274534810415367117375283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8849689873610244744916855 13274534810415367117375283)
            ·
              refine ⟨19911802215623050676062925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13274534810415367117375283 19911802215623050676062925)
              ·
                refine ⟨7466925830858644003523597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19911802215623050676062925 7466925830858644003523597)
                ·
                  refine ⟨2800097186571991501321349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7466925830858644003523597 2800097186571991501321349)
                  ·
                    refine ⟨525018222482248406497753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800097186571991501321349 525018222482248406497753)
                    ·
                      rfl

theorem cell22_1533704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_1533704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533704 prefixEnd_1533704 := by exact prefixLift 1533704
  have htrace : WordTrace (prefixWord ++ tailWord_1533704) baseStart_1533704 baseEnd_1533704 := by
    simpa [prefixWord, tailWord_1533704, baseEnd_1533704] using wordTrace_append hprefix tailTrace_1533704
  have hstable : (prefixWord ++ tailWord_1533704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533704).length < 2 ^ (prefixWord ++ tailWord_1533704).sum := by decide
  have hdescent : baseEnd_1533704 < baseStart_1533704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533736 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_1533736 : Nat := 118140960795 + 1533736 * 2 ^ 59
def prefixEnd_1533736 : Nat := 4983230072969 + 3 ^ 40 * 1533736 * 2
def baseEnd_1533736 : Nat := 175009725578736996565885

theorem tailTrace_1533736 : CollatzResearch.WordTrace tailWord_1533736 prefixEnd_1533736 175009725578736996565885 := by
  unfold tailWord_1533736
  simp only [CollatzResearch.WordTrace]
  refine ⟨27969973785771944049850531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37293298381029258733134041 27969973785771944049850531)
  ·
    refine ⟨41954960678657916074775797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27969973785771944049850531 41954960678657916074775797)
    ·
      refine ⟨3933277563624179632010231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41954960678657916074775797 3933277563624179632010231)
      ·
        refine ⟨5899916345436269448015347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3933277563624179632010231 5899916345436269448015347)
        ·
          refine ⟨8849874518154404172023021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5899916345436269448015347 8849874518154404172023021)
          ·
            refine ⟨3318702944307901564508633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8849874518154404172023021 3318702944307901564508633)
            ·
              refine ⟨2489027208230926173381475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3318702944307901564508633 2489027208230926173381475)
              ·
                refine ⟨3733540812346389260072213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489027208230926173381475 3733540812346389260072213)
                ·
                  refine ⟨175009725578736996565885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3733540812346389260072213 175009725578736996565885)
                  ·
                    rfl

theorem cell22_1533736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_1533736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533736 prefixEnd_1533736 := by exact prefixLift 1533736
  have htrace : WordTrace (prefixWord ++ tailWord_1533736) baseStart_1533736 baseEnd_1533736 := by
    simpa [prefixWord, tailWord_1533736, baseEnd_1533736] using wordTrace_append hprefix tailTrace_1533736
  have hstable : (prefixWord ++ tailWord_1533736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533736).length < 2 ^ (prefixWord ++ tailWord_1533736).sum := by decide
  have hdescent : baseEnd_1533736 < baseStart_1533736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533847 : List Nat := [1, 1, 3, 3, 1, 5, 2, 2, 1, 3]
def baseStart_1533847 : Nat := 118140960795 + 1533847 * 2 ^ 59
def prefixEnd_1533847 : Nat := 4983230072969 + 3 ^ 40 * 1533847 * 2
def baseEnd_1533847 : Nat := 525067174304643700172315

theorem tailTrace_1533847 : CollatzResearch.WordTrace tailWord_1533847 prefixEnd_1533847 525067174304643700172315 := by
  unfold tailWord_1533847
  simp only [CollatzResearch.WordTrace]
  refine ⟨55943996074141754056991795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37295997382761169371327863 55943996074141754056991795)
  ·
    refine ⟨83915994111212631085487693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55943996074141754056991795 83915994111212631085487693)
    ·
      refine ⟨31468497791704736657057885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83915994111212631085487693 31468497791704736657057885)
      ·
        refine ⟨11800686671889276246396707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31468497791704736657057885 11800686671889276246396707)
        ·
          refine ⟨17701030007833914369595061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11800686671889276246396707 17701030007833914369595061)
          ·
            refine ⟨1659471563234429472149537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17701030007833914369595061 1659471563234429472149537)
            ·
              refine ⟨1244603672425822104112153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659471563234429472149537 1244603672425822104112153)
              ·
                refine ⟨933452754319366578084115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244603672425822104112153 933452754319366578084115)
                ·
                  refine ⟨1400179131479049867126173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933452754319366578084115 1400179131479049867126173)
                  ·
                    refine ⟨525067174304643700172315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1400179131479049867126173 525067174304643700172315)
                    ·
                      rfl

theorem cell22_1533847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_1533847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533847 prefixEnd_1533847 := by exact prefixLift 1533847
  have htrace : WordTrace (prefixWord ++ tailWord_1533847) baseStart_1533847 baseEnd_1533847 := by
    simpa [prefixWord, tailWord_1533847, baseEnd_1533847] using wordTrace_append hprefix tailTrace_1533847
  have hstable : (prefixWord ++ tailWord_1533847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533847).length < 2 ^ (prefixWord ++ tailWord_1533847).sum := by decide
  have hdescent : baseEnd_1533847 < baseStart_1533847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533858 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1533858 : Nat := 118140960795 + 1533858 * 2 ^ 59
def prefixEnd_1533858 : Nat := 4983230072969 + 3 ^ 40 * 1533858 * 2
def baseEnd_1533858 : Nat := 525070939829443338147281

theorem tailTrace_1533858 : CollatzResearch.WordTrace tailWord_1533858 prefixEnd_1533858 525070939829443338147281 := by
  unfold tailWord_1533858
  simp only [CollatzResearch.WordTrace]
  refine ⟨13986099319275475733910557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37296264851401268623761485 13986099319275475733910557)
  ·
    refine ⟨5244787244728303400216459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13986099319275475733910557 5244787244728303400216459)
    ·
      refine ⟨7867180867092455100324689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5244787244728303400216459 7867180867092455100324689)
      ·
        refine ⟨5900385650319341325243517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7867180867092455100324689 5900385650319341325243517)
        ·
          refine ⟨2212644618869752996966319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5900385650319341325243517 2212644618869752996966319)
          ·
            refine ⟨3318966928304629495449479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2212644618869752996966319 3318966928304629495449479)
            ·
              refine ⟨4978450392456944243174219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3318966928304629495449479 4978450392456944243174219)
              ·
                refine ⟨7467675588685416364761329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4978450392456944243174219 7467675588685416364761329)
                ·
                  refine ⟨5600756691514062273570997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7467675588685416364761329 5600756691514062273570997)
                  ·
                    refine ⟨525070939829443338147281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5600756691514062273570997 525070939829443338147281)
                    ·
                      rfl

theorem cell22_1533858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1533858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533858 prefixEnd_1533858 := by exact prefixLift 1533858
  have htrace : WordTrace (prefixWord ++ tailWord_1533858) baseStart_1533858 baseEnd_1533858 := by
    simpa [prefixWord, tailWord_1533858, baseEnd_1533858] using wordTrace_append hprefix tailTrace_1533858
  have hstable : (prefixWord ++ tailWord_1533858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533858).length < 2 ^ (prefixWord ++ tailWord_1533858).sum := by decide
  have hdescent : baseEnd_1533858 < baseStart_1533858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533888 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 4]
def baseStart_1533888 : Nat := 118140960795 + 1533888 * 2 ^ 59
def prefixEnd_1533888 : Nat := 4983230072969 + 3 ^ 40 * 1533888 * 2
def baseEnd_1533888 : Nat := 175027069814177753299063

theorem tailTrace_1533888 : CollatzResearch.WordTrace tailWord_1533888 prefixEnd_1533888 175027069814177753299063 := by
  unfold tailWord_1533888
  simp only [CollatzResearch.WordTrace]
  refine ⟨27972745733496609029617159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37296994311328812039489545 27972745733496609029617159)
  ·
    refine ⟨41959118600244913544425739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27972745733496609029617159 41959118600244913544425739)
    ·
      refine ⟨62938677900367370316638609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41959118600244913544425739 62938677900367370316638609)
      ·
        refine ⟨47204008425275527737478957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62938677900367370316638609 47204008425275527737478957)
        ·
          refine ⟨17701503159478322901554609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47204008425275527737478957 17701503159478322901554609)
          ·
            refine ⟨13276127369608742176165957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17701503159478322901554609 13276127369608742176165957)
            ·
              refine ⟨2489273881801639158031117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13276127369608742176165957 2489273881801639158031117)
              ·
                refine ⟨933477705675614684261669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2489273881801639158031117 933477705675614684261669)
                ·
                  refine ⟨175027069814177753299063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933477705675614684261669 175027069814177753299063)
                  ·
                    rfl

theorem cell22_1533888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 4].length) (baseStart_1533888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533888 prefixEnd_1533888 := by exact prefixLift 1533888
  have htrace : WordTrace (prefixWord ++ tailWord_1533888) baseStart_1533888 baseEnd_1533888 := by
    simpa [prefixWord, tailWord_1533888, baseEnd_1533888] using wordTrace_append hprefix tailTrace_1533888
  have hstable : (prefixWord ++ tailWord_1533888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533888).length < 2 ^ (prefixWord ++ tailWord_1533888).sum := by decide
  have hdescent : baseEnd_1533888 < baseStart_1533888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533899 : List Nat := [1, 1, 1, 1, 3, 4, 11]
def baseStart_1533899 : Nat := 118140960795 + 1533899 * 2 ^ 59
def prefixEnd_1533899 : Nat := 4983230072969 + 3 ^ 40 * 1533899 * 2
def baseEnd_1533899 : Nat := 19447591665456773995265

theorem tailTrace_1533899 : CollatzResearch.WordTrace tailWord_1533899 prefixEnd_1533899 19447591665456773995265 := by
  unfold tailWord_1533899
  simp only [CollatzResearch.WordTrace]
  refine ⟨55945892669953366937884751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37297261779968911291923167 55945892669953366937884751)
  ·
    refine ⟨83918839004930050406827127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55945892669953366937884751 83918839004930050406827127)
    ·
      refine ⟨125878258507395075610240691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83918839004930050406827127 125878258507395075610240691)
      ·
        refine ⟨188817387761092613415361037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125878258507395075610240691 188817387761092613415361037)
        ·
          refine ⟨70806520410409730030760389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188817387761092613415361037 70806520410409730030760389)
          ·
            refine ⟨13276222576951824380767573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70806520410409730030760389 13276222576951824380767573)
            ·
              refine ⟨19447591665456773995265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13276222576951824380767573 19447591665456773995265)
              ·
                rfl

theorem cell22_1533899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 11].length) (baseStart_1533899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533899 prefixEnd_1533899 := by exact prefixLift 1533899
  have htrace : WordTrace (prefixWord ++ tailWord_1533899) baseStart_1533899 baseEnd_1533899 := by
    simpa [prefixWord, tailWord_1533899, baseEnd_1533899] using wordTrace_append hprefix tailTrace_1533899
  have hstable : (prefixWord ++ tailWord_1533899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533899).length < 2 ^ (prefixWord ++ tailWord_1533899).sum := by decide
  have hdescent : baseEnd_1533899 < baseStart_1533899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533976 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_1533976 : Nat := 118140960795 + 1533976 * 2 ^ 59
def prefixEnd_1533976 : Nat := 4983230072969 + 3 ^ 40 * 1533976 * 2
def baseEnd_1533976 : Nat := 525111333640930363696919

theorem tailTrace_1533976 : CollatzResearch.WordTrace tailWord_1533976 prefixEnd_1533976 525111333640930363696919 := by
  unfold tailWord_1533976
  simp only [CollatzResearch.WordTrace]
  refine ⟨27974350545337204544218891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37299134060449606058958521 27974350545337204544218891)
  ·
    refine ⟨41961525818005806816328337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27974350545337204544218891 41961525818005806816328337)
    ·
      refine ⟨31471144363504355112246253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41961525818005806816328337 31471144363504355112246253)
      ·
        refine ⟨11801679136314133167092345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31471144363504355112246253 11801679136314133167092345)
        ·
          refine ⟨8851259352235599875319259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11801679136314133167092345 8851259352235599875319259)
          ·
            refine ⟨13276889028353399812978889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8851259352235599875319259 13276889028353399812978889)
            ·
              refine ⟨9957666771265049859734167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13276889028353399812978889 9957666771265049859734167)
              ·
                refine ⟨14936500156897574789601251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9957666771265049859734167 14936500156897574789601251)
                ·
                  refine ⟨22404750235346362184401877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14936500156897574789601251 22404750235346362184401877)
                  ·
                    refine ⟨525111333640930363696919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22404750235346362184401877 525111333640930363696919)
                    ·
                      rfl

theorem cell22_1533976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_1533976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533976 prefixEnd_1533976 := by exact prefixLift 1533976
  have htrace : WordTrace (prefixWord ++ tailWord_1533976) baseStart_1533976 baseEnd_1533976 := by
    simpa [prefixWord, tailWord_1533976, baseEnd_1533976] using wordTrace_append hprefix tailTrace_1533976
  have hstable : (prefixWord ++ tailWord_1533976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533976).length < 2 ^ (prefixWord ++ tailWord_1533976).sum := by decide
  have hdescent : baseEnd_1533976 < baseStart_1533976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1533978 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 5]
def baseStart_1533978 : Nat := 118140960795 + 1533978 * 2 ^ 59
def prefixEnd_1533978 : Nat := 4983230072969 + 3 ^ 40 * 1533978 * 2
def baseEnd_1533978 : Nat := 175037339427267675048971

theorem tailTrace_1533978 : CollatzResearch.WordTrace tailWord_1533978 prefixEnd_1533978 175037339427267675048971 := by
  unfold tailWord_1533978
  simp only [CollatzResearch.WordTrace]
  refine ⟨13987193509166790857502647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37299182691111442286673725 13987193509166790857502647)
  ·
    refine ⟨20980790263750186286253971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13987193509166790857502647 20980790263750186286253971)
    ·
      refine ⟨31471185395625279429380957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20980790263750186286253971 31471185395625279429380957)
      ·
        refine ⟨11801694523359479786017859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31471185395625279429380957 11801694523359479786017859)
        ·
          refine ⟨17702541785039219679026789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11801694523359479786017859 17702541785039219679026789)
          ·
            refine ⟨3319226584694853689817523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17702541785039219679026789 3319226584694853689817523)
            ·
              refine ⟨4978839877042280534726285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319226584694853689817523 4978839877042280534726285)
              ·
                refine ⟨1867064953890855200522357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4978839877042280534726285 1867064953890855200522357)
                ·
                  refine ⟨175037339427267675048971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867064953890855200522357 175037339427267675048971)
                  ·
                    rfl

theorem cell22_1533978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_1533978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1533978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1533978 prefixEnd_1533978 := by exact prefixLift 1533978
  have htrace : WordTrace (prefixWord ++ tailWord_1533978) baseStart_1533978 baseEnd_1533978 := by
    simpa [prefixWord, tailWord_1533978, baseEnd_1533978] using wordTrace_append hprefix tailTrace_1533978
  have hstable : (prefixWord ++ tailWord_1533978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1533978).length < 2 ^ (prefixWord ++ tailWord_1533978).sum := by decide
  have hdescent : baseEnd_1533978 < baseStart_1533978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1533978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534021 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 5, 5]
def baseStart_1534021 : Nat := 118140960795 + 1534021 * 2 ^ 59
def prefixEnd_1534021 : Nat := 4983230072969 + 3 ^ 40 * 1534021 * 2
def baseEnd_1534021 : Nat := 525126738060565246321781

theorem tailTrace_1534021 : CollatzResearch.WordTrace tailWord_1534021 prefixEnd_1534021 525126738060565246321781 := by
  unfold tailWord_1534021
  simp only [CollatzResearch.WordTrace]
  refine ⟨55950342375511381773825917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37300228250340921182550611 55950342375511381773825917)
  ·
    refine ⟨20981378390816768165184719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55950342375511381773825917 20981378390816768165184719)
    ·
      refine ⟨31472067586225152247777079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20981378390816768165184719 31472067586225152247777079)
      ·
        refine ⟨47208101379337728371665619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31472067586225152247777079 47208101379337728371665619)
        ·
          refine ⟨70812152069006592557498429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47208101379337728371665619 70812152069006592557498429)
          ·
            refine ⟨26554557025877472209061911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70812152069006592557498429 26554557025877472209061911)
            ·
              refine ⟨39831835538816208313592867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26554557025877472209061911 39831835538816208313592867)
              ·
                refine ⟨59747753308224312470389301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39831835538816208313592867 59747753308224312470389301)
                ·
                  refine ⟨5601351872646029294098997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59747753308224312470389301 5601351872646029294098997)
                  ·
                    refine ⟨525126738060565246321781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5601351872646029294098997 525126738060565246321781)
                    ·
                      rfl

theorem cell22_1534021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_1534021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534021 prefixEnd_1534021 := by exact prefixLift 1534021
  have htrace : WordTrace (prefixWord ++ tailWord_1534021) baseStart_1534021 baseEnd_1534021 := by
    simpa [prefixWord, tailWord_1534021, baseEnd_1534021] using wordTrace_append hprefix tailTrace_1534021
  have hstable : (prefixWord ++ tailWord_1534021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534021).length < 2 ^ (prefixWord ++ tailWord_1534021).sum := by decide
  have hdescent : baseEnd_1534021 < baseStart_1534021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534051 : List Nat := [1, 1, 1, 5, 1, 1, 2, 10]
def baseStart_1534051 : Nat := 118140960795 + 1534051 * 2 ^ 59
def prefixEnd_1534051 : Nat := 4983230072969 + 3 ^ 40 * 1534051 * 2
def baseEnd_1534051 : Nat := 58348556408183907563521

theorem tailTrace_1534051 : CollatzResearch.WordTrace tailWord_1534051 prefixEnd_1534051 58348556408183907563521 := by
  unfold tailWord_1534051
  simp only [CollatzResearch.WordTrace]
  refine ⟨55951436565402696897418007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37300957710268464598278671 55951436565402696897418007)
  ·
    refine ⟨83927154848104045346127011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55951436565402696897418007 83927154848104045346127011)
    ·
      refine ⟨125890732272156068019190517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83927154848104045346127011 125890732272156068019190517)
      ·
        refine ⟨11802256150514631376799111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125890732272156068019190517 11802256150514631376799111)
        ·
          refine ⟨17703384225771947065198667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11802256150514631376799111 17703384225771947065198667)
          ·
            refine ⟨26555076338657920597798001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17703384225771947065198667 26555076338657920597798001)
            ·
              refine ⟨19916307253993440448348501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26555076338657920597798001 19916307253993440448348501)
              ·
                refine ⟨58348556408183907563521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19916307253993440448348501 58348556408183907563521)
                ·
                  rfl

theorem cell22_1534051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 10].length) (baseStart_1534051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534051 prefixEnd_1534051 := by exact prefixLift 1534051
  have htrace : WordTrace (prefixWord ++ tailWord_1534051) baseStart_1534051 baseEnd_1534051 := by
    simpa [prefixWord, tailWord_1534051, baseEnd_1534051] using wordTrace_append hprefix tailTrace_1534051
  have hstable : (prefixWord ++ tailWord_1534051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534051).length < 2 ^ (prefixWord ++ tailWord_1534051).sum := by decide
  have hdescent : baseEnd_1534051 < baseStart_1534051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534053 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 1, 6]
def baseStart_1534053 : Nat := 118140960795 + 1534053 * 2 ^ 59
def prefixEnd_1534053 : Nat := 4983230072969 + 3 ^ 40 * 1534053 * 2
def baseEnd_1534053 : Nat := 525137692314527829521683

theorem tailTrace_1534053 : CollatzResearch.WordTrace tailWord_1534053 prefixEnd_1534053 525137692314527829521683 := by
  unfold tailWord_1534053
  simp only [CollatzResearch.WordTrace]
  refine ⟨55951509511395451238990813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37301006340930300825993875 55951509511395451238990813)
  ·
    refine ⟨20981816066773294214621555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55951509511395451238990813 20981816066773294214621555)
    ·
      refine ⟨31472724100159941321932333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20981816066773294214621555 31472724100159941321932333)
      ·
        refine ⟨11802271537559977995724625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31472724100159941321932333 11802271537559977995724625)
        ·
          refine ⟨8851703653169983496793469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11802271537559977995724625 8851703653169983496793469)
          ·
            refine ⟨3319388869938743811297551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8851703653169983496793469 3319388869938743811297551)
            ·
              refine ⟨4979083304908115716946327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3319388869938743811297551 4979083304908115716946327)
              ·
                refine ⟨7468624957362173575419491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4979083304908115716946327 7468624957362173575419491)
                ·
                  refine ⟨11202937436043260363129237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7468624957362173575419491 11202937436043260363129237)
                  ·
                    refine ⟨525137692314527829521683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11202937436043260363129237 525137692314527829521683)
                    ·
                      rfl

theorem cell22_1534053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_1534053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534053 prefixEnd_1534053 := by exact prefixLift 1534053
  have htrace : WordTrace (prefixWord ++ tailWord_1534053) baseStart_1534053 baseEnd_1534053 := by
    simpa [prefixWord, tailWord_1534053, baseEnd_1534053] using wordTrace_append hprefix tailTrace_1534053
  have hstable : (prefixWord ++ tailWord_1534053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534053).length < 2 ^ (prefixWord ++ tailWord_1534053).sum := by decide
  have hdescent : baseEnd_1534053 < baseStart_1534053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534113 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 7]
def baseStart_1534113 : Nat := 118140960795 + 1534113 * 2 ^ 59
def prefixEnd_1534113 : Nat := 4983230072969 + 3 ^ 40 * 1534113 * 2
def baseEnd_1534113 : Nat := 175052743846902557673833

theorem tailTrace_1534113 : CollatzResearch.WordTrace tailWord_1534113 prefixEnd_1534113 175052743846902557673833 := by
  unfold tailWord_1534113
  simp only [CollatzResearch.WordTrace]
  refine ⟨55953697891178081486174993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37302465260785387657449995 55953697891178081486174993)
  ·
    refine ⟨41965273418383561114631245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55953697891178081486174993 41965273418383561114631245)
    ·
      refine ⟨15736977531893835417986717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41965273418383561114631245 15736977531893835417986717)
      ·
        refine ⟨5901366574460188281745019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15736977531893835417986717 5901366574460188281745019)
        ·
          refine ⟨8852049861690282422617529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5901366574460188281745019 8852049861690282422617529)
          ·
            refine ⟨6639037396267711816963147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8852049861690282422617529 6639037396267711816963147)
            ·
              refine ⟨9958556094401567725444721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6639037396267711816963147 9958556094401567725444721)
              ·
                refine ⟨7468917070801175794083541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9958556094401567725444721 7468917070801175794083541)
                ·
                  refine ⟨175052743846902557673833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7468917070801175794083541 175052743846902557673833)
                  ·
                    rfl

theorem cell22_1534113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 7].length) (baseStart_1534113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534113 prefixEnd_1534113 := by exact prefixLift 1534113
  have htrace : WordTrace (prefixWord ++ tailWord_1534113) baseStart_1534113 baseEnd_1534113 := by
    simpa [prefixWord, tailWord_1534113, baseEnd_1534113] using wordTrace_append hprefix tailTrace_1534113
  have hstable : (prefixWord ++ tailWord_1534113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534113).length < 2 ^ (prefixWord ++ tailWord_1534113).sum := by decide
  have hdescent : baseEnd_1534113 < baseStart_1534113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534143 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 3, 4]
def baseStart_1534143 : Nat := 118140960795 + 1534143 * 2 ^ 59
def prefixEnd_1534143 : Nat := 4983230072969 + 3 ^ 40 * 1534143 * 2
def baseEnd_1534143 : Nat := 525168501153797594771407

theorem tailTrace_1534143 : CollatzResearch.WordTrace tailWord_1534143 prefixEnd_1534143 525168501153797594771407 := by
  unfold tailWord_1534143
  simp only [CollatzResearch.WordTrace]
  refine ⟨55954792081069396609767083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37303194720712931073178055 55954792081069396609767083)
  ·
    refine ⟨83932188121604094914650625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55954792081069396609767083 83932188121604094914650625)
    ·
      refine ⟨62949141091203071185987969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83932188121604094914650625 62949141091203071185987969)
      ·
        refine ⟨47211855818402303389490977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62949141091203071185987969 47211855818402303389490977)
        ·
          refine ⟨35408891863801727542118233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47211855818402303389490977 35408891863801727542118233)
          ·
            refine ⟨26556668897851295656588675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35408891863801727542118233 26556668897851295656588675)
            ·
              refine ⟨39835003346776943484883013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26556668897851295656588675 39835003346776943484883013)
              ·
                refine ⟨7469063127520676903415565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39835003346776943484883013 7469063127520676903415565)
                ·
                  refine ⟨2800898672820253838780837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7469063127520676903415565 2800898672820253838780837)
                  ·
                    refine ⟨525168501153797594771407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800898672820253838780837 525168501153797594771407)
                    ·
                      rfl

theorem cell22_1534143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 3, 4].length) (baseStart_1534143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534143 prefixEnd_1534143 := by exact prefixLift 1534143
  have htrace : WordTrace (prefixWord ++ tailWord_1534143) baseStart_1534143 baseEnd_1534143 := by
    simpa [prefixWord, tailWord_1534143, baseEnd_1534143] using wordTrace_append hprefix tailTrace_1534143
  have hstable : (prefixWord ++ tailWord_1534143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534143).length < 2 ^ (prefixWord ++ tailWord_1534143).sum := by decide
  have hdescent : baseEnd_1534143 < baseStart_1534143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534175 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 4]
def baseStart_1534175 : Nat := 118140960795 + 1534175 * 2 ^ 59
def prefixEnd_1534175 : Nat := 4983230072969 + 3 ^ 40 * 1534175 * 2
def baseEnd_1534175 : Nat := 175059818469253392657103

theorem tailTrace_1534175 : CollatzResearch.WordTrace tailWord_1534175 prefixEnd_1534175 175059818469253392657103 := by
  unfold tailWord_1534175
  simp only [CollatzResearch.WordTrace]
  refine ⟨55955959216953466074931979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37303972811302310716621319 55955959216953466074931979)
  ·
    refine ⟨83933938825430199112397969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55955959216953466074931979 83933938825430199112397969)
    ·
      refine ⟨62950454119072649334298477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83933938825430199112397969 62950454119072649334298477)
      ·
        refine ⟨23606420294652243500361929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62950454119072649334298477 23606420294652243500361929)
        ·
          refine ⟨17704815220989182625271447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23606420294652243500361929 17704815220989182625271447)
          ·
            refine ⟨26557222831483773937907171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17704815220989182625271447 26557222831483773937907171)
            ·
              refine ⟨39835834247225660906860757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26557222831483773937907171 39835834247225660906860757)
              ·
                refine ⟨933652365169351427504549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39835834247225660906860757 933652365169351427504549)
                ·
                  refine ⟨175059818469253392657103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 933652365169351427504549 175059818469253392657103)
                  ·
                    rfl

theorem cell22_1534175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 4].length) (baseStart_1534175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534175 prefixEnd_1534175 := by exact prefixLift 1534175
  have htrace : WordTrace (prefixWord ++ tailWord_1534175) baseStart_1534175 baseEnd_1534175 := by
    simpa [prefixWord, tailWord_1534175, baseEnd_1534175] using wordTrace_append hprefix tailTrace_1534175
  have hstable : (prefixWord ++ tailWord_1534175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534175).length < 2 ^ (prefixWord ++ tailWord_1534175).sum := by decide
  have hdescent : baseEnd_1534175 < baseStart_1534175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534177 : List Nat := [1, 2, 3, 1, 3, 1, 5, 1, 1, 4]
def baseStart_1534177 : Nat := 118140960795 + 1534177 * 2 ^ 59
def prefixEnd_1534177 : Nat := 4983230072969 + 3 ^ 40 * 1534177 * 2
def baseEnd_1534177 : Nat := 525180140048632839421303

theorem tailTrace_1534177 : CollatzResearch.WordTrace tailWord_1534177 prefixEnd_1534177 525180140048632839421303 := by
  unfold tailWord_1534177
  simp only [CollatzResearch.WordTrace]
  refine ⟨55956032162946220416504785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37304021441964146944336523 55956032162946220416504785)
  ·
    refine ⟨41967024122209665312378589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55956032162946220416504785 41967024122209665312378589)
    ·
      refine ⟨15737634045828624492141971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41967024122209665312378589 15737634045828624492141971)
      ·
        refine ⟨23606451068742936738212957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15737634045828624492141971 23606451068742936738212957)
        ·
          refine ⟨8852419150778601276829859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23606451068742936738212957 8852419150778601276829859)
          ·
            refine ⟨13278628726167901915244789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8852419150778601276829859 13278628726167901915244789)
            ·
              refine ⟨1244871443078240804554199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13278628726167901915244789 1244871443078240804554199)
              ·
                refine ⟨1867307164617361206831299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244871443078240804554199 1867307164617361206831299)
                ·
                  refine ⟨2800960746926041810246949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867307164617361206831299 2800960746926041810246949)
                  ·
                    refine ⟨525180140048632839421303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2800960746926041810246949 525180140048632839421303)
                    ·
                      rfl

theorem cell22_1534177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_1534177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534177 prefixEnd_1534177 := by exact prefixLift 1534177
  have htrace : WordTrace (prefixWord ++ tailWord_1534177) baseStart_1534177 baseEnd_1534177 := by
    simpa [prefixWord, tailWord_1534177, baseEnd_1534177] using wordTrace_append hprefix tailTrace_1534177
  have hstable : (prefixWord ++ tailWord_1534177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534177).length < 2 ^ (prefixWord ++ tailWord_1534177).sum := by decide
  have hdescent : baseEnd_1534177 < baseStart_1534177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534220 : List Nat := [2, 2, 1, 2, 2, 2, 5, 6]
def baseStart_1534220 : Nat := 118140960795 + 1534220 * 2 ^ 59
def prefixEnd_1534220 : Nat := 4983230072969 + 3 ^ 40 * 1534220 * 2
def baseEnd_1534220 : Nat := 58354984425266117844019

theorem tailTrace_1534220 : CollatzResearch.WordTrace tailWord_1534220 prefixEnd_1534220 58354984425266117844019 := by
  unfold tailWord_1534220
  simp only [CollatzResearch.WordTrace]
  refine ⟨27978800250895219380160057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37305067001193625840213409 27978800250895219380160057)
  ·
    refine ⟨20984100188171414535120043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27978800250895219380160057 20984100188171414535120043)
    ·
      refine ⟨31476150282257121802680065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20984100188171414535120043 31476150282257121802680065)
      ·
        refine ⟨23607112711692841352010049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31476150282257121802680065 23607112711692841352010049)
        ·
          refine ⟨17705334533769631014007537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23607112711692841352010049 17705334533769631014007537)
          ·
            refine ⟨13279000900327223260505653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17705334533769631014007537 13279000900327223260505653)
            ·
              refine ⟨1244906334405677180672405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13279000900327223260505653 1244906334405677180672405)
              ·
                refine ⟨58354984425266117844019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1244906334405677180672405 58354984425266117844019)
                ·
                  rfl

theorem cell22_1534220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 6].length) (baseStart_1534220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534220 prefixEnd_1534220 := by exact prefixLift 1534220
  have htrace : WordTrace (prefixWord ++ tailWord_1534220) baseStart_1534220 baseEnd_1534220 := by
    simpa [prefixWord, tailWord_1534220, baseEnd_1534220] using wordTrace_append hprefix tailTrace_1534220
  have hstable : (prefixWord ++ tailWord_1534220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534220).length < 2 ^ (prefixWord ++ tailWord_1534220).sum := by decide
  have hdescent : baseEnd_1534220 < baseStart_1534220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534316 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 5]
def baseStart_1534316 : Nat := 118140960795 + 1534316 * 2 ^ 59
def prefixEnd_1534316 : Nat := 4983230072969 + 3 ^ 40 * 1534316 * 2
def baseEnd_1534316 : Nat := 175075907529760936731959

theorem tailTrace_1534316 : CollatzResearch.WordTrace tailWord_1534316 prefixEnd_1534316 175075907529760936731959 := by
  unfold tailWord_1534316
  simp only [CollatzResearch.WordTrace]
  refine ⟨27980550954721323577907401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37307401272961764770543201 27980550954721323577907401)
  ·
    refine ⟨20985413216040992683430551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27980550954721323577907401 20985413216040992683430551)
    ·
      refine ⟨31478119824061489025145827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20985413216040992683430551 31478119824061489025145827)
      ·
        refine ⟨47217179736092233537718741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31478119824061489025145827 47217179736092233537718741)
        ·
          refine ⟨1106652650064661723540283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 47217179736092233537718741 1106652650064661723540283)
          ·
            refine ⟨1659978975096992585310425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106652650064661723540283 1659978975096992585310425)
            ·
              refine ⟨1244984231322744438982819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659978975096992585310425 1244984231322744438982819)
              ·
                refine ⟨1867476346984116658474229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244984231322744438982819 1867476346984116658474229)
                ·
                  refine ⟨175075907529760936731959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1867476346984116658474229 175075907529760936731959)
                  ·
                    rfl

theorem cell22_1534316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 5].length) (baseStart_1534316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534316 prefixEnd_1534316 := by exact prefixLift 1534316
  have htrace : WordTrace (prefixWord ++ tailWord_1534316) baseStart_1534316 baseEnd_1534316 := by
    simpa [prefixWord, tailWord_1534316, baseEnd_1534316] using wordTrace_append hprefix tailTrace_1534316
  have hstable : (prefixWord ++ tailWord_1534316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534316).length < 2 ^ (prefixWord ++ tailWord_1534316).sum := by decide
  have hdescent : baseEnd_1534316 < baseStart_1534316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534376 : List Nat := [2, 1, 6, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1534376 : Nat := 118140960795 + 1534376 * 2 ^ 59
def prefixEnd_1534376 : Nat := 4983230072969 + 3 ^ 40 * 1534376 * 2
def baseEnd_1534376 : Nat := 525248261815462653695693

theorem tailTrace_1534376 : CollatzResearch.WordTrace tailWord_1534376 prefixEnd_1534376 525248261815462653695693 := by
  unfold tailWord_1534376
  simp only [CollatzResearch.WordTrace]
  refine ⟨27981645144612638701499491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37308860192816851601999321 27981645144612638701499491)
  ·
    refine ⟨41972467716918958052249237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27981645144612638701499491 41972467716918958052249237)
    ·
      refine ⟨1967459424230576158699183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 41972467716918958052249237 1967459424230576158699183)
      ·
        refine ⟨2951189136345864238048775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967459424230576158699183 2951189136345864238048775)
        ·
          refine ⟨4426783704518796357073163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2951189136345864238048775 4426783704518796357073163)
          ·
            refine ⟨6640175556778194535609745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4426783704518796357073163 6640175556778194535609745)
            ·
              refine ⟨4980131667583645901707309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6640175556778194535609745 4980131667583645901707309)
              ·
                refine ⟨1867549375343867213140241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4980131667583645901707309 1867549375343867213140241)
                ·
                  refine ⟨1400662031507900409855181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1867549375343867213140241 1400662031507900409855181)
                  ·
                    refine ⟨525248261815462653695693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1400662031507900409855181 525248261815462653695693)
                    ·
                      rfl

theorem cell22_1534376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1534376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534376 prefixEnd_1534376 := by exact prefixLift 1534376
  have htrace : WordTrace (prefixWord ++ tailWord_1534376) baseStart_1534376 baseEnd_1534376 := by
    simpa [prefixWord, tailWord_1534376, baseEnd_1534376] using wordTrace_append hprefix tailTrace_1534376
  have hstable : (prefixWord ++ tailWord_1534376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534376).length < 2 ^ (prefixWord ++ tailWord_1534376).sum := by decide
  have hdescent : baseEnd_1534376 < baseStart_1534376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534389 : List Nat := [1, 3, 3, 2, 3, 1, 3, 6]
def baseStart_1534389 : Nat := 118140960795 + 1534389 * 2 ^ 59
def prefixEnd_1534389 : Nat := 4983230072969 + 3 ^ 40 * 1534389 * 2
def baseEnd_1534389 : Nat := 58361412442348328124517

theorem tailTrace_1534389 : CollatzResearch.WordTrace tailWord_1534389 prefixEnd_1534389 58361412442348328124517 := by
  unfold tailWord_1534389
  simp only [CollatzResearch.WordTrace]
  refine ⟨55963764438178180623222221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37309176292118787082148147 55963764438178180623222221)
  ·
    refine ⟨20986411664316817733708333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55963764438178180623222221 20986411664316817733708333)
    ·
      refine ⟨7869904374118806650140625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20986411664316817733708333 7869904374118806650140625)
      ·
        refine ⟨5902428280589104987605469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7869904374118806650140625 5902428280589104987605469)
        ·
          refine ⟨2213410605220914370352051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5902428280589104987605469 2213410605220914370352051)
          ·
            refine ⟨3320115907831371555528077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2213410605220914370352051 3320115907831371555528077)
            ·
              refine ⟨1245043465436764333323029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3320115907831371555528077 1245043465436764333323029)
              ·
                refine ⟨58361412442348328124517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1245043465436764333323029 58361412442348328124517)
                ·
                  rfl

theorem cell22_1534389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 6].length) (baseStart_1534389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534389 prefixEnd_1534389 := by exact prefixLift 1534389
  have htrace : WordTrace (prefixWord ++ tailWord_1534389) baseStart_1534389 baseEnd_1534389 := by
    simpa [prefixWord, tailWord_1534389, baseEnd_1534389] using wordTrace_append hprefix tailTrace_1534389
  have hstable : (prefixWord ++ tailWord_1534389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534389).length < 2 ^ (prefixWord ++ tailWord_1534389).sum := by decide
  have hdescent : baseEnd_1534389 < baseStart_1534389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534400 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 7]
def baseStart_1534400 : Nat := 118140960795 + 1534400 * 2 ^ 59
def prefixEnd_1534400 : Nat := 4983230072969 + 3 ^ 40 * 1534400 * 2
def baseEnd_1534400 : Nat := 175085492501978197031873

theorem tailTrace_1534400 : CollatzResearch.WordTrace tailWord_1534400 prefixEnd_1534400 175085492501978197031873 := by
  unfold tailWord_1534400
  simp only [CollatzResearch.WordTrace]
  refine ⟨27982082820569164750936327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37309443760758886334581769 27982082820569164750936327)
  ·
    refine ⟨41973124230853747126404491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27982082820569164750936327 41973124230853747126404491)
    ·
      refine ⟨62959686346280620689606737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41973124230853747126404491 62959686346280620689606737)
      ·
        refine ⟨47219764759710465517205053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62959686346280620689606737 47219764759710465517205053)
        ·
          refine ⟨17707411784891424568951895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47219764759710465517205053 17707411784891424568951895)
          ·
            refine ⟨26561117677337136853427843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17707411784891424568951895 26561117677337136853427843)
            ·
              refine ⟨39841676516005705280141765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26561117677337136853427843 39841676516005705280141765)
              ·
                refine ⟨7470314346751069740026581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39841676516005705280141765 7470314346751069740026581)
                ·
                  refine ⟨175085492501978197031873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7470314346751069740026581 175085492501978197031873)
                  ·
                    rfl

theorem cell22_1534400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 7].length) (baseStart_1534400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534400 prefixEnd_1534400 := by exact prefixLift 1534400
  have htrace : WordTrace (prefixWord ++ tailWord_1534400) baseStart_1534400 baseEnd_1534400 := by
    simpa [prefixWord, tailWord_1534400, baseEnd_1534400] using wordTrace_append hprefix tailTrace_1534400
  have hstable : (prefixWord ++ tailWord_1534400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534400).length < 2 ^ (prefixWord ++ tailWord_1534400).sum := by decide
  have hdescent : baseEnd_1534400 < baseStart_1534400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534421 : List Nat := [1, 3, 2, 3, 1, 2, 2, 4, 1, 3]
def baseStart_1534421 : Nat := 118140960795 + 1534421 * 2 ^ 59
def prefixEnd_1534421 : Nat := 4983230072969 + 3 ^ 40 * 1534421 * 2
def baseEnd_1534421 : Nat := 525263666235097536320555

theorem tailTrace_1534421 : CollatzResearch.WordTrace tailWord_1534421 prefixEnd_1534421 525263666235097536320555 := by
  unfold tailWord_1534421
  simp only [CollatzResearch.WordTrace]
  refine ⟨55964931574062250088387117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37309954382708166725591411 55964931574062250088387117)
  ·
    refine ⟨20986849340273343783145169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55964931574062250088387117 20986849340273343783145169)
    ·
      refine ⟨15740137005205007837358877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20986849340273343783145169 15740137005205007837358877)
      ·
        refine ⟨5902551376951877939009579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15740137005205007837358877 5902551376951877939009579)
        ·
          refine ⟨8853827065427816908514369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5902551376951877939009579 8853827065427816908514369)
          ·
            refine ⟨6640370299070862681385777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8853827065427816908514369 6640370299070862681385777)
            ·
              refine ⟨4980277724303147011039333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6640370299070862681385777 4980277724303147011039333)
              ·
                refine ⟨933802073306840064569875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4980277724303147011039333 933802073306840064569875)
                ·
                  refine ⟨1400703109960260096854813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933802073306840064569875 1400703109960260096854813)
                  ·
                    refine ⟨525263666235097536320555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1400703109960260096854813 525263666235097536320555)
                    ·
                      rfl

theorem cell22_1534421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_1534421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534421 prefixEnd_1534421 := by exact prefixLift 1534421
  have htrace : WordTrace (prefixWord ++ tailWord_1534421) baseStart_1534421 baseEnd_1534421 := by
    simpa [prefixWord, tailWord_1534421, baseEnd_1534421] using wordTrace_append hprefix tailTrace_1534421
  have hstable : (prefixWord ++ tailWord_1534421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534421).length < 2 ^ (prefixWord ++ tailWord_1534421).sum := by decide
  have hdescent : baseEnd_1534421 < baseStart_1534421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534541 : List Nat := [1, 6, 1, 1, 2, 3, 1, 7]
def baseStart_1534541 : Nat := 118140960795 + 1534541 * 2 ^ 59
def prefixEnd_1534541 : Nat := 4983230072969 + 3 ^ 40 * 1534541 * 2
def baseEnd_1534541 : Nat := 58367193854161913702243

theorem tailTrace_1534541 : CollatzResearch.WordTrace tailWord_1534541 prefixEnd_1534541 58367193854161913702243 := by
  unfold tailWord_1534541
  simp only [CollatzResearch.WordTrace]
  refine ⟨55969308333627510582755477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37312872222418340388503651 55969308333627510582755477)
  ·
    refine ⟨2623561328138789558566663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55969308333627510582755477 2623561328138789558566663)
    ·
      refine ⟨3935341992208184337849995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2623561328138789558566663 3935341992208184337849995)
      ·
        refine ⟨5903012988312276506774993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935341992208184337849995 5903012988312276506774993)
        ·
          refine ⟨4427259741234207380081245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5903012988312276506774993 4427259741234207380081245)
          ·
            refine ⟨1660222402962827767530467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4427259741234207380081245 1660222402962827767530467)
            ·
              refine ⟨2490333604444241651295701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660222402962827767530467 2490333604444241651295701)
              ·
                refine ⟨58367193854161913702243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2490333604444241651295701 58367193854161913702243)
                ·
                  rfl

theorem cell22_1534541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 7].length) (baseStart_1534541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534541 prefixEnd_1534541 := by exact prefixLift 1534541
  have htrace : WordTrace (prefixWord ++ tailWord_1534541) baseStart_1534541 baseEnd_1534541 := by
    simpa [prefixWord, tailWord_1534541, baseEnd_1534541] using wordTrace_append hprefix tailTrace_1534541
  have hstable : (prefixWord ++ tailWord_1534541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534541).length < 2 ^ (prefixWord ++ tailWord_1534541).sum := by decide
  have hdescent : baseEnd_1534541 < baseStart_1534541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534567 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 3, 7]
def baseStart_1534567 : Nat := 118140960795 + 1534567 * 2 ^ 59
def prefixEnd_1534567 : Nat := 4983230072969 + 3 ^ 40 * 1534567 * 2
def baseEnd_1534567 : Nat := 525313645018801822170107

theorem tailTrace_1534567 : CollatzResearch.WordTrace tailWord_1534567 prefixEnd_1534567 525313645018801822170107 := by
  unfold tailWord_1534567
  simp only [CollatzResearch.WordTrace]
  refine ⟨55970256631533317023201955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37313504421022211348801303 55970256631533317023201955)
  ·
    refine ⟨83955384947299975534802933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55970256631533317023201955 83955384947299975534802933)
    ·
      refine ⟨7870817338809372706387775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83955384947299975534802933 7870817338809372706387775)
      ·
        refine ⟨11806226008214059059581663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870817338809372706387775 11806226008214059059581663)
        ·
          refine ⟨17709339012321088589372495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806226008214059059581663 17709339012321088589372495)
          ·
            refine ⟨26564008518481632884058743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17709339012321088589372495 26564008518481632884058743)
            ·
              refine ⟨39846012777722449326088115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26564008518481632884058743 39846012777722449326088115)
              ·
                refine ⟨59769019166583673989132173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39846012777722449326088115 59769019166583673989132173)
                ·
                  refine ⟨22413382187468877745924565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59769019166583673989132173 22413382187468877745924565)
                  ·
                    refine ⟨525313645018801822170107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22413382187468877745924565 525313645018801822170107)
                    ·
                      rfl

theorem cell22_1534567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_1534567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534567 prefixEnd_1534567 := by exact prefixLift 1534567
  have htrace : WordTrace (prefixWord ++ tailWord_1534567) baseStart_1534567 baseEnd_1534567 := by
    simpa [prefixWord, tailWord_1534567, baseEnd_1534567] using wordTrace_append hprefix tailTrace_1534567
  have hstable : (prefixWord ++ tailWord_1534567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534567).length < 2 ^ (prefixWord ++ tailWord_1534567).sum := by decide
  have hdescent : baseEnd_1534567 < baseStart_1534567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534573 : List Nat := [1, 5, 1, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1534573 : Nat := 118140960795 + 1534573 * 2 ^ 59
def prefixEnd_1534573 : Nat := 4983230072969 + 3 ^ 40 * 1534573 * 2
def baseEnd_1534573 : Nat := 525315698941419806520089

theorem tailTrace_1534573 : CollatzResearch.WordTrace tailWord_1534573 prefixEnd_1534573 525315698941419806520089 := by
  unfold tailWord_1534573
  simp only [CollatzResearch.WordTrace]
  refine ⟨55970475469511580047920373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37313650313007720031946915 55970475469511580047920373)
  ·
    refine ⟨5247232075266710629492535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55970475469511580047920373 5247232075266710629492535)
    ·
      refine ⟨7870848112900065944238803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5247232075266710629492535 7870848112900065944238803)
      ·
        refine ⟨11806272169350098916358205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7870848112900065944238803 11806272169350098916358205)
        ·
          refine ⟨4427352063506287093634327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11806272169350098916358205 4427352063506287093634327)
          ·
            refine ⟨6641028095259430640451491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427352063506287093634327 6641028095259430640451491)
            ·
              refine ⟨9961542142889145960677237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6641028095259430640451491 9961542142889145960677237)
              ·
                refine ⟨933894575895857433813491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9961542142889145960677237 933894575895857433813491)
                ·
                  refine ⟨1400841863843786150720237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933894575895857433813491 1400841863843786150720237)
                  ·
                    refine ⟨525315698941419806520089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1400841863843786150720237 525315698941419806520089)
                    ·
                      rfl

theorem cell22_1534573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1534573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534573 prefixEnd_1534573 := by exact prefixLift 1534573
  have htrace : WordTrace (prefixWord ++ tailWord_1534573) baseStart_1534573 baseEnd_1534573 := by
    simpa [prefixWord, tailWord_1534573, baseEnd_1534573] using wordTrace_append hprefix tailTrace_1534573
  have hstable : (prefixWord ++ tailWord_1534573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534573).length < 2 ^ (prefixWord ++ tailWord_1534573).sum := by decide
  have hdescent : baseEnd_1534573 < baseStart_1534573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534616 : List Nat := [2, 1, 2, 4, 1, 1, 4, 2, 1, 4]
def baseStart_1534616 : Nat := 118140960795 + 1534616 * 2 ^ 59
def prefixEnd_1534616 : Nat := 4983230072969 + 3 ^ 40 * 1534616 * 2
def baseEnd_1534616 : Nat := 525330418720182027694957

theorem tailTrace_1534616 : CollatzResearch.WordTrace tailWord_1534616 prefixEnd_1534616 525330418720182027694957 := by
  unfold tailWord_1534616
  simp only [CollatzResearch.WordTrace]
  refine ⟨27986021904177899195867851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37314695872237198927823801 27986021904177899195867851)
  ·
    refine ⟨41979032856266848793801777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27986021904177899195867851 41979032856266848793801777)
    ·
      refine ⟨31484274642200136595351333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41979032856266848793801777 31484274642200136595351333)
      ·
        refine ⟨5903301495412525611628375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31484274642200136595351333 5903301495412525611628375)
        ·
          refine ⟨8854952243118788417442563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903301495412525611628375 8854952243118788417442563)
          ·
            refine ⟨13282428364678182626163845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8854952243118788417442563 13282428364678182626163845)
            ·
              refine ⟨2490455318377159242405721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13282428364678182626163845 2490455318377159242405721)
              ·
                refine ⟨1867841488782869431804291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490455318377159242405721 1867841488782869431804291)
                ·
                  refine ⟨2801762233174304147706437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1867841488782869431804291 2801762233174304147706437)
                  ·
                    refine ⟨525330418720182027694957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2801762233174304147706437 525330418720182027694957)
                    ·
                      rfl

theorem cell22_1534616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_1534616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534616 prefixEnd_1534616 := by exact prefixLift 1534616
  have htrace : WordTrace (prefixWord ++ tailWord_1534616) baseStart_1534616 baseEnd_1534616 := by
    simpa [prefixWord, tailWord_1534616, baseEnd_1534616] using wordTrace_append hprefix tailTrace_1534616
  have hstable : (prefixWord ++ tailWord_1534616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534616).length < 2 ^ (prefixWord ++ tailWord_1534616).sum := by decide
  have hdescent : baseEnd_1534616 < baseStart_1534616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534796 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1534796 : Nat := 118140960795 + 1534796 * 2 ^ 59
def prefixEnd_1534796 : Nat := 4983230072969 + 3 ^ 40 * 1534796 * 2
def baseEnd_1534796 : Nat := 525392036398721558194405

theorem tailTrace_1534796 : CollatzResearch.WordTrace tailWord_1534796 prefixEnd_1534796 525392036398721558194405 := by
  unfold tailWord_1534796
  simp only [CollatzResearch.WordTrace]
  refine ⟨27989304473851844566644121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37319072631802459422192161 27989304473851844566644121)
  ·
    refine ⟨20991978355388883424983091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27989304473851844566644121 20991978355388883424983091)
    ·
      refine ⟨31487967533083325137474637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20991978355388883424983091 31487967533083325137474637)
      ·
        refine ⟨11807987824906246926552989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31487967533083325137474637 11807987824906246926552989)
        ·
          refine ⟨4427995434339842597457371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11807987824906246926552989 4427995434339842597457371)
          ·
            refine ⟨6641993151509763896186057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4427995434339842597457371 6641993151509763896186057)
            ·
              refine ⟨4981494863632322922139543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6641993151509763896186057 4981494863632322922139543)
              ·
                refine ⟨7472242295448484383209315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4981494863632322922139543 7472242295448484383209315)
                ·
                  refine ⟨11208363443172726574813973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7472242295448484383209315 11208363443172726574813973)
                  ·
                    refine ⟨525392036398721558194405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11208363443172726574813973 525392036398721558194405)
                    ·
                      rfl

theorem cell22_1534796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1534796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534796 prefixEnd_1534796 := by exact prefixLift 1534796
  have htrace : WordTrace (prefixWord ++ tailWord_1534796) baseStart_1534796 baseEnd_1534796 := by
    simpa [prefixWord, tailWord_1534796, baseEnd_1534796] using wordTrace_append hprefix tailTrace_1534796
  have hstable : (prefixWord ++ tailWord_1534796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534796).length < 2 ^ (prefixWord ++ tailWord_1534796).sum := by decide
  have hdescent : baseEnd_1534796 < baseStart_1534796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534871 : List Nat := [1, 1, 3, 3, 1, 2, 2, 2, 2, 5]
def baseStart_1534871 : Nat := 118140960795 + 1534871 * 2 ^ 59
def prefixEnd_1534871 : Nat := 4983230072969 + 3 ^ 40 * 1534871 * 2
def baseEnd_1534871 : Nat := 525417710431446362569175

theorem tailTrace_1534871 : CollatzResearch.WordTrace tailWord_1534871 prefixEnd_1534871 525417710431446362569175 := by
  unfold tailWord_1534871
  simp only [CollatzResearch.WordTrace]
  refine ⟨55981344422431976942268467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37320896281621317961512311 55981344422431976942268467)
  ·
    refine ⟨83972016633647965413402701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55981344422431976942268467 83972016633647965413402701)
    ·
      refine ⟨31489506237617987030026013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83972016633647965413402701 31489506237617987030026013)
      ·
        refine ⟨11808564839106745136259755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31489506237617987030026013 11808564839106745136259755)
        ·
          refine ⟨17712847258660117704389633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11808564839106745136259755 17712847258660117704389633)
          ·
            refine ⟨13284635443995088278292225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17712847258660117704389633 13284635443995088278292225)
            ·
              refine ⟨9963476582996316208719169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13284635443995088278292225 9963476582996316208719169)
              ·
                refine ⟨7472607437247237156539377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9963476582996316208719169 7472607437247237156539377)
                ·
                  refine ⟨5604455577935427867404533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7472607437247237156539377 5604455577935427867404533)
                  ·
                    refine ⟨525417710431446362569175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5604455577935427867404533 525417710431446362569175)
                    ·
                      rfl

theorem cell22_1534871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_1534871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534871 prefixEnd_1534871 := by exact prefixLift 1534871
  have htrace : WordTrace (prefixWord ++ tailWord_1534871) baseStart_1534871 baseEnd_1534871 := by
    simpa [prefixWord, tailWord_1534871, baseEnd_1534871] using wordTrace_append hprefix tailTrace_1534871
  have hstable : (prefixWord ++ tailWord_1534871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534871).length < 2 ^ (prefixWord ++ tailWord_1534871).sum := by decide
  have hdescent : baseEnd_1534871 < baseStart_1534871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1534920 : List Nat := [2, 1, 3, 1, 5, 1, 1, 3, 1, 4]
def baseStart_1534920 : Nat := 118140960795 + 1534920 * 2 ^ 59
def prefixEnd_1534920 : Nat := 4983230072969 + 3 ^ 40 * 1534920 * 2
def baseEnd_1534920 : Nat := 525434484132826568094025

theorem tailTrace_1534920 : CollatzResearch.WordTrace tailWord_1534920 prefixEnd_1534920 525434484132826568094025 := by
  unfold tailWord_1534920
  simp only [CollatzResearch.WordTrace]
  refine ⟨27991565799627229155401107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37322087732836305540534809 27991565799627229155401107)
  ·
    refine ⟨41987348699440843733101661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27991565799627229155401107 41987348699440843733101661)
    ·
      refine ⟨15745255762290316399913123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41987348699440843733101661 15745255762290316399913123)
      ·
        refine ⟨23617883643435474599869685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15745255762290316399913123 23617883643435474599869685)
        ·
          refine ⟨2214176591572075743737783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23617883643435474599869685 2214176591572075743737783)
          ·
            refine ⟨3321264887358113615606675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214176591572075743737783 3321264887358113615606675)
            ·
              refine ⟨4981897331037170423410013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321264887358113615606675 4981897331037170423410013)
              ·
                refine ⟨1868211499138938908778755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4981897331037170423410013 1868211499138938908778755)
                ·
                  refine ⟨2802317248708408363168133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1868211499138938908778755 2802317248708408363168133)
                  ·
                    refine ⟨525434484132826568094025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2802317248708408363168133 525434484132826568094025)
                    ·
                      rfl

theorem cell22_1534920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_1534920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1534920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1534920 prefixEnd_1534920 := by exact prefixLift 1534920
  have htrace : WordTrace (prefixWord ++ tailWord_1534920) baseStart_1534920 baseEnd_1534920 := by
    simpa [prefixWord, tailWord_1534920, baseEnd_1534920] using wordTrace_append hprefix tailTrace_1534920
  have hstable : (prefixWord ++ tailWord_1534920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1534920).length < 2 ^ (prefixWord ++ tailWord_1534920).sum := by decide
  have hdescent : baseEnd_1534920 < baseStart_1534920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1534920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535046 : List Nat := [6, 1, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1535046 : Nat := 118140960795 + 1535046 * 2 ^ 59
def prefixEnd_1535046 : Nat := 4983230072969 + 3 ^ 40 * 1535046 * 2
def baseEnd_1535046 : Nat := 525477616507804239443639

theorem tailTrace_1535046 : CollatzResearch.WordTrace tailWord_1535046 prefixEnd_1535046 525477616507804239443639 := by
  unfold tailWord_1535046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749616474899936932184031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37325151464531987886592661 1749616474899936932184031)
  ·
    refine ⟨2624424712349905398276047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1749616474899936932184031 2624424712349905398276047)
    ·
      refine ⟨3936637068524858097414071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2624424712349905398276047 3936637068524858097414071)
      ·
        refine ⟨5904955602787287146121107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3936637068524858097414071 5904955602787287146121107)
        ·
          refine ⟨8857433404180930719181661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5904955602787287146121107 8857433404180930719181661)
          ·
            refine ⟨3321537526567849019693123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8857433404180930719181661 3321537526567849019693123)
            ·
              refine ⟨4982306289851773529539685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3321537526567849019693123 4982306289851773529539685)
              ·
                refine ⟨934182429347207536788691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4982306289851773529539685 934182429347207536788691)
                ·
                  refine ⟨1401273644020811305183037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 934182429347207536788691 1401273644020811305183037)
                  ·
                    refine ⟨525477616507804239443639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1401273644020811305183037 525477616507804239443639)
                    ·
                      rfl

theorem cell22_1535046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1535046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535046 prefixEnd_1535046 := by exact prefixLift 1535046
  have htrace : WordTrace (prefixWord ++ tailWord_1535046) baseStart_1535046 baseEnd_1535046 := by
    simpa [prefixWord, tailWord_1535046, baseEnd_1535046] using wordTrace_append hprefix tailTrace_1535046
  have hstable : (prefixWord ++ tailWord_1535046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535046).length < 2 ^ (prefixWord ++ tailWord_1535046).sum := by decide
  have hdescent : baseEnd_1535046 < baseStart_1535046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535085 : List Nat := [1, 5, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1535085 : Nat := 118140960795 + 1535085 * 2 ^ 59
def prefixEnd_1535085 : Nat := 4983230072969 + 3 ^ 40 * 1535085 * 2
def baseEnd_1535085 : Nat := 525490967004821137718519

theorem tailTrace_1535085 : CollatzResearch.WordTrace tailWord_1535085 prefixEnd_1535085 525490967004821137718519 := by
  unfold tailWord_1535085
  simp only [CollatzResearch.WordTrace]
  refine ⟨55989149643656691490558709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37326099762437794327039139 55989149643656691490558709)
  ·
    refine ⟨5248982779092814827239879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55989149643656691490558709 5248982779092814827239879)
    ·
      refine ⟨7873474168639222240859819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5248982779092814827239879 7873474168639222240859819)
      ·
        refine ⟨11810211252958833361289729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7873474168639222240859819 11810211252958833361289729)
        ·
          refine ⟨8857658439719125020967297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11810211252958833361289729 8857658439719125020967297)
          ·
            refine ⟨6643243829789343765725473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8857658439719125020967297 6643243829789343765725473)
            ·
              refine ⟨4982432872342007824294105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6643243829789343765725473 4982432872342007824294105)
              ·
                refine ⟨3736824654256505868220579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4982432872342007824294105 3736824654256505868220579)
                ·
                  refine ⟨5605236981384758802330869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736824654256505868220579 5605236981384758802330869)
                  ·
                    refine ⟨525490967004821137718519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5605236981384758802330869 525490967004821137718519)
                    ·
                      rfl

theorem cell22_1535085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1535085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535085 prefixEnd_1535085 := by exact prefixLift 1535085
  have htrace : WordTrace (prefixWord ++ tailWord_1535085) baseStart_1535085 baseEnd_1535085 := by
    simpa [prefixWord, tailWord_1535085, baseEnd_1535085] using wordTrace_append hprefix tailTrace_1535085
  have hstable : (prefixWord ++ tailWord_1535085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535085).length < 2 ^ (prefixWord ++ tailWord_1535085).sum := by decide
  have hdescent : baseEnd_1535085 < baseStart_1535085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535132 : List Nat := [2, 2, 3, 2, 1, 4, 2, 6]
def baseStart_1535132 : Nat := 118140960795 + 1535132 * 2 ^ 59
def prefixEnd_1535132 : Nat := 4983230072969 + 3 ^ 40 * 1535132 * 2
def baseEnd_1535132 : Nat := 58389672896147631310375

theorem tailTrace_1535132 : CollatzResearch.WordTrace tailWord_1535132 prefixEnd_1535132 58389672896147631310375 := by
  unfold tailWord_1535132
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995431937243209258759825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37327242582990945678346433 27995431937243209258759825)
  ·
    refine ⟨20996573952932406944069869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27995431937243209258759825 20996573952932406944069869)
    ·
      refine ⟨7873715232349652604026201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20996573952932406944069869 7873715232349652604026201)
      ·
        refine ⟨5905286424262239453019651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7873715232349652604026201 5905286424262239453019651)
        ·
          refine ⟨8857929636393359179529477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5905286424262239453019651 8857929636393359179529477)
          ·
            refine ⟨1660861806823754846161777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8857929636393359179529477 1660861806823754846161777)
            ·
              refine ⟨1245646355117816134621333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660861806823754846161777 1245646355117816134621333)
              ·
                refine ⟨58389672896147631310375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1245646355117816134621333 58389672896147631310375)
                ·
                  rfl

theorem cell22_1535132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 6].length) (baseStart_1535132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535132 prefixEnd_1535132 := by exact prefixLift 1535132
  have htrace : WordTrace (prefixWord ++ tailWord_1535132) baseStart_1535132 baseEnd_1535132 := by
    simpa [prefixWord, tailWord_1535132, baseEnd_1535132] using wordTrace_append hprefix tailTrace_1535132
  have hstable : (prefixWord ++ tailWord_1535132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535132).length < 2 ^ (prefixWord ++ tailWord_1535132).sum := by decide
  have hdescent : baseEnd_1535132 < baseStart_1535132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535164 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1535164 : Nat := 118140960795 + 1535164 * 2 ^ 59
def prefixEnd_1535164 : Nat := 4983230072969 + 3 ^ 40 * 1535164 * 2
def baseEnd_1535164 : Nat := 525518010319291264993277

theorem tailTrace_1535164 : CollatzResearch.WordTrace tailWord_1535164 prefixEnd_1535164 525518010319291264993277 := by
  unfold tailWord_1535164
  simp only [CollatzResearch.WordTrace]
  refine ⟨27996015505185243991342273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37328020673580325321789697 27996015505185243991342273)
  ·
    refine ⟨20997011628888932993506705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27996015505185243991342273 20997011628888932993506705)
    ·
      refine ⟨15747758721666699745130029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20997011628888932993506705 15747758721666699745130029)
      ·
        refine ⟨5905409520625012404423761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15747758721666699745130029 5905409520625012404423761)
        ·
          refine ⟨4429057140468759303317821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5905409520625012404423761 4429057140468759303317821)
          ·
            refine ⟨1660896427675784738744183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4429057140468759303317821 1660896427675784738744183)
            ·
              refine ⟨2491344641513677108116275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660896427675784738744183 2491344641513677108116275)
              ·
                refine ⟨3737016962270515662174413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491344641513677108116275 3737016962270515662174413)
                ·
                  refine ⟨1401381360851443373315405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3737016962270515662174413 1401381360851443373315405)
                  ·
                    refine ⟨525518010319291264993277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1401381360851443373315405 525518010319291264993277)
                    ·
                      rfl

theorem cell22_1535164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1535164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535164 prefixEnd_1535164 := by exact prefixLift 1535164
  have htrace : WordTrace (prefixWord ++ tailWord_1535164) baseStart_1535164 baseEnd_1535164 := by
    simpa [prefixWord, tailWord_1535164, baseEnd_1535164] using wordTrace_append hprefix tailTrace_1535164
  have hstable : (prefixWord ++ tailWord_1535164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535164).length < 2 ^ (prefixWord ++ tailWord_1535164).sum := by decide
  have hdescent : baseEnd_1535164 < baseStart_1535164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535170 : List Nat := [3, 5, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1535170 : Nat := 118140960795 + 1535170 * 2 ^ 59
def prefixEnd_1535170 : Nat := 4983230072969 + 3 ^ 40 * 1535170 * 2
def baseEnd_1535170 : Nat := 525520064241909249343259

theorem tailTrace_1535170 : CollatzResearch.WordTrace tailWord_1535170 prefixEnd_1535170 525520064241909249343259 := by
  unfold tailWord_1535170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998062462087187751850741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37328166565565834004935309 13998062462087187751850741)
  ·
    refine ⟨1312318355820673851736007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13998062462087187751850741 1312318355820673851736007)
    ·
      refine ⟨1968477533731010777604011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312318355820673851736007 1968477533731010777604011)
      ·
        refine ⟨2952716300596516166406017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968477533731010777604011 2952716300596516166406017)
        ·
          refine ⟨2214537225447387124804513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2952716300596516166406017 2214537225447387124804513)
          ·
            refine ⟨1660902919085540343603385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2214537225447387124804513 1660902919085540343603385)
            ·
              refine ⟨1245677189314155257702539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660902919085540343603385 1245677189314155257702539)
              ·
                refine ⟨1868515783971232886553809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245677189314155257702539 1868515783971232886553809)
                ·
                  refine ⟨1401386837978424664915357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868515783971232886553809 1401386837978424664915357)
                  ·
                    refine ⟨525520064241909249343259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1401386837978424664915357 525520064241909249343259)
                    ·
                      rfl

theorem cell22_1535170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1535170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535170 prefixEnd_1535170 := by exact prefixLift 1535170
  have htrace : WordTrace (prefixWord ++ tailWord_1535170) baseStart_1535170 baseEnd_1535170 := by
    simpa [prefixWord, tailWord_1535170, baseEnd_1535170] using wordTrace_append hprefix tailTrace_1535170
  have hstable : (prefixWord ++ tailWord_1535170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535170).length < 2 ^ (prefixWord ++ tailWord_1535170).sum := by decide
  have hdescent : baseEnd_1535170 < baseStart_1535170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535173 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 8]
def baseStart_1535173 : Nat := 118140960795 + 1535173 * 2 ^ 59
def prefixEnd_1535173 : Nat := 4983230072969 + 3 ^ 40 * 1535173 * 2
def baseEnd_1535173 : Nat := 525521091203218241518249

theorem tailTrace_1535173 : CollatzResearch.WordTrace tailWord_1535173 prefixEnd_1535173 525521091203218241518249 := by
  unfold tailWord_1535173
  simp only [CollatzResearch.WordTrace]
  refine ⟨55992359267337882519762173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37328239511558588346508115 55992359267337882519762173)
  ·
    refine ⟨20997134725251705944910815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55992359267337882519762173 20997134725251705944910815)
    ·
      refine ⟨31495702087877558917366223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20997134725251705944910815 31495702087877558917366223)
      ·
        refine ⟨47243553131816338376049335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31495702087877558917366223 47243553131816338376049335)
        ·
          refine ⟨70865329697724507564074003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47243553131816338376049335 70865329697724507564074003)
          ·
            refine ⟨106297994546586761346111005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70865329697724507564074003 106297994546586761346111005)
            ·
              refine ⟨39861747954970035504791627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106297994546586761346111005 39861747954970035504791627)
              ·
                refine ⟨59792621932455053257187441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39861747954970035504791627 59792621932455053257187441)
                ·
                  refine ⟨44844466449341289942890581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59792621932455053257187441 44844466449341289942890581)
                  ·
                    refine ⟨525521091203218241518249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44844466449341289942890581 525521091203218241518249)
                    ·
                      rfl

theorem cell22_1535173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_1535173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535173 prefixEnd_1535173 := by exact prefixLift 1535173
  have htrace : WordTrace (prefixWord ++ tailWord_1535173) baseStart_1535173 baseEnd_1535173 := by
    simpa [prefixWord, tailWord_1535173, baseEnd_1535173] using wordTrace_append hprefix tailTrace_1535173
  have hstable : (prefixWord ++ tailWord_1535173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535173).length < 2 ^ (prefixWord ++ tailWord_1535173).sum := by decide
  have hdescent : baseEnd_1535173 < baseStart_1535173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535237 : List Nat := [1, 3, 1, 1, 2, 1, 3, 5, 2, 3]
def baseStart_1535237 : Nat := 118140960795 + 1535237 * 2 ^ 59
def prefixEnd_1535237 : Nat := 4983230072969 + 3 ^ 40 * 1535237 * 2
def baseEnd_1535237 : Nat := 525542999711143407918053

theorem tailTrace_1535237 : CollatzResearch.WordTrace tailWord_1535237 prefixEnd_1535237 525542999711143407918053 := by
  unfold tailWord_1535237
  simp only [CollatzResearch.WordTrace]
  refine ⟨55994693539106021450091965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37329795692737347633394643 55994693539106021450091965)
  ·
    refine ⟨20998010077164758043784487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55994693539106021450091965 20998010077164758043784487)
    ·
      refine ⟨31497015115747137065676731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20998010077164758043784487 31497015115747137065676731)
      ·
        refine ⟨47245522673620705598515097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31497015115747137065676731 47245522673620705598515097)
        ·
          refine ⟨35434142005215529198886323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47245522673620705598515097 35434142005215529198886323)
          ·
            refine ⟨53151213007823293798329485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35434142005215529198886323 53151213007823293798329485)
            ·
              refine ⟨19931704877933735174373557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53151213007823293798329485 19931704877933735174373557)
              ·
                refine ⟨1868597332306287672597521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19931704877933735174373557 1868597332306287672597521)
                ·
                  refine ⟨1401447999229715754448141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868597332306287672597521 1401447999229715754448141)
                  ·
                    refine ⟨525542999711143407918053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1401447999229715754448141 525542999711143407918053)
                    ·
                      rfl

theorem cell22_1535237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_1535237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535237 prefixEnd_1535237 := by exact prefixLift 1535237
  have htrace : WordTrace (prefixWord ++ tailWord_1535237) baseStart_1535237 baseEnd_1535237 := by
    simpa [prefixWord, tailWord_1535237, baseEnd_1535237] using wordTrace_append hprefix tailTrace_1535237
  have hstable : (prefixWord ++ tailWord_1535237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535237).length < 2 ^ (prefixWord ++ tailWord_1535237).sum := by decide
  have hdescent : baseEnd_1535237 < baseStart_1535237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535318 : List Nat := [5, 2, 3, 1, 1, 2, 8]
def baseStart_1535318 : Nat := 118140960795 + 1535318 * 2 ^ 59
def prefixEnd_1535318 : Nat := 4983230072969 + 3 ^ 40 * 1535318 * 2
def baseEnd_1535318 : Nat := 19465582506166155431215

theorem tailTrace_1535318 : CollatzResearch.WordTrace tailWord_1535318 prefixEnd_1535318 19465582506166155431215 := by
  unfold tailWord_1535318
  simp only [CollatzResearch.WordTrace]
  refine ⟨3499852990738285767736913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37331765234541714855860405 3499852990738285767736913)
  ·
    refine ⟨2624889743053714325802685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3499852990738285767736913 2624889743053714325802685)
    ·
      refine ⟨984333653645142872176007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2624889743053714325802685 984333653645142872176007)
      ·
        refine ⟨1476500480467714308264011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984333653645142872176007 1476500480467714308264011)
        ·
          refine ⟨2214750720701571462396017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476500480467714308264011 2214750720701571462396017)
          ·
            refine ⟨1661063040526178596797013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2214750720701571462396017 1661063040526178596797013)
            ·
              refine ⟨19465582506166155431215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1661063040526178596797013 19465582506166155431215)
              ·
                rfl

theorem cell22_1535318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 8].length) (baseStart_1535318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535318 prefixEnd_1535318 := by exact prefixLift 1535318
  have htrace : WordTrace (prefixWord ++ tailWord_1535318) baseStart_1535318 baseEnd_1535318 := by
    simpa [prefixWord, tailWord_1535318, baseEnd_1535318] using wordTrace_append hprefix tailTrace_1535318
  have hstable : (prefixWord ++ tailWord_1535318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535318).length < 2 ^ (prefixWord ++ tailWord_1535318).sum := by decide
  have hdescent : baseEnd_1535318 < baseStart_1535318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535372 : List Nat := [2, 2, 1, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1535372 : Nat := 118140960795 + 1535372 * 2 ^ 59
def prefixEnd_1535372 : Nat := 4983230072969 + 3 ^ 40 * 1535372 * 2
def baseEnd_1535372 : Nat := 525589212970048055792639

theorem tailTrace_1535372 : CollatzResearch.WordTrace tailWord_1535372 prefixEnd_1535372 525589212970048055792639 := by
  unfold tailWord_1535372
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999808696808469753128185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37333078262411293004170913 27999808696808469753128185)
  ·
    refine ⟨20999856522606352314846139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27999808696808469753128185 20999856522606352314846139)
    ·
      refine ⟨31499784783909528472269209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20999856522606352314846139 31499784783909528472269209)
      ·
        refine ⟨23624838587932146354201907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31499784783909528472269209 23624838587932146354201907)
        ·
          refine ⟨35437257881898219531302861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23624838587932146354201907 35437257881898219531302861)
          ·
            refine ⟨13288971705711832324238573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35437257881898219531302861 13288971705711832324238573)
            ·
              refine ⟨4983364389641937121589465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13288971705711832324238573 4983364389641937121589465)
              ·
                refine ⟨3737523292231452841192099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983364389641937121589465 3737523292231452841192099)
                ·
                  refine ⟨5606284938347179261788149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737523292231452841192099 5606284938347179261788149)
                  ·
                    refine ⟨525589212970048055792639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5606284938347179261788149 525589212970048055792639)
                    ·
                      rfl

theorem cell22_1535372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1535372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535372 prefixEnd_1535372 := by exact prefixLift 1535372
  have htrace : WordTrace (prefixWord ++ tailWord_1535372) baseStart_1535372 baseEnd_1535372 := by
    simpa [prefixWord, tailWord_1535372, baseEnd_1535372] using wordTrace_append hprefix tailTrace_1535372
  have hstable : (prefixWord ++ tailWord_1535372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535372).length < 2 ^ (prefixWord ++ tailWord_1535372).sum := by decide
  have hdescent : baseEnd_1535372 < baseStart_1535372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535385 : List Nat := [1, 2, 1, 2, 1, 15]
def baseStart_1535385 : Nat := 118140960795 + 1535385 * 2 ^ 59
def prefixEnd_1535385 : Nat := 4983230072969 + 3 ^ 40 * 1535385 * 2
def baseEnd_1535385 : Nat := 6488810655996547595279

theorem tailTrace_1535385 : CollatzResearch.WordTrace tailWord_1535385 prefixEnd_1535385 6488810655996547595279 := by
  unfold tailWord_1535385
  simp only [CollatzResearch.WordTrace]
  refine ⟨56000091542569842726479609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37333394361713228484319739 56000091542569842726479609)
  ·
    refine ⟨42000068656927382044859707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56000091542569842726479609 42000068656927382044859707)
    ·
      refine ⟨63000102985391073067289561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42000068656927382044859707 63000102985391073067289561)
      ·
        refine ⟨47250077239043304800467171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63000102985391073067289561 47250077239043304800467171)
        ·
          refine ⟨70875115858564957200700757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47250077239043304800467171 70875115858564957200700757)
          ·
            refine ⟨6488810655996547595279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 70875115858564957200700757 6488810655996547595279)
            ·
              rfl

theorem cell22_1535385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 15].length) (baseStart_1535385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535385 prefixEnd_1535385 := by exact prefixLift 1535385
  have htrace : WordTrace (prefixWord ++ tailWord_1535385) baseStart_1535385 baseEnd_1535385 := by
    simpa [prefixWord, tailWord_1535385, baseEnd_1535385] using wordTrace_append hprefix tailTrace_1535385
  have hstable : (prefixWord ++ tailWord_1535385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535385).length < 2 ^ (prefixWord ++ tailWord_1535385).sum := by decide
  have hdescent : baseEnd_1535385 < baseStart_1535385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535391 : List Nat := [1, 1, 2, 5, 1, 2, 4, 2, 4]
def baseStart_1535391 : Nat := 118140960795 + 1535391 * 2 ^ 59
def prefixEnd_1535391 : Nat := 4983230072969 + 3 ^ 40 * 1535391 * 2
def baseEnd_1535391 : Nat := 175198572352779446522527

theorem tailTrace_1535391 : CollatzResearch.WordTrace tailWord_1535391 prefixEnd_1535391 175198572352779446522527 := by
  unfold tailWord_1535391
  simp only [CollatzResearch.WordTrace]
  refine ⟨56000310380548105751198027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37333540253698737167465351 56000310380548105751198027)
  ·
    refine ⟨84000465570822158626797041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56000310380548105751198027 84000465570822158626797041)
    ·
      refine ⟨63000349178116618970097781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84000465570822158626797041 63000349178116618970097781)
      ·
        refine ⟨5906282735448433028446667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63000349178116618970097781 5906282735448433028446667)
        ·
          refine ⟨8859424103172649542670001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5906282735448433028446667 8859424103172649542670001)
          ·
            refine ⟨6644568077379487157002501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8859424103172649542670001 6644568077379487157002501)
            ·
              refine ⟨1245856514508653841937969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6644568077379487157002501 1245856514508653841937969)
              ·
                refine ⟨934392385881490381453477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245856514508653841937969 934392385881490381453477)
                ·
                  refine ⟨175198572352779446522527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 934392385881490381453477 175198572352779446522527)
                  ·
                    rfl

theorem cell22_1535391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 4].length) (baseStart_1535391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535391 prefixEnd_1535391 := by exact prefixLift 1535391
  have htrace : WordTrace (prefixWord ++ tailWord_1535391) baseStart_1535391 baseEnd_1535391 := by
    simpa [prefixWord, tailWord_1535391, baseEnd_1535391] using wordTrace_append hprefix tailTrace_1535391
  have hstable : (prefixWord ++ tailWord_1535391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535391).length < 2 ^ (prefixWord ++ tailWord_1535391).sum := by decide
  have hdescent : baseEnd_1535391 < baseStart_1535391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
