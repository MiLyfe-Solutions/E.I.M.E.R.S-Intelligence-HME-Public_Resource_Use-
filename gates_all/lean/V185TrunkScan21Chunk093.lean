import V185TrunkScan21Chunk092

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1127185 : List Nat := [1, 2, 2, 1, 1, 3, 5, 6]
def baseStart_1127185 : Nat := 118140960795 + 1127185 * 2 ^ 59
def prefixEnd_1127185 : Nat := 4983230072969 + 3 ^ 40 * 1127185 * 2
def baseEnd_1127185 : Nat := 85746324672337424770915

theorem tailTrace_1127185 : CollatzResearch.WordTrace tailWord_1127185 prefixEnd_1127185 85746324672337424770915 := by
  unfold tailWord_1127185
  simp only [CollatzResearch.WordTrace]
  refine ⟨41111814421408727716775009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27407876280939151811183339 41111814421408727716775009)
  ·
    refine ⟨30833860816056545787581257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41111814421408727716775009 30833860816056545787581257)
    ·
      refine ⟨23125395612042409340685943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30833860816056545787581257 23125395612042409340685943)
      ·
        refine ⟨34688093418063614011028915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23125395612042409340685943 34688093418063614011028915)
        ·
          refine ⟨52032140127095421016543373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34688093418063614011028915 52032140127095421016543373)
          ·
            refine ⟨19512052547660782881203765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52032140127095421016543373 19512052547660782881203765)
            ·
              refine ⟨1829254926343198395112853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19512052547660782881203765 1829254926343198395112853)
              ·
                refine ⟨85746324672337424770915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1829254926343198395112853 85746324672337424770915)
                ·
                  rfl

theorem cell21_1127185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 6].length) (baseStart_1127185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127185 prefixEnd_1127185 := by exact prefixLift 1127185
  have htrace : WordTrace (prefixWord ++ tailWord_1127185) baseStart_1127185 baseEnd_1127185 := by
    simpa [prefixWord, tailWord_1127185, baseEnd_1127185] using wordTrace_append hprefix tailTrace_1127185
  have hstable : (prefixWord ++ tailWord_1127185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127185).length < 2 ^ (prefixWord ++ tailWord_1127185).sum := by decide
  have hdescent : baseEnd_1127185 < baseStart_1127185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127222 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1127222 : Nat := 118140960795 + 1127222 * 2 ^ 59
def prefixEnd_1127222 : Nat := 4983230072969 + 3 ^ 40 * 1127222 * 2
def baseEnd_1127222 : Nat := 257247417921108432196003

theorem tailTrace_1127222 : CollatzResearch.WordTrace tailWord_1127222 prefixEnd_1127222 257247417921108432196003 := by
  unfold tailWord_1127222
  simp only [CollatzResearch.WordTrace]
  refine ⟨2569572745142167689741995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27408775948183122023914613 2569572745142167689741995)
  ·
    refine ⟨3854359117713251534612993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2569572745142167689741995 3854359117713251534612993)
    ·
      refine ⟨2890769338284938650959745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3854359117713251534612993 2890769338284938650959745)
      ·
        refine ⟨2168077003713703988219809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2890769338284938650959745 2168077003713703988219809)
        ·
          refine ⟨1626057752785277991164857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2168077003713703988219809 1626057752785277991164857)
          ·
            refine ⟨1219543314588958493373643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1626057752785277991164857 1219543314588958493373643)
            ·
              refine ⟨1829314971883437740060465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219543314588958493373643 1829314971883437740060465)
              ·
                refine ⟨1371986228912578305045349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1829314971883437740060465 1371986228912578305045349)
                ·
                  refine ⟨257247417921108432196003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1371986228912578305045349 257247417921108432196003)
                  ·
                    rfl

theorem cell21_1127222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1127222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127222 prefixEnd_1127222 := by exact prefixLift 1127222
  have htrace : WordTrace (prefixWord ++ tailWord_1127222) baseStart_1127222 baseEnd_1127222 := by
    simpa [prefixWord, tailWord_1127222, baseEnd_1127222] using wordTrace_append hprefix tailTrace_1127222
  have hstable : (prefixWord ++ tailWord_1127222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127222).length < 2 ^ (prefixWord ++ tailWord_1127222).sum := by decide
  have hdescent : baseEnd_1127222 < baseStart_1127222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127275 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 7]
def baseStart_1127275 : Nat := 118140960795 + 1127275 * 2 ^ 59
def prefixEnd_1127275 : Nat := 4983230072969 + 3 ^ 40 * 1127275 * 2
def baseEnd_1127275 : Nat := 257259513243192117812561

theorem tailTrace_1127275 : CollatzResearch.WordTrace tailWord_1127275 prefixEnd_1127275 257259513243192117812561 := by
  unfold tailWord_1127275
  simp only [CollatzResearch.WordTrace]
  refine ⟨41115096991082673087551279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27410064660721782058367519 41115096991082673087551279)
  ·
    refine ⟨61672645486624009631326919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41115096991082673087551279 61672645486624009631326919)
    ·
      refine ⟨92508968229936014446990379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61672645486624009631326919 92508968229936014446990379)
      ·
        refine ⟨138763452344904021670485569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92508968229936014446990379 138763452344904021670485569)
        ·
          refine ⟨104072589258678016252864177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 138763452344904021670485569 104072589258678016252864177)
          ·
            refine ⟨78054441944008512189648133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104072589258678016252864177 78054441944008512189648133)
            ·
              refine ⟨14635207864501596035559025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78054441944008512189648133 14635207864501596035559025)
              ·
                refine ⟨10976405898376197026669269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14635207864501596035559025 10976405898376197026669269)
                ·
                  refine ⟨257259513243192117812561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10976405898376197026669269 257259513243192117812561)
                  ·
                    rfl

theorem cell21_1127275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_1127275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127275 prefixEnd_1127275 := by exact prefixLift 1127275
  have htrace : WordTrace (prefixWord ++ tailWord_1127275) baseStart_1127275 baseEnd_1127275 := by
    simpa [prefixWord, tailWord_1127275, baseEnd_1127275] using wordTrace_append hprefix tailTrace_1127275
  have hstable : (prefixWord ++ tailWord_1127275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127275).length < 2 ^ (prefixWord ++ tailWord_1127275).sum := by decide
  have hdescent : baseEnd_1127275 < baseStart_1127275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127298 : List Nat := [3, 4, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1127298 : Nat := 118140960795 + 1127298 * 2 ^ 59
def prefixEnd_1127298 : Nat := 4983230072969 + 3 ^ 40 * 1127298 * 2
def baseEnd_1127298 : Nat := 257264762156549188929181

theorem tailTrace_1127298 : CollatzResearch.WordTrace tailWord_1127298 prefixEnd_1127298 257264762156549188929181 := by
  unfold tailWord_1127298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10278983967499837003909637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27410623913332898677092365 10278983967499837003909637)
  ·
    refine ⟨1927309493906219438233057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10278983967499837003909637 1927309493906219438233057)
    ·
      refine ⟨1445482120429664578674793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1927309493906219438233057 1445482120429664578674793)
      ·
        refine ⟨1084111590322248434006095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1445482120429664578674793 1084111590322248434006095)
        ·
          refine ⟨1626167385483372651009143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1084111590322248434006095 1626167385483372651009143)
          ·
            refine ⟨2439251078225058976513715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1626167385483372651009143 2439251078225058976513715)
            ·
              refine ⟨3658876617337588464770573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439251078225058976513715 3658876617337588464770573)
              ·
                refine ⟨1372078731501595674288965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3658876617337588464770573 1372078731501595674288965)
                ·
                  refine ⟨257264762156549188929181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1372078731501595674288965 257264762156549188929181)
                  ·
                    rfl

theorem cell21_1127298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1127298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127298 prefixEnd_1127298 := by exact prefixLift 1127298
  have htrace : WordTrace (prefixWord ++ tailWord_1127298) baseStart_1127298 baseEnd_1127298 := by
    simpa [prefixWord, tailWord_1127298, baseEnd_1127298] using wordTrace_append hprefix tailTrace_1127298
  have hstable : (prefixWord ++ tailWord_1127298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127298).length < 2 ^ (prefixWord ++ tailWord_1127298).sum := by decide
  have hdescent : baseEnd_1127298 < baseStart_1127298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127385 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 3]
def baseStart_1127385 : Nat := 118140960795 + 1127385 * 2 ^ 59
def prefixEnd_1127385 : Nat := 4983230072969 + 3 ^ 40 * 1127385 * 2
def baseEnd_1127385 : Nat := 257284616741856370979003

theorem tailTrace_1127385 : CollatzResearch.WordTrace tailWord_1127385 prefixEnd_1127385 257284616741856370979003 := by
  unfold tailWord_1127385
  simp only [CollatzResearch.WordTrace]
  refine ⟨41119109020684161874055609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27412739347122774582703739 41119109020684161874055609)
  ·
    refine ⟨30839331765513121405541707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41119109020684161874055609 30839331765513121405541707)
    ·
      refine ⟨46258997648269682108312561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30839331765513121405541707 46258997648269682108312561)
      ·
        refine ⟨34694248236202261581234421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46258997648269682108312561 34694248236202261581234421)
        ·
          refine ⟨3252585772143962023240727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34694248236202261581234421 3252585772143962023240727)
          ·
            refine ⟨4878878658215943034861091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3252585772143962023240727 4878878658215943034861091)
            ·
              refine ⟨7318317987323914552291637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4878878658215943034861091 7318317987323914552291637)
              ·
                refine ⟨686092311311616989277341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7318317987323914552291637 686092311311616989277341)
                ·
                  refine ⟨257284616741856370979003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686092311311616989277341 257284616741856370979003)
                  ·
                    rfl

theorem cell21_1127385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 3].length) (baseStart_1127385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127385 prefixEnd_1127385 := by exact prefixLift 1127385
  have htrace : WordTrace (prefixWord ++ tailWord_1127385) baseStart_1127385 baseEnd_1127385 := by
    simpa [prefixWord, tailWord_1127385, baseEnd_1127385] using wordTrace_append hprefix tailTrace_1127385
  have hstable : (prefixWord ++ tailWord_1127385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127385).length < 2 ^ (prefixWord ++ tailWord_1127385).sum := by decide
  have hdescent : baseEnd_1127385 < baseStart_1127385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127399 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 6]
def baseStart_1127399 : Nat := 118140960795 + 1127399 * 2 ^ 59
def prefixEnd_1127399 : Nat := 4983230072969 + 3 ^ 40 * 1127399 * 2
def baseEnd_1127399 : Nat := 257287811732595457745641

theorem tailTrace_1127399 : CollatzResearch.WordTrace tailWord_1127399 prefixEnd_1127399 257287811732595457745641 := by
  unfold tailWord_1127399
  simp only [CollatzResearch.WordTrace]
  refine ⟨41119619642633442265065251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27413079761755628176710167 41119619642633442265065251)
  ·
    refine ⟨61679429463950163397597877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41119619642633442265065251 61679429463950163397597877)
    ·
      refine ⟨5782446512245327818524801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61679429463950163397597877 5782446512245327818524801)
      ·
        refine ⟨4336834884183995863893601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5782446512245327818524801 4336834884183995863893601)
        ·
          refine ⟨3252626163137996897920201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4336834884183995863893601 3252626163137996897920201)
          ·
            refine ⟨2439469622353497673440151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3252626163137996897920201 2439469622353497673440151)
            ·
              refine ⟨3659204433530246510160227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2439469622353497673440151 3659204433530246510160227)
              ·
                refine ⟨5488806650295369765240341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3659204433530246510160227 5488806650295369765240341)
                ·
                  refine ⟨257287811732595457745641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5488806650295369765240341 257287811732595457745641)
                  ·
                    rfl

theorem cell21_1127399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_1127399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127399 prefixEnd_1127399 := by exact prefixLift 1127399
  have htrace : WordTrace (prefixWord ++ tailWord_1127399) baseStart_1127399 baseEnd_1127399 := by
    simpa [prefixWord, tailWord_1127399, baseEnd_1127399] using wordTrace_append hprefix tailTrace_1127399
  have hstable : (prefixWord ++ tailWord_1127399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127399).length < 2 ^ (prefixWord ++ tailWord_1127399).sum := by decide
  have hdescent : baseEnd_1127399 < baseStart_1127399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127613 : List Nat := [1, 4, 1, 2, 1, 1, 5, 3, 3]
def baseStart_1127613 : Nat := 118140960795 + 1127613 * 2 ^ 59
def prefixEnd_1127613 : Nat := 4983230072969 + 3 ^ 40 * 1127613 * 2
def baseEnd_1127613 : Nat := 257336649448178641178537

theorem tailTrace_1127613 : CollatzResearch.WordTrace tailWord_1127613 prefixEnd_1127613 257336649448178641178537 := by
  unfold tailWord_1127613
  simp only [CollatzResearch.WordTrace]
  refine ⟨41127424863858156813355493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27418283242572104542236995 41127424863858156813355493)
  ·
    refine ⟨7711392161973404402504155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41127424863858156813355493 7711392161973404402504155)
    ·
      refine ⟨11567088242960106603756233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711392161973404402504155 11567088242960106603756233)
      ·
        refine ⟨8675316182220079952817175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11567088242960106603756233 8675316182220079952817175)
        ·
          refine ⟨13012974273330119929225763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8675316182220079952817175 13012974273330119929225763)
          ·
            refine ⟨19519461409995179893838645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13012974273330119929225763 19519461409995179893838645)
            ·
              refine ⟨1829949507187048115047373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19519461409995179893838645 1829949507187048115047373)
              ·
                refine ⟨686231065195143043142765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1829949507187048115047373 686231065195143043142765)
                ·
                  refine ⟨257336649448178641178537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686231065195143043142765 257336649448178641178537)
                  ·
                    rfl

theorem cell21_1127613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 3, 3].length) (baseStart_1127613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127613 prefixEnd_1127613 := by exact prefixLift 1127613
  have htrace : WordTrace (prefixWord ++ tailWord_1127613) baseStart_1127613 baseEnd_1127613 := by
    simpa [prefixWord, tailWord_1127613, baseEnd_1127613] using wordTrace_append hprefix tailTrace_1127613
  have hstable : (prefixWord ++ tailWord_1127613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127613).length < 2 ^ (prefixWord ++ tailWord_1127613).sum := by decide
  have hdescent : baseEnd_1127613 < baseStart_1127613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127624 : List Nat := [2, 1, 3, 1, 2, 1, 11]
def baseStart_1127624 : Nat := 118140960795 + 1127624 * 2 ^ 59
def prefixEnd_1127624 : Nat := 4983230072969 + 3 ^ 40 * 1127624 * 2
def baseEnd_1127624 : Nat := 28593239977560562943909

theorem tailTrace_1127624 : CollatzResearch.WordTrace tailWord_1127624 prefixEnd_1127624 28593239977560562943909 := by
  unfold tailWord_1127624
  simp only [CollatzResearch.WordTrace]
  refine ⟨20563913033409152846002963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27418550711212203794670617 20563913033409152846002963)
  ·
    refine ⟨30845869550113729269004445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20563913033409152846002963 30845869550113729269004445)
    ·
      refine ⟨11567201081292648475876667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30845869550113729269004445 11567201081292648475876667)
      ·
        refine ⟨17350801621938972713815001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11567201081292648475876667 17350801621938972713815001)
        ·
          refine ⟨13013101216454229535361251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17350801621938972713815001 13013101216454229535361251)
          ·
            refine ⟨19519651824681344303041877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13013101216454229535361251 19519651824681344303041877)
            ·
              refine ⟨28593239977560562943909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19519651824681344303041877 28593239977560562943909)
              ·
                rfl

theorem cell21_1127624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 11].length) (baseStart_1127624 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127624 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127624 prefixEnd_1127624 := by exact prefixLift 1127624
  have htrace : WordTrace (prefixWord ++ tailWord_1127624) baseStart_1127624 baseEnd_1127624 := by
    simpa [prefixWord, tailWord_1127624, baseEnd_1127624] using wordTrace_append hprefix tailTrace_1127624
  have hstable : (prefixWord ++ tailWord_1127624).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127624).length < 2 ^ (prefixWord ++ tailWord_1127624).sum := by decide
  have hdescent : baseEnd_1127624 < baseStart_1127624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127630 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_1127630 : Nat := 118140960795 + 1127630 * 2 ^ 59
def prefixEnd_1127630 : Nat := 4983230072969 + 3 ^ 40 * 1127630 * 2
def baseEnd_1127630 : Nat := 257340529079790389395169

theorem tailTrace_1127630 : CollatzResearch.WordTrace tailWord_1127630 prefixEnd_1127630 257340529079790389395169 := by
  unfold tailWord_1127630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141005613099571089590543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27418696603197712477816229 5141005613099571089590543)
  ·
    refine ⟨7711508419649356634385815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5141005613099571089590543 7711508419649356634385815)
    ·
      refine ⟨11567262629474034951578723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7711508419649356634385815 11567262629474034951578723)
      ·
        refine ⟨17350893944211052427368085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11567262629474034951578723 17350893944211052427368085)
        ·
          refine ⟨813323153634893082532879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17350893944211052427368085 813323153634893082532879)
          ·
            refine ⟨1219984730452339623799319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813323153634893082532879 1219984730452339623799319)
            ·
              refine ⟨1829977095678509435698979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1219984730452339623799319 1829977095678509435698979)
              ·
                refine ⟨2744965643517764153548469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1829977095678509435698979 2744965643517764153548469)
                ·
                  refine ⟨257340529079790389395169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2744965643517764153548469 257340529079790389395169)
                  ·
                    rfl

theorem cell21_1127630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_1127630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127630 prefixEnd_1127630 := by exact prefixLift 1127630
  have htrace : WordTrace (prefixWord ++ tailWord_1127630) baseStart_1127630 baseEnd_1127630 := by
    simpa [prefixWord, tailWord_1127630, baseEnd_1127630] using wordTrace_append hprefix tailTrace_1127630
  have hstable : (prefixWord ++ tailWord_1127630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127630).length < 2 ^ (prefixWord ++ tailWord_1127630).sum := by decide
  have hdescent : baseEnd_1127630 < baseStart_1127630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127737 : List Nat := [1, 2, 1, 6, 3, 1, 1, 2, 4]
def baseStart_1127737 : Nat := 118140960795 + 1127737 * 2 ^ 59
def prefixEnd_1127737 : Nat := 4983230072969 + 3 ^ 40 * 1127737 * 2
def baseEnd_1127737 : Nat := 257364947937581981111617

theorem tailTrace_1127737 : CollatzResearch.WordTrace tailWord_1127737 prefixEnd_1127737 257364947937581981111617 := by
  unfold tailWord_1127737
  simp only [CollatzResearch.WordTrace]
  refine ⟨41131947515408925990869465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27421298343605950660579643 41131947515408925990869465)
  ·
    refine ⟨30848960636556694493152099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41131947515408925990869465 30848960636556694493152099)
    ·
      refine ⟨46273440954835041739728149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30848960636556694493152099 46273440954835041739728149)
      ·
        refine ⟨2169067544757892581549757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46273440954835041739728149 2169067544757892581549757)
        ·
          refine ⟨813400329284209718081159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2169067544757892581549757 813400329284209718081159)
          ·
            refine ⟨1220100493926314577121739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813400329284209718081159 1220100493926314577121739)
            ·
              refine ⟨1830150740889471865682609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220100493926314577121739 1830150740889471865682609)
              ·
                refine ⟨1372613055667103899261957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1830150740889471865682609 1372613055667103899261957)
                ·
                  refine ⟨257364947937581981111617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1372613055667103899261957 257364947937581981111617)
                  ·
                    rfl

theorem cell21_1127737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 2, 4].length) (baseStart_1127737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127737 prefixEnd_1127737 := by exact prefixLift 1127737
  have htrace : WordTrace (prefixWord ++ tailWord_1127737) baseStart_1127737 baseEnd_1127737 := by
    simpa [prefixWord, tailWord_1127737, baseEnd_1127737] using wordTrace_append hprefix tailTrace_1127737
  have hstable : (prefixWord ++ tailWord_1127737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127737).length < 2 ^ (prefixWord ++ tailWord_1127737).sum := by decide
  have hdescent : baseEnd_1127737 < baseStart_1127737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127810 : List Nat := [3, 4, 2, 1, 1, 1, 1, 8]
def baseStart_1127810 : Nat := 118140960795 + 1127810 * 2 ^ 59
def prefixEnd_1127810 : Nat := 4983230072969 + 3 ^ 40 * 1127810 * 2
def baseEnd_1127810 : Nat := 85793869177383358798267

theorem tailTrace_1127810 : CollatzResearch.WordTrace tailWord_1127810 prefixEnd_1127810 85793869177383358798267 := by
  unfold tailWord_1127810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10283652511036114864569221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27423073362762972972184589 10283652511036114864569221)
  ·
    refine ⟨1928184845819271537106729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10283652511036114864569221 1928184845819271537106729)
    ·
      refine ⟨1446138634364453652830047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1928184845819271537106729 1446138634364453652830047)
      ·
        refine ⟨2169207951546680479245071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446138634364453652830047 2169207951546680479245071)
        ·
          refine ⟨3253811927320020718867607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2169207951546680479245071 3253811927320020718867607)
          ·
            refine ⟨4880717890980031078301411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3253811927320020718867607 4880717890980031078301411)
            ·
              refine ⟨7321076836470046617452117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4880717890980031078301411 7321076836470046617452117)
              ·
                refine ⟨85793869177383358798267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7321076836470046617452117 85793869177383358798267)
                ·
                  rfl

theorem cell21_1127810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_1127810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127810 prefixEnd_1127810 := by exact prefixLift 1127810
  have htrace : WordTrace (prefixWord ++ tailWord_1127810) baseStart_1127810 baseEnd_1127810 := by
    simpa [prefixWord, tailWord_1127810, baseEnd_1127810] using wordTrace_append hprefix tailTrace_1127810
  have hstable : (prefixWord ++ tailWord_1127810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127810).length < 2 ^ (prefixWord ++ tailWord_1127810).sum := by decide
  have hdescent : baseEnd_1127810 < baseStart_1127810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1127917 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 5]
def baseStart_1127917 : Nat := 118140960795 + 1127917 * 2 ^ 59
def prefixEnd_1127917 : Nat := 4983230072969 + 3 ^ 40 * 1127917 * 2
def baseEnd_1127917 : Nat := 257406026389941668111249

theorem tailTrace_1127917 : CollatzResearch.WordTrace tailWord_1127917 prefixEnd_1127917 257406026389941668111249 := by
  unfold tailWord_1127917
  simp only [CollatzResearch.WordTrace]
  refine ⟨41138512654756816732422005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27425675103171211154948003 41138512654756816732422005)
  ·
    refine ⟨3856735561383451568664563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41138512654756816732422005 3856735561383451568664563)
    ·
      refine ⟨5785103342075177352996845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856735561383451568664563 5785103342075177352996845)
      ·
        refine ⟨2169413753278191507373817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5785103342075177352996845 2169413753278191507373817)
        ·
          refine ⟨1627060314958643630530363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2169413753278191507373817 1627060314958643630530363)
          ·
            refine ⟨2440590472437965445795545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627060314958643630530363 2440590472437965445795545)
            ·
              refine ⟨1830442854328474084346659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2440590472437965445795545 1830442854328474084346659)
              ·
                refine ⟨2745664281492711126519989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1830442854328474084346659 2745664281492711126519989)
                ·
                  refine ⟨257406026389941668111249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2745664281492711126519989 257406026389941668111249)
                  ·
                    rfl

theorem cell21_1127917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_1127917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1127917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1127917 prefixEnd_1127917 := by exact prefixLift 1127917
  have htrace : WordTrace (prefixWord ++ tailWord_1127917) baseStart_1127917 baseEnd_1127917 := by
    simpa [prefixWord, tailWord_1127917, baseEnd_1127917] using wordTrace_append hprefix tailTrace_1127917
  have hstable : (prefixWord ++ tailWord_1127917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1127917).length < 2 ^ (prefixWord ++ tailWord_1127917).sum := by decide
  have hdescent : baseEnd_1127917 < baseStart_1127917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1127917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128125 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 8]
def baseStart_1128125 : Nat := 118140960795 + 1128125 * 2 ^ 59
def prefixEnd_1128125 : Nat := 4983230072969 + 3 ^ 40 * 1128125 * 2
def baseEnd_1128125 : Nat := 257453494823779528644157

theorem tailTrace_1128125 : CollatzResearch.WordTrace tailWord_1128125 prefixEnd_1128125 257453494823779528644157 := by
  unfold tailWord_1128125
  simp only [CollatzResearch.WordTrace]
  refine ⟨41146099038003268255993829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27430732692002178837329219 41146099038003268255993829)
  ·
    refine ⟨7714893569625612797998843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41146099038003268255993829 7714893569625612797998843)
    ·
      refine ⟨11572340354438419196998265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7714893569625612797998843 11572340354438419196998265)
      ·
        refine ⟨8679255265828814397748699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11572340354438419196998265 8679255265828814397748699)
        ·
          refine ⟨13018882898743221596623049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8679255265828814397748699 13018882898743221596623049)
          ·
            refine ⟨9764162174057416197467287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13018882898743221596623049 9764162174057416197467287)
            ·
              refine ⟨14646243261086124296200931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9764162174057416197467287 14646243261086124296200931)
              ·
                refine ⟨21969364891629186444301397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14646243261086124296200931 21969364891629186444301397)
                ·
                  refine ⟨257453494823779528644157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21969364891629186444301397 257453494823779528644157)
                  ·
                    rfl

theorem cell21_1128125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_1128125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128125 prefixEnd_1128125 := by exact prefixLift 1128125
  have htrace : WordTrace (prefixWord ++ tailWord_1128125) baseStart_1128125 baseEnd_1128125 := by
    simpa [prefixWord, tailWord_1128125, baseEnd_1128125] using wordTrace_append hprefix tailTrace_1128125
  have hstable : (prefixWord ++ tailWord_1128125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128125).length < 2 ^ (prefixWord ++ tailWord_1128125).sum := by decide
  have hdescent : baseEnd_1128125 < baseStart_1128125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128142 : List Nat := [4, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_1128142 : Nat := 118140960795 + 1128142 * 2 ^ 59
def prefixEnd_1128142 : Nat := 4983230072969 + 3 ^ 40 * 1128142 * 2
def baseEnd_1128142 : Nat := 257457374455391276860789

theorem tailTrace_1128142 : CollatzResearch.WordTrace tailWord_1128142 prefixEnd_1128142 257457374455391276860789 := by
  unfold tailWord_1128142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143339884867710019920335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27431146052627786772908453 5143339884867710019920335)
  ·
    refine ⟨7715009827301565029880503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5143339884867710019920335 7715009827301565029880503)
    ·
      refine ⟨11572514740952347544820755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7715009827301565029880503 11572514740952347544820755)
      ·
        refine ⟨17358772111428521317231133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11572514740952347544820755 17358772111428521317231133)
        ·
          refine ⟨6509539541785695493961675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17358772111428521317231133 6509539541785695493961675)
          ·
            refine ⟨9764309312678543240942513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6509539541785695493961675 9764309312678543240942513)
            ·
              refine ⟨7323231984508907430706885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9764309312678543240942513 7323231984508907430706885)
              ·
                refine ⟨1373105997095420143257541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7323231984508907430706885 1373105997095420143257541)
                ·
                  refine ⟨257457374455391276860789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373105997095420143257541 257457374455391276860789)
                  ·
                    rfl

theorem cell21_1128142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_1128142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128142 prefixEnd_1128142 := by exact prefixLift 1128142
  have htrace : WordTrace (prefixWord ++ tailWord_1128142) baseStart_1128142 baseEnd_1128142 := by
    simpa [prefixWord, tailWord_1128142, baseEnd_1128142] using wordTrace_append hprefix tailTrace_1128142
  have hstable : (prefixWord ++ tailWord_1128142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128142).length < 2 ^ (prefixWord ++ tailWord_1128142).sum := by decide
  have hdescent : baseEnd_1128142 < baseStart_1128142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128145 : List Nat := [1, 2, 2, 1, 2, 5, 3, 2, 3]
def baseStart_1128145 : Nat := 118140960795 + 1128145 * 2 ^ 59
def prefixEnd_1128145 : Nat := 4983230072969 + 3 ^ 40 * 1128145 * 2
def baseEnd_1128145 : Nat := 257458059096263938310783

theorem tailTrace_1128145 : CollatzResearch.WordTrace tailWord_1128145 prefixEnd_1128145 257458059096263938310783 := by
  unfold tailWord_1128145
  simp only [CollatzResearch.WordTrace]
  refine ⟨41146828497930811671721889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27431218998620541114481259 41146828497930811671721889)
  ·
    refine ⟨30860121373448108753791417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41146828497930811671721889 30860121373448108753791417)
    ·
      refine ⟨23145091030086081565343563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30860121373448108753791417 23145091030086081565343563)
      ·
        refine ⟨34717636545129122348015345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23145091030086081565343563 34717636545129122348015345)
        ·
          refine ⟨26038227408846841761011509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34717636545129122348015345 26038227408846841761011509)
          ·
            refine ⟨2441083819579391415094829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26038227408846841761011509 2441083819579391415094829)
            ·
              refine ⟨915406432342271780660561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2441083819579391415094829 915406432342271780660561)
              ·
                refine ⟨686554824256703835495421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915406432342271780660561 686554824256703835495421)
                ·
                  refine ⟨257458059096263938310783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686554824256703835495421 257458059096263938310783)
                  ·
                    rfl

theorem cell21_1128145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 2, 3].length) (baseStart_1128145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128145 prefixEnd_1128145 := by exact prefixLift 1128145
  have htrace : WordTrace (prefixWord ++ tailWord_1128145) baseStart_1128145 baseEnd_1128145 := by
    simpa [prefixWord, tailWord_1128145, baseEnd_1128145] using wordTrace_append hprefix tailTrace_1128145
  have hstable : (prefixWord ++ tailWord_1128145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128145).length < 2 ^ (prefixWord ++ tailWord_1128145).sum := by decide
  have hdescent : baseEnd_1128145 < baseStart_1128145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128218 : List Nat := [3, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_1128218 : Nat := 118140960795 + 1128218 * 2 ^ 59
def prefixEnd_1128218 : Nat := 4983230072969 + 3 ^ 40 * 1128218 * 2
def baseEnd_1128218 : Nat := 257474718690832033593967

theorem tailTrace_1128218 : CollatzResearch.WordTrace tailWord_1128218 prefixEnd_1128218 257474718690832033593967 := by
  unfold tailWord_1128218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10287372756666586284782327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27432994017777563426086205 10287372756666586284782327)
  ·
    refine ⟨15431059134999879427173491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10287372756666586284782327 15431059134999879427173491)
    ·
      refine ⟨23146588702499819140760237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15431059134999879427173491 23146588702499819140760237)
      ·
        refine ⟨8679970763437432177785089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23146588702499819140760237 8679970763437432177785089)
        ·
          refine ⟨6509978072578074133338817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8679970763437432177785089 6509978072578074133338817)
          ·
            refine ⟨4882483554433555600004113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6509978072578074133338817 4882483554433555600004113)
            ·
              refine ⟨3661862665825166700003085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4882483554433555600004113 3661862665825166700003085)
              ·
                refine ⟨1373198499684437512501157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3661862665825166700003085 1373198499684437512501157)
                ·
                  refine ⟨257474718690832033593967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373198499684437512501157 257474718690832033593967)
                  ·
                    rfl

theorem cell21_1128218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_1128218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128218 prefixEnd_1128218 := by exact prefixLift 1128218
  have htrace : WordTrace (prefixWord ++ tailWord_1128218) baseStart_1128218 baseEnd_1128218 := by
    simpa [prefixWord, tailWord_1128218, baseEnd_1128218] using wordTrace_append hprefix tailTrace_1128218
  have hstable : (prefixWord ++ tailWord_1128218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128218).length < 2 ^ (prefixWord ++ tailWord_1128218).sum := by decide
  have hdescent : baseEnd_1128218 < baseStart_1128218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128238 : List Nat := [4, 1, 3, 2, 2, 1, 2, 3, 3]
def baseStart_1128238 : Nat := 118140960795 + 1128238 * 2 ^ 59
def prefixEnd_1128238 : Nat := 4983230072969 + 3 ^ 40 * 1128238 * 2
def baseEnd_1128238 : Nat := 257479282963316443260593

theorem tailTrace_1128238 : CollatzResearch.WordTrace tailWord_1128238 prefixEnd_1128238 257479282963316443260593 := by
  unfold tailWord_1128238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143777560824236069357171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27433480324395925703238245 5143777560824236069357171)
  ·
    refine ⟨7715666341236354104035757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5143777560824236069357171 7715666341236354104035757)
    ·
      refine ⟨2893374877963632789013409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7715666341236354104035757 2893374877963632789013409)
      ·
        refine ⟨2170031158472724591760057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2893374877963632789013409 2170031158472724591760057)
        ·
          refine ⟨1627523368854543443820043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2170031158472724591760057 1627523368854543443820043)
          ·
            refine ⟨2441285053281815165730065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627523368854543443820043 2441285053281815165730065)
            ·
              refine ⟨1830963789961361374297549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2441285053281815165730065 1830963789961361374297549)
              ·
                refine ⟨686611421235510515361581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1830963789961361374297549 686611421235510515361581)
                ·
                  refine ⟨257479282963316443260593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686611421235510515361581 257479282963316443260593)
                  ·
                    rfl

theorem cell21_1128238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_1128238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128238 prefixEnd_1128238 := by exact prefixLift 1128238
  have htrace : WordTrace (prefixWord ++ tailWord_1128238) baseStart_1128238 baseEnd_1128238 := by
    simpa [prefixWord, tailWord_1128238, baseEnd_1128238] using wordTrace_append hprefix tailTrace_1128238
  have hstable : (prefixWord ++ tailWord_1128238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128238).length < 2 ^ (prefixWord ++ tailWord_1128238).sum := by decide
  have hdescent : baseEnd_1128238 < baseStart_1128238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128249 : List Nat := [1, 2, 1, 7, 1, 1, 8]
def baseStart_1128249 : Nat := 118140960795 + 1128249 * 2 ^ 59
def prefixEnd_1128249 : Nat := 4983230072969 + 3 ^ 40 * 1128249 * 2
def baseEnd_1128249 : Nat := 28609088145909207619693

theorem tailTrace_1128249 : CollatzResearch.WordTrace tailWord_1128249 prefixEnd_1128249 28609088145909207619693 := by
  unfold tailWord_1128249
  simp only [CollatzResearch.WordTrace]
  refine ⟨41150621689554037433507801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27433747793036024955671867 41150621689554037433507801)
  ·
    refine ⟨30862966267165528075130851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41150621689554037433507801 30862966267165528075130851)
    ·
      refine ⟨46294449400748292112696277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30862966267165528075130851 46294449400748292112696277)
      ·
        refine ⟨1085026157830038096391319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 46294449400748292112696277 1085026157830038096391319)
        ·
          refine ⟨1627539236745057144586979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085026157830038096391319 1627539236745057144586979)
          ·
            refine ⟨2441308855117585716880469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1627539236745057144586979 2441308855117585716880469)
            ·
              refine ⟨28609088145909207619693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2441308855117585716880469 28609088145909207619693)
              ·
                rfl

theorem cell21_1128249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 8].length) (baseStart_1128249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128249 prefixEnd_1128249 := by exact prefixLift 1128249
  have htrace : WordTrace (prefixWord ++ tailWord_1128249) baseStart_1128249 baseEnd_1128249 := by
    simpa [prefixWord, tailWord_1128249, baseEnd_1128249] using wordTrace_append hprefix tailTrace_1128249
  have hstable : (prefixWord ++ tailWord_1128249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128249).length < 2 ^ (prefixWord ++ tailWord_1128249).sum := by decide
  have hdescent : baseEnd_1128249 < baseStart_1128249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128328 : List Nat := [2, 1, 3, 3, 3, 2, 2, 1, 4]
def baseStart_1128328 : Nat := 118140960795 + 1128328 * 2 ^ 59
def prefixEnd_1128328 : Nat := 4983230072969 + 3 ^ 40 * 1128328 * 2
def baseEnd_1128328 : Nat := 257499822189496286760409

theorem tailTrace_1128328 : CollatzResearch.WordTrace tailWord_1128328 prefixEnd_1128328 257499822189496286760409 := by
  unfold tailWord_1128328
  simp only [CollatzResearch.WordTrace]
  refine ⟨20576751528133916962816819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27435668704178555950422425 20576751528133916962816819)
  ·
    refine ⟨30865127292200875444225229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20576751528133916962816819 30865127292200875444225229)
    ·
      refine ⟨11574422734575328291584461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30865127292200875444225229 11574422734575328291584461)
      ·
        refine ⟨4340408525465748109344173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11574422734575328291584461 4340408525465748109344173)
        ·
          refine ⟨1627653197049655541004065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4340408525465748109344173 1627653197049655541004065)
          ·
            refine ⟨1220739897787241655753049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627653197049655541004065 1220739897787241655753049)
            ·
              refine ⟨915554923340431241814787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1220739897787241655753049 915554923340431241814787)
              ·
                refine ⟨1373332385010646862722181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915554923340431241814787 1373332385010646862722181)
                ·
                  refine ⟨257499822189496286760409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1373332385010646862722181 257499822189496286760409)
                  ·
                    rfl

theorem cell21_1128328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 2, 1, 4].length) (baseStart_1128328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128328 prefixEnd_1128328 := by exact prefixLift 1128328
  have htrace : WordTrace (prefixWord ++ tailWord_1128328) baseStart_1128328 baseEnd_1128328 := by
    simpa [prefixWord, tailWord_1128328, baseEnd_1128328] using wordTrace_append hprefix tailTrace_1128328
  have hstable : (prefixWord ++ tailWord_1128328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128328).length < 2 ^ (prefixWord ++ tailWord_1128328).sum := by decide
  have hdescent : baseEnd_1128328 < baseStart_1128328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128373 : List Nat := [1, 3, 3, 2, 1, 2, 4, 2, 3]
def baseStart_1128373 : Nat := 118140960795 + 1128373 * 2 ^ 59
def prefixEnd_1128373 : Nat := 4983230072969 + 3 ^ 40 * 1128373 * 2
def baseEnd_1128373 : Nat := 257510091802586208510317

theorem tailTrace_1128373 : CollatzResearch.WordTrace tailWord_1128373 prefixEnd_1128373 257510091802586208510317 := by
  unfold tailWord_1128373
  simp only [CollatzResearch.WordTrace]
  refine ⟨41155144341104806611021773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27436762894069871074014515 41155144341104806611021773)
  ·
    refine ⟨15433179127914302479133165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41155144341104806611021773 15433179127914302479133165)
    ·
      refine ⟨5787442172967863429674937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15433179127914302479133165 5787442172967863429674937)
      ·
        refine ⟨4340581629725897572256203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5787442172967863429674937 4340581629725897572256203)
        ·
          refine ⟨6510872444588846358384305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4340581629725897572256203 6510872444588846358384305)
          ·
            refine ⟨4883154333441634768788229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6510872444588846358384305 4883154333441634768788229)
            ·
              refine ⟨915591437520306519147793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4883154333441634768788229 915591437520306519147793)
              ·
                refine ⟨686693578140229889360845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915591437520306519147793 686693578140229889360845)
                ·
                  refine ⟨257510091802586208510317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686693578140229889360845 257510091802586208510317)
                  ·
                    rfl

theorem cell21_1128373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_1128373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128373 prefixEnd_1128373 := by exact prefixLift 1128373
  have htrace : WordTrace (prefixWord ++ tailWord_1128373) baseStart_1128373 baseEnd_1128373 := by
    simpa [prefixWord, tailWord_1128373, baseEnd_1128373] using wordTrace_append hprefix tailTrace_1128373
  have hstable : (prefixWord ++ tailWord_1128373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128373).length < 2 ^ (prefixWord ++ tailWord_1128373).sum := by decide
  have hdescent : baseEnd_1128373 < baseStart_1128373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128519 : List Nat := [1, 1, 4, 1, 3, 1, 1, 9]
def baseStart_1128519 : Nat := 118140960795 + 1128519 * 2 ^ 59
def prefixEnd_1128519 : Nat := 4983230072969 + 3 ^ 40 * 1128519 * 2
def baseEnd_1128519 : Nat := 85847803663907466358895

theorem tailTrace_1128519 : CollatzResearch.WordTrace tailWord_1128519 prefixEnd_1128519 85847803663907466358895 := by
  unfold tailWord_1128519
  simp only [CollatzResearch.WordTrace]
  refine ⟨41160469398575873545836611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27440312932383915697224407 41160469398575873545836611)
  ·
    refine ⟨61740704097863810318754917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41160469398575873545836611 61740704097863810318754917)
    ·
      refine ⟨11576382018349464434766547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61740704097863810318754917 11576382018349464434766547)
      ·
        refine ⟨17364573027524196652149821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11576382018349464434766547 17364573027524196652149821)
        ·
          refine ⟨6511714885321573744556183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17364573027524196652149821 6511714885321573744556183)
          ·
            refine ⟨9767572327982360616834275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6511714885321573744556183 9767572327982360616834275)
            ·
              refine ⟨14651358491973540925251413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9767572327982360616834275 14651358491973540925251413)
              ·
                refine ⟨85847803663907466358895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14651358491973540925251413 85847803663907466358895)
                ·
                  rfl

theorem cell21_1128519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_1128519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128519 prefixEnd_1128519 := by exact prefixLift 1128519
  have htrace : WordTrace (prefixWord ++ tailWord_1128519) baseStart_1128519 baseEnd_1128519 := by
    simpa [prefixWord, tailWord_1128519, baseEnd_1128519] using wordTrace_append hprefix tailTrace_1128519
  have hstable : (prefixWord ++ tailWord_1128519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128519).length < 2 ^ (prefixWord ++ tailWord_1128519).sum := by decide
  have hdescent : baseEnd_1128519 < baseStart_1128519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128584 : List Nat := [2, 1, 3, 4, 1, 1, 1, 5, 3]
def baseStart_1128584 : Nat := 118140960795 + 1128584 * 2 ^ 59
def prefixEnd_1128584 : Nat := 4983230072969 + 3 ^ 40 * 1128584 * 2
def baseEnd_1128584 : Nat := 257558244877296730493219

theorem tailTrace_1128584 : CollatzResearch.WordTrace tailWord_1128584 prefixEnd_1128584 257558244877296730493219 := by
  unfold tailWord_1128584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20581420071670194823476403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27441893428893593097968537 20581420071670194823476403)
  ·
    refine ⟨30872130107505292235214605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20581420071670194823476403 30872130107505292235214605)
    ·
      refine ⟨11577048790314484588205477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30872130107505292235214605 11577048790314484588205477)
      ·
        refine ⟨2170696648183965860288527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11577048790314484588205477 2170696648183965860288527)
        ·
          refine ⟨3256044972275948790432791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2170696648183965860288527 3256044972275948790432791)
          ·
            refine ⟨4884067458413923185649187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3256044972275948790432791 4884067458413923185649187)
            ·
              refine ⟨7326101187620884778473781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4884067458413923185649187 7326101187620884778473781)
              ·
                refine ⟨686821986339457947981917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7326101187620884778473781 686821986339457947981917)
                ·
                  refine ⟨257558244877296730493219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686821986339457947981917 257558244877296730493219)
                  ·
                    rfl

theorem cell21_1128584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 5, 3].length) (baseStart_1128584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128584 prefixEnd_1128584 := by exact prefixLift 1128584
  have htrace : WordTrace (prefixWord ++ tailWord_1128584) baseStart_1128584 baseEnd_1128584 := by
    simpa [prefixWord, tailWord_1128584, baseEnd_1128584] using wordTrace_append hprefix tailTrace_1128584
  have hstable : (prefixWord ++ tailWord_1128584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128584).length < 2 ^ (prefixWord ++ tailWord_1128584).sum := by decide
  have hdescent : baseEnd_1128584 < baseStart_1128584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128626 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_1128626 : Nat := 118140960795 + 1128626 * 2 ^ 59
def prefixEnd_1128626 : Nat := 4983230072969 + 3 ^ 40 * 1128626 * 2
def baseEnd_1128626 : Nat := 257567829849513990793133

theorem tailTrace_1128626 : CollatzResearch.WordTrace tailWord_1128626 prefixEnd_1128626 257567829849513990793133 := by
  unfold tailWord_1128626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10291093002297057704995433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27442914672792153879987821 10291093002297057704995433)
  ·
    refine ⟨7718319751722793278746575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10291093002297057704995433 7718319751722793278746575)
    ·
      refine ⟨11577479627584189918119863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7718319751722793278746575 11577479627584189918119863)
      ·
        refine ⟨17366219441376284877179795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11577479627584189918119863 17366219441376284877179795)
        ·
          refine ⟨26049329162064427315769693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17366219441376284877179795 26049329162064427315769693)
          ·
            refine ⟨9768498435774160243413635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26049329162064427315769693 9768498435774160243413635)
            ·
              refine ⟨14652747653661240365120453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9768498435774160243413635 14652747653661240365120453)
              ·
                refine ⟨2747390185061482568460085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14652747653661240365120453 2747390185061482568460085)
                ·
                  refine ⟨257567829849513990793133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2747390185061482568460085 257567829849513990793133)
                  ·
                    rfl

theorem cell21_1128626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_1128626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128626 prefixEnd_1128626 := by exact prefixLift 1128626
  have htrace : WordTrace (prefixWord ++ tailWord_1128626) baseStart_1128626 baseEnd_1128626 := by
    simpa [prefixWord, tailWord_1128626, baseEnd_1128626] using wordTrace_append hprefix tailTrace_1128626
  have hstable : (prefixWord ++ tailWord_1128626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128626).length < 2 ^ (prefixWord ++ tailWord_1128626).sum := by decide
  have hdescent : baseEnd_1128626 < baseStart_1128626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128629 : List Nat := [1, 3, 3, 4, 1, 1, 1, 7]
def baseStart_1128629 : Nat := 118140960795 + 1128629 * 2 ^ 59
def prefixEnd_1128629 : Nat := 4983230072969 + 3 ^ 40 * 1128629 * 2
def baseEnd_1128629 : Nat := 85856171496795550747709

theorem tailTrace_1128629 : CollatzResearch.WordTrace tailWord_1128629 prefixEnd_1128629 85856171496795550747709 := by
  unfold tailWord_1128629
  simp only [CollatzResearch.WordTrace]
  refine ⟨41164481428177362332340941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27442987618784908221560627 41164481428177362332340941)
  ·
    refine ⟨15436680535566510874627853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41164481428177362332340941 15436680535566510874627853)
    ·
      refine ⟨5788755200837441577985445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15436680535566510874627853 5788755200837441577985445)
      ·
        refine ⟨1085391600157020295872271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5788755200837441577985445 1085391600157020295872271)
        ·
          refine ⟨1628087400235530443808407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085391600157020295872271 1628087400235530443808407)
          ·
            refine ⟨2442131100353295665712611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628087400235530443808407 2442131100353295665712611)
            ·
              refine ⟨3663196650529943498568917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2442131100353295665712611 3663196650529943498568917)
              ·
                refine ⟨85856171496795550747709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3663196650529943498568917 85856171496795550747709)
                ·
                  rfl

theorem cell21_1128629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 7].length) (baseStart_1128629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128629 prefixEnd_1128629 := by exact prefixLift 1128629
  have htrace : WordTrace (prefixWord ++ tailWord_1128629) baseStart_1128629 baseEnd_1128629 := by
    simpa [prefixWord, tailWord_1128629, baseEnd_1128629] using wordTrace_append hprefix tailTrace_1128629
  have hstable : (prefixWord ++ tailWord_1128629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128629).length < 2 ^ (prefixWord ++ tailWord_1128629).sum := by decide
  have hdescent : baseEnd_1128629 < baseStart_1128629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128711 : List Nat := [1, 1, 4, 5, 2, 1, 2, 2, 3]
def baseStart_1128711 : Nat := 118140960795 + 1128711 * 2 ^ 59
def prefixEnd_1128711 : Nat := 4983230072969 + 3 ^ 40 * 1128711 * 2
def baseEnd_1128711 : Nat := 257587228007572731876293

theorem tailTrace_1128711 : CollatzResearch.WordTrace tailWord_1128711 prefixEnd_1128711 257587228007572731876293 := by
  unfold tailWord_1128711
  simp only [CollatzResearch.WordTrace]
  refine ⟨41167472213880290336825987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27444981475920193557883991 41167472213880290336825987)
  ·
    refine ⟨61751208320820435505238981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41167472213880290336825987 61751208320820435505238981)
    ·
      refine ⟨11578351560153831657232309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61751208320820435505238981 11578351560153831657232309)
      ·
        refine ⟨1085470458764421717865529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11578351560153831657232309 1085470458764421717865529)
        ·
          refine ⟨814102844073316288399147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085470458764421717865529 814102844073316288399147)
          ·
            refine ⟨1221154266109974432598721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814102844073316288399147 1221154266109974432598721)
            ·
              refine ⟨915865699582480824449041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1221154266109974432598721 915865699582480824449041)
              ·
                refine ⟨686899274686860618336781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 915865699582480824449041 686899274686860618336781)
                ·
                  refine ⟨257587228007572731876293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686899274686860618336781 257587228007572731876293)
                  ·
                    rfl

theorem cell21_1128711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 2, 3].length) (baseStart_1128711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128711 prefixEnd_1128711 := by exact prefixLift 1128711
  have htrace : WordTrace (prefixWord ++ tailWord_1128711) baseStart_1128711 baseEnd_1128711 := by
    simpa [prefixWord, tailWord_1128711, baseEnd_1128711] using wordTrace_append hprefix tailTrace_1128711
  have hstable : (prefixWord ++ tailWord_1128711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128711).length < 2 ^ (prefixWord ++ tailWord_1128711).sum := by decide
  have hdescent : baseEnd_1128711 < baseStart_1128711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128868 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1128868 : Nat := 118140960795 + 1128868 * 2 ^ 59
def prefixEnd_1128868 : Nat := 4983230072969 + 3 ^ 40 * 1128868 * 2
def baseEnd_1128868 : Nat := 257623057546575347759305

theorem tailTrace_1128868 : CollatzResearch.WordTrace tailWord_1128868 prefixEnd_1128868 257623057546575347759305 := by
  unfold tailWord_1128868
  simp only [CollatzResearch.WordTrace]
  refine ⟨20586599237155753075145629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27448798982874337433527505 20586599237155753075145629)
  ·
    refine ⟨7719974713933407403179611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20586599237155753075145629 7719974713933407403179611)
    ·
      refine ⟨11579962070900111104769417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7719974713933407403179611 11579962070900111104769417)
      ·
        refine ⟨8684971553175083328577063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11579962070900111104769417 8684971553175083328577063)
        ·
          refine ⟨13027457329762624992865595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8684971553175083328577063 13027457329762624992865595)
          ·
            refine ⟨19541185994643937489298393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13027457329762624992865595 19541185994643937489298393)
            ·
              refine ⟨14655889495982953116973795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19541185994643937489298393 14655889495982953116973795)
              ·
                refine ⟨21983834243974429675460693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14655889495982953116973795 21983834243974429675460693)
                ·
                  refine ⟨257623057546575347759305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21983834243974429675460693 257623057546575347759305)
                  ·
                    rfl

theorem cell21_1128868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1128868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128868 prefixEnd_1128868 := by exact prefixLift 1128868
  have htrace : WordTrace (prefixWord ++ tailWord_1128868) baseStart_1128868 baseEnd_1128868 := by
    simpa [prefixWord, tailWord_1128868, baseEnd_1128868] using wordTrace_append hprefix tailTrace_1128868
  have hstable : (prefixWord ++ tailWord_1128868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128868).length < 2 ^ (prefixWord ++ tailWord_1128868).sum := by decide
  have hdescent : baseEnd_1128868 < baseStart_1128868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128874 : List Nat := [3, 1, 6, 1, 2, 8]
def baseStart_1128874 : Nat := 118140960795 + 1128874 * 2 ^ 59
def prefixEnd_1128874 : Nat := 4983230072969 + 3 ^ 40 * 1128874 * 2
def baseEnd_1128874 : Nat := 9541645438085950765159

theorem tailTrace_1128874 : CollatzResearch.WordTrace tailWord_1128874 prefixEnd_1128874 9541645438085950765159 := by
  unfold tailWord_1128874
  simp only [CollatzResearch.WordTrace]
  refine ⟨10293354328072442293752419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27448944874859846116673117 10293354328072442293752419)
  ·
    refine ⟨15440031492108663440628629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10293354328072442293752419 15440031492108663440628629)
    ·
      refine ⟨723751476192593598779467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15440031492108663440628629 723751476192593598779467)
      ·
        refine ⟨1085627214288890398169201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 723751476192593598779467 1085627214288890398169201)
        ·
          refine ⟨814220410716667798626901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1085627214288890398169201 814220410716667798626901)
          ·
            refine ⟨9541645438085950765159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 814220410716667798626901 9541645438085950765159)
            ·
              rfl

theorem cell21_1128874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 8].length) (baseStart_1128874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128874 prefixEnd_1128874 := by exact prefixLift 1128874
  have htrace : WordTrace (prefixWord ++ tailWord_1128874) baseStart_1128874 baseEnd_1128874 := by
    simpa [prefixWord, tailWord_1128874, baseEnd_1128874] using wordTrace_append hprefix tailTrace_1128874
  have hstable : (prefixWord ++ tailWord_1128874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128874).length < 2 ^ (prefixWord ++ tailWord_1128874).sum := by decide
  have hdescent : baseEnd_1128874 < baseStart_1128874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128944 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 6]
def baseStart_1128944 : Nat := 118140960795 + 1128944 * 2 ^ 59
def prefixEnd_1128944 : Nat := 4983230072969 + 3 ^ 40 * 1128944 * 2
def baseEnd_1128944 : Nat := 257640401782016104492483

theorem tailTrace_1128944 : CollatzResearch.WordTrace tailWord_1128944 prefixEnd_1128944 257640401782016104492483 := by
  unfold tailWord_1128944
  simp only [CollatzResearch.WordTrace]
  refine ⟨20587985211018085565028943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27450646948024114086705257 20587985211018085565028943)
  ·
    refine ⟨30881977816527128347543415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20587985211018085565028943 30881977816527128347543415)
    ·
      refine ⟨46322966724790692521315123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30881977816527128347543415 46322966724790692521315123)
      ·
        refine ⟨69484450087186038781972685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46322966724790692521315123 69484450087186038781972685)
        ·
          refine ⟨26056668782694764543239757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69484450087186038781972685 26056668782694764543239757)
          ·
            refine ⟨9771250793510536703714909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26056668782694764543239757 9771250793510536703714909)
            ·
              refine ⟨3664219047566451263893091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9771250793510536703714909 3664219047566451263893091)
              ·
                refine ⟨5496328571349676895839637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3664219047566451263893091 5496328571349676895839637)
                ·
                  refine ⟨257640401782016104492483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5496328571349676895839637 257640401782016104492483)
                  ·
                    rfl

theorem cell21_1128944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 6].length) (baseStart_1128944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128944 prefixEnd_1128944 := by exact prefixLift 1128944
  have htrace : WordTrace (prefixWord ++ tailWord_1128944) baseStart_1128944 baseEnd_1128944 := by
    simpa [prefixWord, tailWord_1128944, baseEnd_1128944] using wordTrace_append hprefix tailTrace_1128944
  have hstable : (prefixWord ++ tailWord_1128944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128944).length < 2 ^ (prefixWord ++ tailWord_1128944).sum := by decide
  have hdescent : baseEnd_1128944 < baseStart_1128944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1128992 : List Nat := [2, 1, 1, 6, 2, 2, 7]
def baseStart_1128992 : Nat := 118140960795 + 1128992 * 2 ^ 59
def prefixEnd_1128992 : Nat := 4983230072969 + 3 ^ 40 * 1128992 * 2
def baseEnd_1128992 : Nat := 28627928448442076410265

theorem tailTrace_1128992 : CollatzResearch.WordTrace tailWord_1128992 prefixEnd_1128992 28627928448442076410265 := by
  unfold tailWord_1128992
  simp only [CollatzResearch.WordTrace]
  refine ⟨20588860562931137663902615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27451814083908183551870153 20588860562931137663902615)
  ·
    refine ⟨30883290844396706495853923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20588860562931137663902615 30883290844396706495853923)
    ·
      refine ⟨46324936266595059743780885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30883290844396706495853923 46324936266595059743780885)
      ·
        refine ⟨2171481387496643425489729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46324936266595059743780885 2171481387496643425489729)
        ·
          refine ⟨1628611040622482569117297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2171481387496643425489729 1628611040622482569117297)
          ·
            refine ⟨1221458280466861926837973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1628611040622482569117297 1221458280466861926837973)
            ·
              refine ⟨28627928448442076410265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1221458280466861926837973 28627928448442076410265)
              ·
                rfl

theorem cell21_1128992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 7].length) (baseStart_1128992 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1128992 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1128992 prefixEnd_1128992 := by exact prefixLift 1128992
  have htrace : WordTrace (prefixWord ++ tailWord_1128992) baseStart_1128992 baseEnd_1128992 := by
    simpa [prefixWord, tailWord_1128992, baseEnd_1128992] using wordTrace_append hprefix tailTrace_1128992
  have hstable : (prefixWord ++ tailWord_1128992).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1128992).length < 2 ^ (prefixWord ++ tailWord_1128992).sum := by decide
  have hdescent : baseEnd_1128992 < baseStart_1128992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1128992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129065 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 5]
def baseStart_1129065 : Nat := 118140960795 + 1129065 * 2 ^ 59
def prefixEnd_1129065 : Nat := 4983230072969 + 3 ^ 40 * 1129065 * 2
def baseEnd_1129065 : Nat := 257668015630546782975569

theorem tailTrace_1129065 : CollatzResearch.WordTrace tailWord_1129065 prefixEnd_1129065 257668015630546782975569 := by
  unfold tailWord_1129065
  simp only [CollatzResearch.WordTrace]
  refine ⟨41180383654597808795212649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27453589103065205863475099 41180383654597808795212649)
  ·
    refine ⟨30885287740948356596409487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41180383654597808795212649 30885287740948356596409487)
    ·
      refine ⟨46327931611422534894614231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30885287740948356596409487 46327931611422534894614231)
      ·
        refine ⟨69491897417133802341921347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46327931611422534894614231 69491897417133802341921347)
        ·
          refine ⟨104237846125700703512882021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69491897417133802341921347 104237846125700703512882021)
          ·
            refine ⟨19544596148568881908665379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104237846125700703512882021 19544596148568881908665379)
            ·
              refine ⟨29316894222853322862998069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19544596148568881908665379 29316894222853322862998069)
              ·
                refine ⟨2748458833392499018406069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29316894222853322862998069 2748458833392499018406069)
                ·
                  refine ⟨257668015630546782975569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2748458833392499018406069 257668015630546782975569)
                  ·
                    rfl

theorem cell21_1129065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_1129065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129065 prefixEnd_1129065 := by exact prefixLift 1129065
  have htrace : WordTrace (prefixWord ++ tailWord_1129065) baseStart_1129065 baseEnd_1129065 := by
    simpa [prefixWord, tailWord_1129065, baseEnd_1129065] using wordTrace_append hprefix tailTrace_1129065
  have hstable : (prefixWord ++ tailWord_1129065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129065).length < 2 ^ (prefixWord ++ tailWord_1129065).sum := by decide
  have hdescent : baseEnd_1129065 < baseStart_1129065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129189 : List Nat := [1, 3, 1, 4, 1, 3, 1, 3, 4]
def baseStart_1129189 : Nat := 118140960795 + 1129189 * 2 ^ 59
def prefixEnd_1129189 : Nat := 4983230072969 + 3 ^ 40 * 1129189 * 2
def baseEnd_1129189 : Nat := 257696314119950122908649

theorem tailTrace_1129189 : CollatzResearch.WordTrace tailWord_1129189 prefixEnd_1129189 257696314119950122908649 := by
  unfold tailWord_1129189
  simp only [CollatzResearch.WordTrace]
  refine ⟨41184906306148577972726621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27456604204099051981817747 41184906306148577972726621)
  ·
    refine ⟨15444339864805716739772483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41184906306148577972726621 15444339864805716739772483)
    ·
      refine ⟨23166509797208575109658725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15444339864805716739772483 23166509797208575109658725)
      ·
        refine ⟨4343720586976607833061011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23166509797208575109658725 4343720586976607833061011)
        ·
          refine ⟨6515580880464911749591517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4343720586976607833061011 6515580880464911749591517)
          ·
            refine ⟨2443342830174341906096819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6515580880464911749591517 2443342830174341906096819)
            ·
              refine ⟨3665014245261512859145229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443342830174341906096819 3665014245261512859145229)
              ·
                refine ⟨1374380341973067322179461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3665014245261512859145229 1374380341973067322179461)
                ·
                  refine ⟨257696314119950122908649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1374380341973067322179461 257696314119950122908649)
                  ·
                    rfl

theorem cell21_1129189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_1129189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129189 prefixEnd_1129189 := by exact prefixLift 1129189
  have htrace : WordTrace (prefixWord ++ tailWord_1129189) baseStart_1129189 baseEnd_1129189 := by
    simpa [prefixWord, tailWord_1129189, baseEnd_1129189] using wordTrace_append hprefix tailTrace_1129189
  have hstable : (prefixWord ++ tailWord_1129189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129189).length < 2 ^ (prefixWord ++ tailWord_1129189).sum := by decide
  have hdescent : baseEnd_1129189 < baseStart_1129189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129400 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 4]
def baseStart_1129400 : Nat := 118140960795 + 1129400 * 2 ^ 59
def prefixEnd_1129400 : Nat := 4983230072969 + 3 ^ 40 * 1129400 * 2
def baseEnd_1129400 : Nat := 257744467194660644891551

theorem tailTrace_1129400 : CollatzResearch.WordTrace tailWord_1129400 prefixEnd_1129400 257744467194660644891551 := by
  unfold tailWord_1129400
  simp only [CollatzResearch.WordTrace]
  refine ⟨20596301054192080504328827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27461734738922774005771769 20596301054192080504328827)
  ·
    refine ⟨30894451581288120756493241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20596301054192080504328827 30894451581288120756493241)
    ·
      refine ⟨23170838685966090567369931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30894451581288120756493241 23170838685966090567369931)
      ·
        refine ⟨34756258028949135851054897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23170838685966090567369931 34756258028949135851054897)
        ·
          refine ⟨26067193521711851888291173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34756258028949135851054897 26067193521711851888291173)
          ·
            refine ⟨4887598785320972229054595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26067193521711851888291173 4887598785320972229054595)
            ·
              refine ⟨7331398177981458343581893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887598785320972229054595 7331398177981458343581893)
              ·
                refine ⟨1374637158371523439421605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7331398177981458343581893 1374637158371523439421605)
                ·
                  refine ⟨257744467194660644891551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1374637158371523439421605 257744467194660644891551)
                  ·
                    rfl

theorem cell21_1129400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 4].length) (baseStart_1129400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129400 prefixEnd_1129400 := by exact prefixLift 1129400
  have htrace : WordTrace (prefixWord ++ tailWord_1129400) baseStart_1129400 baseEnd_1129400 := by
    simpa [prefixWord, tailWord_1129400, baseEnd_1129400] using wordTrace_append hprefix tailTrace_1129400
  have hstable : (prefixWord ++ tailWord_1129400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129400).length < 2 ^ (prefixWord ++ tailWord_1129400).sum := by decide
  have hdescent : baseEnd_1129400 < baseStart_1129400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129462 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1129462 : Nat := 118140960795 + 1129462 * 2 ^ 59
def prefixEnd_1129462 : Nat := 4983230072969 + 3 ^ 40 * 1129462 * 2
def baseEnd_1129462 : Nat := 257758616439362314858091

theorem tailTrace_1129462 : CollatzResearch.WordTrace tailWord_1129462 prefixEnd_1129462 257758616439362314858091 := by
  unfold tailWord_1129462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574678964634971599838415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27463242289439697064943093 2574678964634971599838415)
  ·
    refine ⟨3862018446952457399757623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2574678964634971599838415 3862018446952457399757623)
    ·
      refine ⟨5793027670428686099636435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3862018446952457399757623 5793027670428686099636435)
      ·
        refine ⟨8689541505643029149454653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793027670428686099636435 8689541505643029149454653)
        ·
          refine ⟨3258578064616135931045495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8689541505643029149454653 3258578064616135931045495)
          ·
            refine ⟨4887867096924203896568243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3258578064616135931045495 4887867096924203896568243)
            ·
              refine ⟨7331800645386305844852365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4887867096924203896568243 7331800645386305844852365)
              ·
                refine ⟨2749425242019864691819637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7331800645386305844852365 2749425242019864691819637)
                ·
                  refine ⟨257758616439362314858091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2749425242019864691819637 257758616439362314858091)
                  ·
                    rfl

theorem cell21_1129462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1129462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129462 prefixEnd_1129462 := by exact prefixLift 1129462
  have htrace : WordTrace (prefixWord ++ tailWord_1129462) baseStart_1129462 baseEnd_1129462 := by
    simpa [prefixWord, tailWord_1129462, baseEnd_1129462] using wordTrace_append hprefix tailTrace_1129462
  have hstable : (prefixWord ++ tailWord_1129462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129462).length < 2 ^ (prefixWord ++ tailWord_1129462).sum := by decide
  have hdescent : baseEnd_1129462 < baseStart_1129462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129524 : List Nat := [2, 5, 1, 2, 1, 2, 2, 6]
def baseStart_1129524 : Nat := 118140960795 + 1129524 * 2 ^ 59
def prefixEnd_1129524 : Nat := 4983230072969 + 3 ^ 40 * 1129524 * 2
def baseEnd_1129524 : Nat := 85924255228021328274877

theorem tailTrace_1129524 : CollatzResearch.WordTrace tailWord_1129524 prefixEnd_1129524 85924255228021328274877 := by
  unfold tailWord_1129524
  simp only [CollatzResearch.WordTrace]
  refine ⟨20598562379967465093085813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27464749839956620124114417 20598562379967465093085813)
  ·
    refine ⟨1931115223121949852476795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20598562379967465093085813 1931115223121949852476795)
    ·
      refine ⟨2896672834682924778715193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931115223121949852476795 2896672834682924778715193)
      ·
        refine ⟨2172504626012193584036395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2896672834682924778715193 2172504626012193584036395)
        ·
          refine ⟨3258756939018290376054593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2172504626012193584036395 3258756939018290376054593)
          ·
            refine ⟨2444067704263717782040945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3258756939018290376054593 2444067704263717782040945)
            ·
              refine ⟨1833050778197788336530709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2444067704263717782040945 1833050778197788336530709)
              ·
                refine ⟨85924255228021328274877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1833050778197788336530709 85924255228021328274877)
                ·
                  rfl

theorem cell21_1129524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_1129524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129524 prefixEnd_1129524 := by exact prefixLift 1129524
  have htrace : WordTrace (prefixWord ++ tailWord_1129524) baseStart_1129524 baseEnd_1129524 := by
    simpa [prefixWord, tailWord_1129524, baseEnd_1129524] using wordTrace_append hprefix tailTrace_1129524
  have hstable : (prefixWord ++ tailWord_1129524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129524).length < 2 ^ (prefixWord ++ tailWord_1129524).sum := by decide
  have hdescent : baseEnd_1129524 < baseStart_1129524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129597 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 5]
def baseStart_1129597 : Nat := 118140960795 + 1129597 * 2 ^ 59
def prefixEnd_1129597 : Nat := 4983230072969 + 3 ^ 40 * 1129597 * 2
def baseEnd_1129597 : Nat := 257789425278632080107815

theorem tailTrace_1129597 : CollatzResearch.WordTrace tailWord_1129597 prefixEnd_1129597 257789425278632080107815 := by
  unfold tailWord_1129597
  simp only [CollatzResearch.WordTrace]
  refine ⟨41199787288670463653579045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27466524859113642435719363 41199787288670463653579045)
  ·
    refine ⟨7724960116625711935046071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41199787288670463653579045 7724960116625711935046071)
    ·
      refine ⟨11587440174938567902569107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7724960116625711935046071 11587440174938567902569107)
      ·
        refine ⟨17381160262407851853853661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11587440174938567902569107 17381160262407851853853661)
        ·
          refine ⟨6517935098402944445195123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17381160262407851853853661 6517935098402944445195123)
          ·
            refine ⟨9776902647604416667792685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6517935098402944445195123 9776902647604416667792685)
            ·
              refine ⟨3666338492851656250422257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9776902647604416667792685 3666338492851656250422257)
              ·
                refine ⟨2749753869638742187816693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3666338492851656250422257 2749753869638742187816693)
                ·
                  refine ⟨257789425278632080107815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2749753869638742187816693 257789425278632080107815)
                  ·
                    rfl

theorem cell21_1129597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_1129597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129597 prefixEnd_1129597 := by exact prefixLift 1129597
  have htrace : WordTrace (prefixWord ++ tailWord_1129597) baseStart_1129597 baseEnd_1129597 := by
    simpa [prefixWord, tailWord_1129597, baseEnd_1129597] using wordTrace_append hprefix tailTrace_1129597
  have hstable : (prefixWord ++ tailWord_1129597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129597).length < 2 ^ (prefixWord ++ tailWord_1129597).sum := by decide
  have hdescent : baseEnd_1129597 < baseStart_1129597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129628 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1129628 : Nat := 118140960795 + 1129628 * 2 ^ 59
def prefixEnd_1129628 : Nat := 4983230072969 + 3 ^ 40 * 1129628 * 2
def baseEnd_1129628 : Nat := 257796499900982915091085

theorem tailTrace_1129628 : CollatzResearch.WordTrace tailWord_1129628 prefixEnd_1129628 257796499900982915091085 := by
  unfold tailWord_1129628
  simp only [CollatzResearch.WordTrace]
  refine ⟨20600458975779077973978769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27467278634372103965305025 20600458975779077973978769)
  ·
    refine ⟨15450344231834308480484077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20600458975779077973978769 15450344231834308480484077)
    ·
      refine ⟨5793879086937865680181529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15450344231834308480484077 5793879086937865680181529)
      ·
        refine ⟨4345409315203399260136147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5793879086937865680181529 4345409315203399260136147)
        ·
          refine ⟨6518113972805098890204221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345409315203399260136147 6518113972805098890204221)
          ·
            refine ⟨2444292739801912083826583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6518113972805098890204221 2444292739801912083826583)
            ·
              refine ⟨3666439109702868125739875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2444292739801912083826583 3666439109702868125739875)
              ·
                refine ⟨5499658664554302188609813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666439109702868125739875 5499658664554302188609813)
                ·
                  refine ⟨257796499900982915091085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5499658664554302188609813 257796499900982915091085)
                  ·
                    rfl

theorem cell21_1129628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1129628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129628 prefixEnd_1129628 := by exact prefixLift 1129628
  have htrace : WordTrace (prefixWord ++ tailWord_1129628) baseStart_1129628 baseEnd_1129628 := by
    simpa [prefixWord, tailWord_1129628, baseEnd_1129628] using wordTrace_append hprefix tailTrace_1129628
  have hstable : (prefixWord ++ tailWord_1129628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129628).length < 2 ^ (prefixWord ++ tailWord_1129628).sum := by decide
  have hdescent : baseEnd_1129628 < baseStart_1129628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129656 : List Nat := [2, 1, 2, 1, 2, 1, 2, 3, 7]
def baseStart_1129656 : Nat := 118140960795 + 1129656 * 2 ^ 59
def prefixEnd_1129656 : Nat := 4983230072969 + 3 ^ 40 * 1129656 * 2
def baseEnd_1129656 : Nat := 257802889882461088624361

theorem tailTrace_1129656 : CollatzResearch.WordTrace tailWord_1129656 prefixEnd_1129656 257802889882461088624361 := by
  unfold tailWord_1129656
  simp only [CollatzResearch.WordTrace]
  refine ⟨20600969597728358364988411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27467959463637811153317881 20600969597728358364988411)
  ·
    refine ⟨30901454396592537547482617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20600969597728358364988411 30901454396592537547482617)
    ·
      refine ⟨23176090797444403160611963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30901454396592537547482617 23176090797444403160611963)
      ·
        refine ⟨34764136196166604740917945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23176090797444403160611963 34764136196166604740917945)
        ·
          refine ⟨26073102147124953555688459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34764136196166604740917945 26073102147124953555688459)
          ·
            refine ⟨39109653220687430333532689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26073102147124953555688459 39109653220687430333532689)
            ·
              refine ⟨29332239915515572750149517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39109653220687430333532689 29332239915515572750149517)
              ·
                refine ⟨10999589968318339781306069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29332239915515572750149517 10999589968318339781306069)
                ·
                  refine ⟨257802889882461088624361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10999589968318339781306069 257802889882461088624361)
                  ·
                    rfl

theorem cell21_1129656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_1129656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129656 prefixEnd_1129656 := by exact prefixLift 1129656
  have htrace : WordTrace (prefixWord ++ tailWord_1129656) baseStart_1129656 baseEnd_1129656 := by
    simpa [prefixWord, tailWord_1129656, baseEnd_1129656] using wordTrace_append hprefix tailTrace_1129656
  have hstable : (prefixWord ++ tailWord_1129656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129656).length < 2 ^ (prefixWord ++ tailWord_1129656).sum := by decide
  have hdescent : baseEnd_1129656 < baseStart_1129656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129687 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 6]
def baseStart_1129687 : Nat := 118140960795 + 1129687 * 2 ^ 59
def prefixEnd_1129687 : Nat := 4983230072969 + 3 ^ 40 * 1129687 * 2
def baseEnd_1129687 : Nat := 257809964504811923607631

theorem tailTrace_1129687 : CollatzResearch.WordTrace tailWord_1129687 prefixEnd_1129687 257809964504811923607631 := by
  unfold tailWord_1129687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41203069858344409024355315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27468713238896272682903543 41203069858344409024355315)
  ·
    refine ⟨61804604787516613536532973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41203069858344409024355315 61804604787516613536532973)
    ·
      refine ⟨23176726795318730076199865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61804604787516613536532973 23176726795318730076199865)
      ·
        refine ⟨17382545096489047557149899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23176726795318730076199865 17382545096489047557149899)
        ·
          refine ⟨26073817644733571335724849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17382545096489047557149899 26073817644733571335724849)
          ·
            refine ⟨19555363233550178501793637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26073817644733571335724849 19555363233550178501793637)
            ·
              refine ⟨3666630606290658469086307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19555363233550178501793637 3666630606290658469086307)
              ·
                refine ⟨5499945909435987703629461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3666630606290658469086307 5499945909435987703629461)
                ·
                  refine ⟨257809964504811923607631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5499945909435987703629461 257809964504811923607631)
                  ·
                    rfl

theorem cell21_1129687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_1129687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129687 prefixEnd_1129687 := by exact prefixLift 1129687
  have htrace : WordTrace (prefixWord ++ tailWord_1129687) baseStart_1129687 baseEnd_1129687 := by
    simpa [prefixWord, tailWord_1129687, baseEnd_1129687] using wordTrace_append hprefix tailTrace_1129687
  have hstable : (prefixWord ++ tailWord_1129687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129687).length < 2 ^ (prefixWord ++ tailWord_1129687).sum := by decide
  have hdescent : baseEnd_1129687 < baseStart_1129687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129704 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 4]
def baseStart_1129704 : Nat := 118140960795 + 1129704 * 2 ^ 59
def prefixEnd_1129704 : Nat := 4983230072969 + 3 ^ 40 * 1129704 * 2
def baseEnd_1129704 : Nat := 257813844136423671824263

theorem tailTrace_1129704 : CollatzResearch.WordTrace tailWord_1129704 prefixEnd_1129704 257813844136423671824263 := by
  unfold tailWord_1129704
  simp only [CollatzResearch.WordTrace]
  refine ⟨20601844949641410463862083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27469126599521880618482777 20601844949641410463862083)
  ·
    refine ⟨30902767424462115695793125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20601844949641410463862083 30902767424462115695793125)
    ·
      refine ⟨5794268892086646692961211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30902767424462115695793125 5794268892086646692961211)
      ·
        refine ⟨8691403338129970039441817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5794268892086646692961211 8691403338129970039441817)
        ·
          refine ⟨6518552503597477529581363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8691403338129970039441817 6518552503597477529581363)
          ·
            refine ⟨9777828755396216294372045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518552503597477529581363 9777828755396216294372045)
            ·
              refine ⟨3666685783273581110389517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9777828755396216294372045 3666685783273581110389517)
              ·
                refine ⟨1375007168727592916396069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3666685783273581110389517 1375007168727592916396069)
                ·
                  refine ⟨257813844136423671824263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375007168727592916396069 257813844136423671824263)
                  ·
                    rfl

theorem cell21_1129704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_1129704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129704 prefixEnd_1129704 := by exact prefixLift 1129704
  have htrace : WordTrace (prefixWord ++ tailWord_1129704) baseStart_1129704 baseEnd_1129704 := by
    simpa [prefixWord, tailWord_1129704, baseEnd_1129704] using wordTrace_append hprefix tailTrace_1129704
  have hstable : (prefixWord ++ tailWord_1129704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129704).length < 2 ^ (prefixWord ++ tailWord_1129704).sum := by decide
  have hdescent : baseEnd_1129704 < baseStart_1129704 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129780 : List Nat := [2, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1129780 : Nat := 118140960795 + 1129780 * 2 ^ 59
def prefixEnd_1129780 : Nat := 4983230072969 + 3 ^ 40 * 1129780 * 2
def baseEnd_1129780 : Nat := 257831188371864428557441

theorem tailTrace_1129780 : CollatzResearch.WordTrace tailWord_1129780 prefixEnd_1129780 257831188371864428557441 := by
  unfold tailWord_1129780
  simp only [CollatzResearch.WordTrace]
  refine ⟨20603230923503742953745397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27470974564671657271660529 20603230923503742953745397)
  ·
    refine ⟨1931552899078475901913631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20603230923503742953745397 1931552899078475901913631)
    ·
      refine ⟨2897329348617713852870447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931552899078475901913631 2897329348617713852870447)
      ·
        refine ⟨4345994022926570779305671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897329348617713852870447 4345994022926570779305671)
        ·
          refine ⟨6518991034389856168958507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4345994022926570779305671 6518991034389856168958507)
          ·
            refine ⟨9778486551584784253437761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6518991034389856168958507 9778486551584784253437761)
            ·
              refine ⟨7333864913688588190078321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9778486551584784253437761 7333864913688588190078321)
              ·
                refine ⟨5500398685266441142558741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7333864913688588190078321 5500398685266441142558741)
                ·
                  refine ⟨257831188371864428557441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5500398685266441142558741 257831188371864428557441)
                  ·
                    rfl

theorem cell21_1129780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1129780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129780 prefixEnd_1129780 := by exact prefixLift 1129780
  have htrace : WordTrace (prefixWord ++ tailWord_1129780) baseStart_1129780 baseEnd_1129780 := by
    simpa [prefixWord, tailWord_1129780, baseEnd_1129780] using wordTrace_append hprefix tailTrace_1129780
  have hstable : (prefixWord ++ tailWord_1129780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129780).length < 2 ^ (prefixWord ++ tailWord_1129780).sum := by decide
  have hdescent : baseEnd_1129780 < baseStart_1129780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129859 : List Nat := [1, 1, 1, 3, 5, 2, 3, 2, 3]
def baseStart_1129859 : Nat := 118140960795 + 1129859 * 2 ^ 59
def prefixEnd_1129859 : Nat := 4983230072969 + 3 ^ 40 * 1129859 * 2
def baseEnd_1129859 : Nat := 257849217248177846740613

theorem tailTrace_1129859 : CollatzResearch.WordTrace tailWord_1129859 prefixEnd_1129859 257849217248177846740613 := by
  unfold tailWord_1129859
  simp only [CollatzResearch.WordTrace]
  refine ⟨41209343213721282399616631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27472895475814188266411087 41209343213721282399616631)
  ·
    refine ⟨61814014820581923599424947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41209343213721282399616631 61814014820581923599424947)
    ·
      refine ⟨92721022230872885399137421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61814014820581923599424947 92721022230872885399137421)
      ·
        refine ⟨34770383336577332024676533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92721022230872885399137421 34770383336577332024676533)
        ·
          refine ⟨3259723437804124877313425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34770383336577332024676533 3259723437804124877313425)
          ·
            refine ⟨2444792578353093657985069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3259723437804124877313425 2444792578353093657985069)
            ·
              refine ⟨916797216882410121744401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2444792578353093657985069 916797216882410121744401)
              ·
                refine ⟨687597912661807591308301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 916797216882410121744401 687597912661807591308301)
                ·
                  refine ⟨257849217248177846740613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687597912661807591308301 257849217248177846740613)
                  ·
                    rfl

theorem cell21_1129859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 2, 3].length) (baseStart_1129859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129859 prefixEnd_1129859 := by exact prefixLift 1129859
  have htrace : WordTrace (prefixWord ++ tailWord_1129859) baseStart_1129859 baseEnd_1129859 := by
    simpa [prefixWord, tailWord_1129859, baseEnd_1129859] using wordTrace_append hprefix tailTrace_1129859
  have hstable : (prefixWord ++ tailWord_1129859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129859).length < 2 ^ (prefixWord ++ tailWord_1129859).sum := by decide
  have hdescent : baseEnd_1129859 < baseStart_1129859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129932 : List Nat := [2, 2, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1129932 : Nat := 118140960795 + 1129932 * 2 ^ 59
def prefixEnd_1129932 : Nat := 4983230072969 + 3 ^ 40 * 1129932 * 2
def baseEnd_1129932 : Nat := 257865876842745942023797

theorem tailTrace_1129932 : CollatzResearch.WordTrace tailWord_1129932 prefixEnd_1129932 257865876842745942023797 := by
  unfold tailWord_1129932
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606002871228407933512025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27474670494971210578016033 20606002871228407933512025)
  ·
    refine ⟨15454502153421305950134019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20606002871228407933512025 15454502153421305950134019)
    ·
      refine ⟨23181753230131958925201029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15454502153421305950134019 23181753230131958925201029)
      ·
        refine ⟨4346578730649742298475193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23181753230131958925201029 4346578730649742298475193)
        ·
          refine ⟨3259934047987306723856395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4346578730649742298475193 3259934047987306723856395)
          ·
            refine ⟨4889901071980960085784593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3259934047987306723856395 4889901071980960085784593)
            ·
              refine ⟨3667425803985720064338445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4889901071980960085784593 3667425803985720064338445)
              ·
                refine ⟨1375284676494645024126917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3667425803985720064338445 1375284676494645024126917)
                ·
                  refine ⟨257865876842745942023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375284676494645024126917 257865876842745942023797)
                  ·
                    rfl

theorem cell21_1129932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1129932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129932 prefixEnd_1129932 := by exact prefixLift 1129932
  have htrace : WordTrace (prefixWord ++ tailWord_1129932) baseStart_1129932 baseEnd_1129932 := by
    simpa [prefixWord, tailWord_1129932, baseEnd_1129932] using wordTrace_append hprefix tailTrace_1129932
  have hstable : (prefixWord ++ tailWord_1129932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129932).length < 2 ^ (prefixWord ++ tailWord_1129932).sum := by decide
  have hdescent : baseEnd_1129932 < baseStart_1129932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1129960 : List Nat := [2, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_1129960 : Nat := 118140960795 + 1129960 * 2 ^ 59
def prefixEnd_1129960 : Nat := 4983230072969 + 3 ^ 40 * 1129960 * 2
def baseEnd_1129960 : Nat := 257872266824224115557073

theorem tailTrace_1129960 : CollatzResearch.WordTrace tailWord_1129960 prefixEnd_1129960 257872266824224115557073 := by
  unfold tailWord_1129960
  simp only [CollatzResearch.WordTrace]
  refine ⟨20606513493177688324521667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27475351324236917766028889 20606513493177688324521667)
  ·
    refine ⟨30909770239766532486782501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20606513493177688324521667 30909770239766532486782501)
    ·
      refine ⟨5795581919956224841271719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30909770239766532486782501 5795581919956224841271719)
      ·
        refine ⟨8693372879934337261907579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5795581919956224841271719 8693372879934337261907579)
        ·
          refine ⟨13040059319901505892861369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8693372879934337261907579 13040059319901505892861369)
          ·
            refine ⟨9780044489926129419646027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13040059319901505892861369 9780044489926129419646027)
            ·
              refine ⟨14670066734889194129469041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780044489926129419646027 14670066734889194129469041)
              ·
                refine ⟨11002550051166895597101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14670066734889194129469041 11002550051166895597101781)
                ·
                  refine ⟨257872266824224115557073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11002550051166895597101781 257872266824224115557073)
                  ·
                    rfl

theorem cell21_1129960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_1129960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1129960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1129960 prefixEnd_1129960 := by exact prefixLift 1129960
  have htrace : WordTrace (prefixWord ++ tailWord_1129960) baseStart_1129960 baseEnd_1129960 := by
    simpa [prefixWord, tailWord_1129960, baseEnd_1129960] using wordTrace_append hprefix tailTrace_1129960
  have hstable : (prefixWord ++ tailWord_1129960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1129960).length < 2 ^ (prefixWord ++ tailWord_1129960).sum := by decide
  have hdescent : baseEnd_1129960 < baseStart_1129960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1129960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130014 : List Nat := [4, 3, 3, 1, 2, 1, 7]
def baseStart_1130014 : Nat := 118140960795 + 1130014 * 2 ^ 59
def prefixEnd_1130014 : Nat := 4983230072969 + 3 ^ 40 * 1130014 * 2
def baseEnd_1130014 : Nat := 28653843373325780184107

theorem tailTrace_1130014 : CollatzResearch.WordTrace tailWord_1130014 prefixEnd_1130014 28653843373325780184107 := by
  unfold tailWord_1130014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151874566019967983938637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27476664352106495914339397 5151874566019967983938637)
  ·
    refine ⟨1931952962257487993976989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5151874566019967983938637 1931952962257487993976989)
    ·
      refine ⟨724482360846557997741371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1931952962257487993976989 724482360846557997741371)
      ·
        refine ⟨1086723541269836996612057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 724482360846557997741371 1086723541269836996612057)
        ·
          refine ⟨815042655952377747459043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1086723541269836996612057 815042655952377747459043)
          ·
            refine ⟨1222563983928566621188565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815042655952377747459043 1222563983928566621188565)
            ·
              refine ⟨28653843373325780184107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1222563983928566621188565 28653843373325780184107)
              ·
                rfl

theorem cell21_1130014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 7].length) (baseStart_1130014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130014 prefixEnd_1130014 := by exact prefixLift 1130014
  have htrace : WordTrace (prefixWord ++ tailWord_1130014) baseStart_1130014 baseEnd_1130014 := by
    simpa [prefixWord, tailWord_1130014, baseEnd_1130014] using wordTrace_append hprefix tailTrace_1130014
  have hstable : (prefixWord ++ tailWord_1130014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130014).length < 2 ^ (prefixWord ++ tailWord_1130014).sum := by decide
  have hdescent : baseEnd_1130014 < baseStart_1130014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130084 : List Nat := [2, 3, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1130084 : Nat := 118140960795 + 1130084 * 2 ^ 59
def prefixEnd_1130084 : Nat := 4983230072969 + 3 ^ 40 * 1130084 * 2
def baseEnd_1130084 : Nat := 257900565313627455490153

theorem tailTrace_1130084 : CollatzResearch.WordTrace tailWord_1130084 prefixEnd_1130084 257900565313627455490153 := by
  unfold tailWord_1130084
  simp only [CollatzResearch.WordTrace]
  refine ⟨20608774818953072913278653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27478366425270763884371537 20608774818953072913278653)
  ·
    refine ⟨7728290557107402342479495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20608774818953072913278653 7728290557107402342479495)
    ·
      refine ⟨11592435835661103513719243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7728290557107402342479495 11592435835661103513719243)
      ·
        refine ⟨17388653753491655270578865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11592435835661103513719243 17388653753491655270578865)
        ·
          refine ⟨13041490315118741452934149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17388653753491655270578865 13041490315118741452934149)
          ·
            refine ⟨2445279434084764022425153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13041490315118741452934149 2445279434084764022425153)
            ·
              refine ⟨1833959575563573016818865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2445279434084764022425153 1833959575563573016818865)
              ·
                refine ⟨1375469681672679762614149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833959575563573016818865 1375469681672679762614149)
                ·
                  refine ⟨257900565313627455490153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375469681672679762614149 257900565313627455490153)
                  ·
                    rfl

theorem cell21_1130084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1130084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130084 prefixEnd_1130084 := by exact prefixLift 1130084
  have htrace : WordTrace (prefixWord ++ tailWord_1130084) baseStart_1130084 baseEnd_1130084 := by
    simpa [prefixWord, tailWord_1130084, baseEnd_1130084] using wordTrace_append hprefix tailTrace_1130084
  have hstable : (prefixWord ++ tailWord_1130084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130084).length < 2 ^ (prefixWord ++ tailWord_1130084).sum := by decide
  have hdescent : baseEnd_1130084 < baseStart_1130084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130098 : List Nat := [3, 2, 1, 2, 3, 1, 3, 6]
def baseStart_1130098 : Nat := 118140960795 + 1130098 * 2 ^ 59
def prefixEnd_1130098 : Nat := 4983230072969 + 3 ^ 40 * 1130098 * 2
def baseEnd_1130098 : Nat := 85967920101455514085597

theorem tailTrace_1130098 : CollatzResearch.WordTrace tailWord_1130098 prefixEnd_1130098 85967920101455514085597 := by
  unfold tailWord_1130098
  simp only [CollatzResearch.WordTrace]
  refine ⟨10304515064963856554391737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27478706839903617478377965 10304515064963856554391737)
  ·
    refine ⟨7728386298722892415793803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10304515064963856554391737 7728386298722892415793803)
    ·
      refine ⟨11592579448084338623690705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7728386298722892415793803 11592579448084338623690705)
      ·
        refine ⟨8694434586063253967768029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11592579448084338623690705 8694434586063253967768029)
        ·
          refine ⟨3260412969773720237913011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8694434586063253967768029 3260412969773720237913011)
          ·
            refine ⟨4890619454660580356869517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3260412969773720237913011 4890619454660580356869517)
            ·
              refine ⟨1833982295497717633826069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4890619454660580356869517 1833982295497717633826069)
              ·
                refine ⟨85967920101455514085597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1833982295497717633826069 85967920101455514085597)
                ·
                  rfl

theorem cell21_1130098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 6].length) (baseStart_1130098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130098 prefixEnd_1130098 := by exact prefixLift 1130098
  have htrace : WordTrace (prefixWord ++ tailWord_1130098) baseStart_1130098 baseEnd_1130098 := by
    simpa [prefixWord, tailWord_1130098, baseEnd_1130098] using wordTrace_append hprefix tailTrace_1130098
  have hstable : (prefixWord ++ tailWord_1130098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130098).length < 2 ^ (prefixWord ++ tailWord_1130098).sum := by decide
  have hdescent : baseEnd_1130098 < baseStart_1130098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130112 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_1130112 : Nat := 118140960795 + 1130112 * 2 ^ 59
def prefixEnd_1130112 : Nat := 4983230072969 + 3 ^ 40 * 1130112 * 2
def baseEnd_1130112 : Nat := 257906955295105629023429

theorem tailTrace_1130112 : CollatzResearch.WordTrace tailWord_1130112 prefixEnd_1130112 257906955295105629023429 := by
  unfold tailWord_1130112
  simp only [CollatzResearch.WordTrace]
  refine ⟨20609285440902353304288295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27479047254536471072384393 20609285440902353304288295)
  ·
    refine ⟨30913928161353529956432443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20609285440902353304288295 30913928161353529956432443)
    ·
      refine ⟨46370892242030294934648665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30913928161353529956432443 46370892242030294934648665)
      ·
        refine ⟨34778169181522721200986499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46370892242030294934648665 34778169181522721200986499)
        ·
          refine ⟨52167253772284081801479749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34778169181522721200986499 52167253772284081801479749)
          ·
            refine ⟨9781360082303265337777453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52167253772284081801479749 9781360082303265337777453)
            ·
              refine ⟨3668010030863724501666545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9781360082303265337777453 3668010030863724501666545)
              ·
                refine ⟨2751007523147793376249909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3668010030863724501666545 2751007523147793376249909)
                ·
                  refine ⟨257906955295105629023429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2751007523147793376249909 257906955295105629023429)
                  ·
                    rfl

theorem cell21_1130112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_1130112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130112 prefixEnd_1130112 := by exact prefixLift 1130112
  have htrace : WordTrace (prefixWord ++ tailWord_1130112) baseStart_1130112 baseEnd_1130112 := by
    simpa [prefixWord, tailWord_1130112, baseEnd_1130112] using wordTrace_append hprefix tailTrace_1130112
  have hstable : (prefixWord ++ tailWord_1130112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130112).length < 2 ^ (prefixWord ++ tailWord_1130112).sum := by decide
  have hdescent : baseEnd_1130112 < baseStart_1130112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130174 : List Nat := [4, 2, 1, 1, 2, 3, 1, 7]
def baseStart_1130174 : Nat := 118140960795 + 1130174 * 2 ^ 59
def prefixEnd_1130174 : Nat := 4983230072969 + 3 ^ 40 * 1130174 * 2
def baseEnd_1130174 : Nat := 85973701513269099663323

theorem tailTrace_1130174 : CollatzResearch.WordTrace tailWord_1130174 prefixEnd_1130174 85973701513269099663323 := by
  unfold tailWord_1130174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152604025947511399666697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27480554805053394131555717 5152604025947511399666697)
  ·
    refine ⟨3864453019460633549750023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5152604025947511399666697 3864453019460633549750023)
    ·
      refine ⟨5796679529190950324625035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3864453019460633549750023 5796679529190950324625035)
      ·
        refine ⟨8695019293786425486937553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796679529190950324625035 8695019293786425486937553)
        ·
          refine ⟨6521264470339819115203165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8695019293786425486937553 6521264470339819115203165)
          ·
            refine ⟨2445474176377432168201187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6521264470339819115203165 2445474176377432168201187)
            ·
              refine ⟨3668211264566148252301781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445474176377432168201187 3668211264566148252301781)
              ·
                refine ⟨85973701513269099663323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3668211264566148252301781 85973701513269099663323)
                ·
                  rfl

theorem cell21_1130174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_1130174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130174 prefixEnd_1130174 := by exact prefixLift 1130174
  have htrace : WordTrace (prefixWord ++ tailWord_1130174) baseStart_1130174 baseEnd_1130174 := by
    simpa [prefixWord, tailWord_1130174, baseEnd_1130174] using wordTrace_append hprefix tailTrace_1130174
  have hstable : (prefixWord ++ tailWord_1130174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130174).length < 2 ^ (prefixWord ++ tailWord_1130174).sum := by decide
  have hdescent : baseEnd_1130174 < baseStart_1130174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130298 : List Nat := [3, 1, 1, 1, 5, 2, 2, 3, 3]
def baseStart_1130298 : Nat := 118140960795 + 1130298 * 2 ^ 59
def prefixEnd_1130298 : Nat := 4983230072969 + 3 ^ 40 * 1130298 * 2
def baseEnd_1130298 : Nat := 257949403029210638923049

theorem tailTrace_1130298 : CollatzResearch.WordTrace tailWord_1130298 prefixEnd_1130298 257949403029210638923049 := by
  unfold tailWord_1130298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10306338714782715093711887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27483569906087240249898365 10306338714782715093711887)
  ·
    refine ⟨15459508072174072640567831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10306338714782715093711887 15459508072174072640567831)
    ·
      refine ⟨23189262108261108960851747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15459508072174072640567831 23189262108261108960851747)
      ·
        refine ⟨34783893162391663441277621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23189262108261108960851747 34783893162391663441277621)
        ·
          refine ⟨3260989983974218447619777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34783893162391663441277621 3260989983974218447619777)
          ·
            refine ⟨2445742487980663835714833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3260989983974218447619777 2445742487980663835714833)
            ·
              refine ⟨1834306865985497876786125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2445742487980663835714833 1834306865985497876786125)
              ·
                refine ⟨687865074744561703794797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1834306865985497876786125 687865074744561703794797)
                ·
                  refine ⟨257949403029210638923049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 687865074744561703794797 257949403029210638923049)
                  ·
                    rfl

theorem cell21_1130298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 3, 3].length) (baseStart_1130298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130298 prefixEnd_1130298 := by exact prefixLift 1130298
  have htrace : WordTrace (prefixWord ++ tailWord_1130298) baseStart_1130298 baseEnd_1130298 := by
    simpa [prefixWord, tailWord_1130298, baseEnd_1130298] using wordTrace_append hprefix tailTrace_1130298
  have hstable : (prefixWord ++ tailWord_1130298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130298).length < 2 ^ (prefixWord ++ tailWord_1130298).sum := by decide
  have hdescent : baseEnd_1130298 < baseStart_1130298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130312 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 4]
def baseStart_1130312 : Nat := 118140960795 + 1130312 * 2 ^ 59
def prefixEnd_1130312 : Nat := 4983230072969 + 3 ^ 40 * 1130312 * 2
def baseEnd_1130312 : Nat := 257952598019949725689687

theorem tailTrace_1130312 : CollatzResearch.WordTrace tailWord_1130312 prefixEnd_1130312 257952598019949725689687 := by
  unfold tailWord_1130312
  simp only [CollatzResearch.WordTrace]
  refine ⟨20612932740540070382928595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27483910320720093843904793 20612932740540070382928595)
  ·
    refine ⟨30919399110810105574392893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20612932740540070382928595 30919399110810105574392893)
    ·
      refine ⟨11594774666553789590397335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30919399110810105574392893 11594774666553789590397335)
      ·
        refine ⟨17392161999830684385596003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11594774666553789590397335 17392161999830684385596003)
        ·
          refine ⟨26088242999746026578394005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17392161999830684385596003 26088242999746026578394005)
          ·
            refine ⟨1222886390613094995862219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 26088242999746026578394005 1222886390613094995862219)
            ·
              refine ⟨1834329585919642493793329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222886390613094995862219 1834329585919642493793329)
              ·
                refine ⟨1375747189439731870344997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834329585919642493793329 1375747189439731870344997)
                ·
                  refine ⟨257952598019949725689687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375747189439731870344997 257952598019949725689687)
                  ·
                    rfl

theorem cell21_1130312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 4].length) (baseStart_1130312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130312 prefixEnd_1130312 := by exact prefixLift 1130312
  have htrace : WordTrace (prefixWord ++ tailWord_1130312) baseStart_1130312 baseEnd_1130312 := by
    simpa [prefixWord, tailWord_1130312, baseEnd_1130312] using wordTrace_append hprefix tailTrace_1130312
  have hstable : (prefixWord ++ tailWord_1130312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130312).length < 2 ^ (prefixWord ++ tailWord_1130312).sum := by decide
  have hdescent : baseEnd_1130312 < baseStart_1130312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130388 : List Nat := [2, 4, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1130388 : Nat := 118140960795 + 1130388 * 2 ^ 59
def prefixEnd_1130388 : Nat := 4983230072969 + 3 ^ 40 * 1130388 * 2
def baseEnd_1130388 : Nat := 257969942255390482422865

theorem tailTrace_1130388 : CollatzResearch.WordTrace tailWord_1130388 prefixEnd_1130388 257969942255390482422865 := by
  unfold tailWord_1130388
  simp only [CollatzResearch.WordTrace]
  refine ⟨20614318714402402872811909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27485758285869870497082545 20614318714402402872811909)
  ·
    refine ⟨3865184758950450538652233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20614318714402402872811909 3865184758950450538652233)
    ·
      refine ⟨2898888569212837903989175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3865184758950450538652233 2898888569212837903989175)
      ·
        refine ⟨4348332853819256855983763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2898888569212837903989175 4348332853819256855983763)
        ·
          refine ⟨6522499280728885283975645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4348332853819256855983763 6522499280728885283975645)
          ·
            refine ⟨2445937230273331981490867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6522499280728885283975645 2445937230273331981490867)
            ·
              refine ⟨3668905845409997972236301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2445937230273331981490867 3668905845409997972236301)
              ·
                refine ⟨1375839692028749239588613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3668905845409997972236301 1375839692028749239588613)
                ·
                  refine ⟨257969942255390482422865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375839692028749239588613 257969942255390482422865)
                  ·
                    rfl

theorem cell21_1130388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1130388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130388 prefixEnd_1130388 := by exact prefixLift 1130388
  have htrace : WordTrace (prefixWord ++ tailWord_1130388) baseStart_1130388 baseEnd_1130388 := by
    simpa [prefixWord, tailWord_1130388, baseEnd_1130388] using wordTrace_append hprefix tailTrace_1130388
  have hstable : (prefixWord ++ tailWord_1130388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130388).length < 2 ^ (prefixWord ++ tailWord_1130388).sum := by decide
  have hdescent : baseEnd_1130388 < baseStart_1130388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130481 : List Nat := [1, 2, 2, 2, 6, 1, 1, 2, 4]
def baseStart_1130481 : Nat := 118140960795 + 1130481 * 2 ^ 59
def prefixEnd_1130481 : Nat := 4983230072969 + 3 ^ 40 * 1130481 * 2
def baseEnd_1130481 : Nat := 257991166122442987372675

theorem tailTrace_1130481 : CollatzResearch.WordTrace tailWord_1130481 prefixEnd_1130481 257991166122442987372675 := by
  unfold tailWord_1130481
  simp only [CollatzResearch.WordTrace]
  refine ⟨41232029417467882628759297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27488019611645255085839531 41232029417467882628759297)
  ·
    refine ⟨30924022063100911971569473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41232029417467882628759297 30924022063100911971569473)
    ·
      refine ⟨23193016547325683978677105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30924022063100911971569473 23193016547325683978677105)
      ·
        refine ⟨17394762410494262984007829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23193016547325683978677105 17394762410494262984007829)
        ·
          refine ⟨815379487991918577375367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 17394762410494262984007829 815379487991918577375367)
          ·
            refine ⟨1223069231987877866063051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815379487991918577375367 1223069231987877866063051)
            ·
              refine ⟨1834603847981816799094577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223069231987877866063051 1834603847981816799094577)
              ·
                refine ⟨1375952885986362599320933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834603847981816799094577 1375952885986362599320933)
                ·
                  refine ⟨257991166122442987372675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1375952885986362599320933 257991166122442987372675)
                  ·
                    rfl

theorem cell21_1130481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 4].length) (baseStart_1130481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130481 prefixEnd_1130481 := by exact prefixLift 1130481
  have htrace : WordTrace (prefixWord ++ tailWord_1130481) baseStart_1130481 baseEnd_1130481 := by
    simpa [prefixWord, tailWord_1130481, baseEnd_1130481] using wordTrace_append hprefix tailTrace_1130481
  have hstable : (prefixWord ++ tailWord_1130481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130481).length < 2 ^ (prefixWord ++ tailWord_1130481).sum := by decide
  have hdescent : baseEnd_1130481 < baseStart_1130481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130492 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1130492 : Nat := 118140960795 + 1130492 * 2 ^ 59
def prefixEnd_1130492 : Nat := 4983230072969 + 3 ^ 40 * 1130492 * 2
def baseEnd_1130492 : Nat := 257993676472309412689319

theorem tailTrace_1130492 : CollatzResearch.WordTrace tailWord_1130492 prefixEnd_1130492 257993676472309412689319 := by
  unfold tailWord_1130492
  simp only [CollatzResearch.WordTrace]
  refine ⟨20616215310214015753704865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27488287080285354338273153 20616215310214015753704865)
  ·
    refine ⟨15462161482660511815278649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20616215310214015753704865 15462161482660511815278649)
    ·
      refine ⟨11596621111995383861458987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15462161482660511815278649 11596621111995383861458987)
      ·
        refine ⟨17394931667993075792188481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11596621111995383861458987 17394931667993075792188481)
        ·
          refine ⟨13046198750994806844141361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17394931667993075792188481 13046198750994806844141361)
          ·
            refine ⟨9784649063246105133106021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13046198750994806844141361 9784649063246105133106021)
            ·
              refine ⟨1834621699358644712457379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9784649063246105133106021 1834621699358644712457379)
              ·
                refine ⟨2751932549037967068686069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1834621699358644712457379 2751932549037967068686069)
                ·
                  refine ⟨257993676472309412689319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2751932549037967068686069 257993676472309412689319)
                  ·
                    rfl

theorem cell21_1130492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1130492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130492 prefixEnd_1130492 := by exact prefixLift 1130492
  have htrace : WordTrace (prefixWord ++ tailWord_1130492) baseStart_1130492 baseEnd_1130492 := by
    simpa [prefixWord, tailWord_1130492, baseEnd_1130492] using wordTrace_append hprefix tailTrace_1130492
  have hstable : (prefixWord ++ tailWord_1130492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130492).length < 2 ^ (prefixWord ++ tailWord_1130492).sum := by decide
  have hdescent : baseEnd_1130492 < baseStart_1130492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130599 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 4]
def baseStart_1130599 : Nat := 118140960795 + 1130599 * 2 ^ 59
def prefixEnd_1130599 : Nat := 4983230072969 + 3 ^ 40 * 1130599 * 2
def baseEnd_1130599 : Nat := 258018095330101004405767

theorem tailTrace_1130599 : CollatzResearch.WordTrace tailWord_1130599 prefixEnd_1130599 258018095330101004405767 := by
  unfold tailWord_1130599
  simp only [CollatzResearch.WordTrace]
  refine ⟨41236333231040388781554851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27490888820693592521036567 41236333231040388781554851)
  ·
    refine ⟨61854499846560583172332277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41236333231040388781554851 61854499846560583172332277)
    ·
      refine ⟨5798859360615054672406151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61854499846560583172332277 5798859360615054672406151)
      ·
        refine ⟨8698289040922582008609227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5798859360615054672406151 8698289040922582008609227)
        ·
          refine ⟨13047433561383873012913841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8698289040922582008609227 13047433561383873012913841)
          ·
            refine ⟨9785575171037904759685381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13047433561383873012913841 9785575171037904759685381)
            ·
              refine ⟨1834795344569607142441009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9785575171037904759685381 1834795344569607142441009)
              ·
                refine ⟨1376096508427205356830757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1834795344569607142441009 1376096508427205356830757)
                ·
                  refine ⟨258018095330101004405767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376096508427205356830757 258018095330101004405767)
                  ·
                    rfl

theorem cell21_1130599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 4].length) (baseStart_1130599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130599 prefixEnd_1130599 := by exact prefixLift 1130599
  have htrace : WordTrace (prefixWord ++ tailWord_1130599) baseStart_1130599 baseEnd_1130599 := by
    simpa [prefixWord, tailWord_1130599, baseEnd_1130599] using wordTrace_append hprefix tailTrace_1130599
  have hstable : (prefixWord ++ tailWord_1130599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130599).length < 2 ^ (prefixWord ++ tailWord_1130599).sum := by decide
  have hdescent : baseEnd_1130599 < baseStart_1130599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130602 : List Nat := [3, 1, 3, 2, 3, 1, 1, 4, 3]
def baseStart_1130602 : Nat := 118140960795 + 1130602 * 2 ^ 59
def prefixEnd_1130602 : Nat := 4983230072969 + 3 ^ 40 * 1130602 * 2
def baseEnd_1130602 : Nat := 258018779970973665855761

theorem tailTrace_1130602 : CollatzResearch.WordTrace tailWord_1130602 prefixEnd_1130602 258018779970973665855761 := by
  unfold tailWord_1130602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10309110662507380073478515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27490961766686346862609373 10309110662507380073478515)
  ·
    refine ⟨15463665993761070110217773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10309110662507380073478515 15463665993761070110217773)
    ·
      refine ⟨5798874747660401291331665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15463665993761070110217773 5798874747660401291331665)
      ·
        refine ⟨4349156060745300968498749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5798874747660401291331665 4349156060745300968498749)
        ·
          refine ⟨1630933522779487863187031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4349156060745300968498749 1630933522779487863187031)
          ·
            refine ⟨2446400284169231794780547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1630933522779487863187031 2446400284169231794780547)
            ·
              refine ⟨3669600426253847692170821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2446400284169231794780547 3669600426253847692170821)
              ·
                refine ⟨688050079922596442282029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3669600426253847692170821 688050079922596442282029)
                ·
                  refine ⟨258018779970973665855761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688050079922596442282029 258018779970973665855761)
                  ·
                    rfl

theorem cell21_1130602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_1130602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130602 prefixEnd_1130602 := by exact prefixLift 1130602
  have htrace : WordTrace (prefixWord ++ tailWord_1130602) baseStart_1130602 baseEnd_1130602 := by
    simpa [prefixWord, tailWord_1130602, baseEnd_1130602] using wordTrace_append hprefix tailTrace_1130602
  have hstable : (prefixWord ++ tailWord_1130602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130602).length < 2 ^ (prefixWord ++ tailWord_1130602).sum := by decide
  have hdescent : baseEnd_1130602 < baseStart_1130602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130627 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_1130627 : Nat := 118140960795 + 1130627 * 2 ^ 59
def prefixEnd_1130627 : Nat := 4983230072969 + 3 ^ 40 * 1130627 * 2
def baseEnd_1130627 : Nat := 258024485311579177939043

theorem tailTrace_1130627 : CollatzResearch.WordTrace tailWord_1130627 prefixEnd_1130627 258024485311579177939043 := by
  unfold tailWord_1130627
  simp only [CollatzResearch.WordTrace]
  refine ⟨41237354474938949563574135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27491569649959299709049423 41237354474938949563574135)
  ·
    refine ⟨61856031712408424345361203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41237354474938949563574135 61856031712408424345361203)
    ·
      refine ⟨92784047568612636518041805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61856031712408424345361203 92784047568612636518041805)
      ·
        refine ⟨34794017838229738694265677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92784047568612636518041805 34794017838229738694265677)
        ·
          refine ⟨13047756689336152010349629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34794017838229738694265677 13047756689336152010349629)
          ·
            refine ⟨4892908758501057003881111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13047756689336152010349629 4892908758501057003881111)
            ·
              refine ⟨7339363137751585505821667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4892908758501057003881111 7339363137751585505821667)
              ·
                refine ⟨11009044706627378258732501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7339363137751585505821667 11009044706627378258732501)
                ·
                  refine ⟨258024485311579177939043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11009044706627378258732501 258024485311579177939043)
                  ·
                    rfl

theorem cell21_1130627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_1130627 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130627 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130627 prefixEnd_1130627 := by exact prefixLift 1130627
  have htrace : WordTrace (prefixWord ++ tailWord_1130627) baseStart_1130627 baseEnd_1130627 := by
    simpa [prefixWord, tailWord_1130627, baseEnd_1130627] using wordTrace_append hprefix tailTrace_1130627
  have hstable : (prefixWord ++ tailWord_1130627).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130627).length < 2 ^ (prefixWord ++ tailWord_1130627).sum := by decide
  have hdescent : baseEnd_1130627 < baseStart_1130627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130858 : List Nat := [3, 1, 3, 3, 1, 1, 4, 5]
def baseStart_1130858 : Nat := 118140960795 + 1130858 * 2 ^ 59
def prefixEnd_1130858 : Nat := 4983230072969 + 3 ^ 40 * 1130858 * 2
def baseEnd_1130858 : Nat := 86025734219591369862857

theorem tailTrace_1130858 : CollatzResearch.WordTrace tailWord_1130858 prefixEnd_1130858 86025734219591369862857 := by
  unfold tailWord_1130858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10311444934275519003808307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27497186491401384010155485 10311444934275519003808307)
  ·
    refine ⟨15467167401413278505712461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10311444934275519003808307 15467167401413278505712461)
    ·
      refine ⟨5800187775529979439642173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15467167401413278505712461 5800187775529979439642173)
      ·
        refine ⟨2175070415823742289865815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5800187775529979439642173 2175070415823742289865815)
        ·
          refine ⟨3262605623735613434798723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175070415823742289865815 3262605623735613434798723)
          ·
            refine ⟨4893908435603420152198085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3262605623735613434798723 4893908435603420152198085)
            ·
              refine ⟨917607831675641278537141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4893908435603420152198085 917607831675641278537141)
              ·
                refine ⟨86025734219591369862857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 917607831675641278537141 86025734219591369862857)
                ·
                  rfl

theorem cell21_1130858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_1130858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130858 prefixEnd_1130858 := by exact prefixLift 1130858
  have htrace : WordTrace (prefixWord ++ tailWord_1130858) baseStart_1130858 baseEnd_1130858 := by
    simpa [prefixWord, tailWord_1130858, baseEnd_1130858] using wordTrace_append hprefix tailTrace_1130858
  have hstable : (prefixWord ++ tailWord_1130858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130858).length < 2 ^ (prefixWord ++ tailWord_1130858).sum := by decide
  have hdescent : baseEnd_1130858 < baseStart_1130858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1130903 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 4]
def baseStart_1130903 : Nat := 118140960795 + 1130903 * 2 ^ 59
def prefixEnd_1130903 : Nat := 4983230072969 + 3 ^ 40 * 1130903 * 2
def baseEnd_1130903 : Nat := 258087472271864031338479

theorem tailTrace_1130903 : CollatzResearch.WordTrace tailWord_1130903 prefixEnd_1130903 258087472271864031338479 := by
  unfold tailWord_1130903
  simp only [CollatzResearch.WordTrace]
  refine ⟨41247421021939048700621363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27498280681292699133747575 41247421021939048700621363)
  ·
    refine ⟨61871131532908573050932045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41247421021939048700621363 61871131532908573050932045)
    ·
      refine ⟨23201674324840714894099517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61871131532908573050932045 23201674324840714894099517)
      ·
        refine ⟨8700627871815268085287319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23201674324840714894099517 8700627871815268085287319)
        ·
          refine ⟨13050941807722902127930979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8700627871815268085287319 13050941807722902127930979)
          ·
            refine ⟨19576412711584353191896469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13050941807722902127930979 19576412711584353191896469)
            ·
              refine ⟨917644345855516555870147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19576412711584353191896469 917644345855516555870147)
              ·
                refine ⟨1376466518783274833805221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 917644345855516555870147 1376466518783274833805221)
                ·
                  refine ⟨258087472271864031338479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376466518783274833805221 258087472271864031338479)
                  ·
                    rfl

theorem cell21_1130903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 4].length) (baseStart_1130903 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1130903 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1130903 prefixEnd_1130903 := by exact prefixLift 1130903
  have htrace : WordTrace (prefixWord ++ tailWord_1130903) baseStart_1130903 baseEnd_1130903 := by
    simpa [prefixWord, tailWord_1130903, baseEnd_1130903] using wordTrace_append hprefix tailTrace_1130903
  have hstable : (prefixWord ++ tailWord_1130903).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1130903).length < 2 ^ (prefixWord ++ tailWord_1130903).sum := by decide
  have hdescent : baseEnd_1130903 < baseStart_1130903 := by decide
  rcases family_descends (prefixWord ++ tailWord_1130903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131007 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 5]
def baseStart_1131007 : Nat := 118140960795 + 1131007 * 2 ^ 59
def prefixEnd_1131007 : Nat := 4983230072969 + 3 ^ 40 * 1131007 * 2
def baseEnd_1131007 : Nat := 258111206488782961604933

theorem tailTrace_1131007 : CollatzResearch.WordTrace tailWord_1131007 prefixEnd_1131007 258111206488782961604933 := by
  unfold tailWord_1131007
  simp only [CollatzResearch.WordTrace]
  refine ⟨41251214213562274462407275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27500809475708182974938183 41251214213562274462407275)
  ·
    refine ⟨61876821320343411693610913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41251214213562274462407275 61876821320343411693610913)
    ·
      refine ⟨46407615990257558770208185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61876821320343411693610913 46407615990257558770208185)
      ·
        refine ⟨34805711992693169077656139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46407615990257558770208185 34805711992693169077656139)
        ·
          refine ⟨52208567989039753616484209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34805711992693169077656139 52208567989039753616484209)
          ·
            refine ⟨39156425991779815212363157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52208567989039753616484209 39156425991779815212363157)
            ·
              refine ⟨1835457468364678838079523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39156425991779815212363157 1835457468364678838079523)
              ·
                refine ⟨2753186202547018257119285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1835457468364678838079523 2753186202547018257119285)
                ·
                  refine ⟨258111206488782961604933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2753186202547018257119285 258111206488782961604933)
                  ·
                    rfl

theorem cell21_1131007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 5].length) (baseStart_1131007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131007 prefixEnd_1131007 := by exact prefixLift 1131007
  have htrace : WordTrace (prefixWord ++ tailWord_1131007) baseStart_1131007 baseEnd_1131007 := by
    simpa [prefixWord, tailWord_1131007, baseEnd_1131007] using wordTrace_append hprefix tailTrace_1131007
  have hstable : (prefixWord ++ tailWord_1131007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131007).length < 2 ^ (prefixWord ++ tailWord_1131007).sum := by decide
  have hdescent : baseEnd_1131007 < baseStart_1131007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131069 : List Nat := [1, 4, 1, 3, 2, 2, 2, 6]
def baseStart_1131069 : Nat := 118140960795 + 1131069 * 2 ^ 59
def prefixEnd_1131069 : Nat := 4983230072969 + 3 ^ 40 * 1131069 * 2
def baseEnd_1131069 : Nat := 86041785244494877190491

theorem tailTrace_1131069 : CollatzResearch.WordTrace tailWord_1131069 prefixEnd_1131069 86041785244494877190491 := by
  unfold tailWord_1131069
  simp only [CollatzResearch.WordTrace]
  refine ⟨41253475539337659051164261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27502317026225106034109507 41253475539337659051164261)
  ·
    refine ⟨7735026663625811072093299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41253475539337659051164261 7735026663625811072093299)
    ·
      refine ⟨11602539995438716608139949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7735026663625811072093299 11602539995438716608139949)
      ·
        refine ⟨4350952498289518728052481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11602539995438716608139949 4350952498289518728052481)
        ·
          refine ⟨3263214373717139046039361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4350952498289518728052481 3263214373717139046039361)
          ·
            refine ⟨2447410780287854284529521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3263214373717139046039361 2447410780287854284529521)
            ·
              refine ⟨1835558085215890713397141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2447410780287854284529521 1835558085215890713397141)
              ·
                refine ⟨86041785244494877190491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1835558085215890713397141 86041785244494877190491)
                ·
                  rfl

theorem cell21_1131069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 6].length) (baseStart_1131069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131069 prefixEnd_1131069 := by exact prefixLift 1131069
  have htrace : WordTrace (prefixWord ++ tailWord_1131069) baseStart_1131069 baseEnd_1131069 := by
    simpa [prefixWord, tailWord_1131069, baseEnd_1131069] using wordTrace_append hprefix tailTrace_1131069
  have hstable : (prefixWord ++ tailWord_1131069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131069).length < 2 ^ (prefixWord ++ tailWord_1131069).sum := by decide
  have hdescent : baseEnd_1131069 < baseStart_1131069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131117 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 3]
def baseStart_1131117 : Nat := 118140960795 + 1131117 * 2 ^ 59
def prefixEnd_1131117 : Nat := 4983230072969 + 3 ^ 40 * 1131117 * 2
def baseEnd_1131117 : Nat := 258136309987447214771375

theorem tailTrace_1131117 : CollatzResearch.WordTrace tailWord_1131117 prefixEnd_1131117 258136309987447214771375 := by
  unfold tailWord_1131117
  simp only [CollatzResearch.WordTrace]
  refine ⟨41255226243163763248911605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27503484162109175499274403 41255226243163763248911605)
  ·
    refine ⟨3867677460296602804585463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41255226243163763248911605 3867677460296602804585463)
    ·
      refine ⟨5801516190444904206878195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867677460296602804585463 5801516190444904206878195)
      ·
        refine ⟨8702274285667356310317293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5801516190444904206878195 8702274285667356310317293)
        ·
          refine ⟨3263352857125258616368985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8702274285667356310317293 3263352857125258616368985)
          ·
            refine ⟨2447514642843943962276739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3263352857125258616368985 2447514642843943962276739)
            ·
              refine ⟨3671271964265915943415109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447514642843943962276739 3671271964265915943415109)
              ·
                refine ⟨688363493299859239390333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3671271964265915943415109 688363493299859239390333)
                ·
                  refine ⟨258136309987447214771375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688363493299859239390333 258136309987447214771375)
                  ·
                    rfl

theorem cell21_1131117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_1131117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131117 prefixEnd_1131117 := by exact prefixLift 1131117
  have htrace : WordTrace (prefixWord ++ tailWord_1131117) baseStart_1131117 baseEnd_1131117 := by
    simpa [prefixWord, tailWord_1131117, baseEnd_1131117] using wordTrace_append hprefix tailTrace_1131117
  have hstable : (prefixWord ++ tailWord_1131117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131117).length < 2 ^ (prefixWord ++ tailWord_1131117).sum := by decide
  have hdescent : baseEnd_1131117 < baseStart_1131117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131334 : List Nat := [6, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_1131334 : Nat := 118140960795 + 1131334 * 2 ^ 59
def prefixEnd_1131334 : Nat := 4983230072969 + 3 ^ 40 * 1131334 * 2
def baseEnd_1131334 : Nat := 258185832343903059654265

theorem tailTrace_1131334 : CollatzResearch.WordTrace tailWord_1131334 prefixEnd_1131334 258185832343903059654265 := by
  unfold tailWord_1131334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289473152605550290923783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27508760588918406206374037 1289473152605550290923783)
  ·
    refine ⟨1934209728908325436385675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289473152605550290923783 1934209728908325436385675)
    ·
      refine ⟨2901314593362488154578513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934209728908325436385675 2901314593362488154578513)
      ·
        refine ⟨2175985945021866115933885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2901314593362488154578513 2175985945021866115933885)
        ·
          refine ⟨815994729383199793475207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2175985945021866115933885 815994729383199793475207)
          ·
            refine ⟨1223992094074799690212811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 815994729383199793475207 1223992094074799690212811)
            ·
              refine ⟨1835988141112199535319217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1223992094074799690212811 1835988141112199535319217)
              ·
                refine ⟨1376991105834149651489413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1835988141112199535319217 1376991105834149651489413)
                ·
                  refine ⟨258185832343903059654265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1376991105834149651489413 258185832343903059654265)
                  ·
                    rfl

theorem cell21_1131334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_1131334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131334 prefixEnd_1131334 := by exact prefixLift 1131334
  have htrace : WordTrace (prefixWord ++ tailWord_1131334) baseStart_1131334 baseEnd_1131334 := by
    simpa [prefixWord, tailWord_1131334, baseEnd_1131334] using wordTrace_append hprefix tailTrace_1131334
  have hstable : (prefixWord ++ tailWord_1131334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131334).length < 2 ^ (prefixWord ++ tailWord_1131334).sum := by decide
  have hdescent : baseEnd_1131334 < baseStart_1131334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131390 : List Nat := [4, 2, 3, 1, 2, 2, 7]
def baseStart_1131390 : Nat := 118140960795 + 1131390 * 2 ^ 59
def prefixEnd_1131390 : Nat := 4983230072969 + 3 ^ 40 * 1131390 * 2
def baseEnd_1131390 : Nat := 28688734700762156302313

theorem tailTrace_1131390 : CollatzResearch.WordTrace tailWord_1131390 prefixEnd_1131390 28688734700762156302313 := by
  unfold tailWord_1131390
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158147921396841359199953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27510122247449820582399749 5158147921396841359199953)
  ·
    refine ⟨3868610941047631019399965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5158147921396841359199953 3868610941047631019399965)
    ·
      refine ⟨1450729102892861632274987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3868610941047631019399965 1450729102892861632274987)
      ·
        refine ⟨2176093654339292448412481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1450729102892861632274987 2176093654339292448412481)
        ·
          refine ⟨1632070240754469336309361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2176093654339292448412481 1632070240754469336309361)
          ·
            refine ⟨1224052680565852002232021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632070240754469336309361 1224052680565852002232021)
            ·
              refine ⟨28688734700762156302313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1224052680565852002232021 28688734700762156302313)
              ·
                rfl

theorem cell21_1131390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 7].length) (baseStart_1131390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131390 prefixEnd_1131390 := by exact prefixLift 1131390
  have htrace : WordTrace (prefixWord ++ tailWord_1131390) baseStart_1131390 baseEnd_1131390 := by
    simpa [prefixWord, tailWord_1131390, baseEnd_1131390] using wordTrace_append hprefix tailTrace_1131390
  have hstable : (prefixWord ++ tailWord_1131390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131390).length < 2 ^ (prefixWord ++ tailWord_1131390).sum := by decide
  have hdescent : baseEnd_1131390 < baseStart_1131390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131401 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_1131401 : Nat := 118140960795 + 1131401 * 2 ^ 59
def prefixEnd_1131401 : Nat := 4983230072969 + 3 ^ 40 * 1131401 * 2
def baseEnd_1131401 : Nat := 258201122656725832037461

theorem tailTrace_1131401 : CollatzResearch.WordTrace tailWord_1131401 prefixEnd_1131401 258201122656725832037461 := by
  unfold tailWord_1131401
  simp only [CollatzResearch.WordTrace]
  refine ⟨41265584574134879752250057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27510389716089919834833371 41265584574134879752250057)
  ·
    refine ⟨30949188430601159814187543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41265584574134879752250057 30949188430601159814187543)
    ·
      refine ⟨46423782645901739721281315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30949188430601159814187543 46423782645901739721281315)
      ·
        refine ⟨69635673968852609581921973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46423782645901739721281315 69635673968852609581921973)
        ·
          refine ⟨6528344434579932148305185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69635673968852609581921973 6528344434579932148305185)
          ·
            refine ⟨4896258325934949111228889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6528344434579932148305185 4896258325934949111228889)
            ·
              refine ⟨3672193744451211833421667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4896258325934949111228889 3672193744451211833421667)
              ·
                refine ⟨5508290616676817750132501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3672193744451211833421667 5508290616676817750132501)
                ·
                  refine ⟨258201122656725832037461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5508290616676817750132501 258201122656725832037461)
                  ·
                    rfl

theorem cell21_1131401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_1131401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131401 prefixEnd_1131401 := by exact prefixLift 1131401
  have htrace : WordTrace (prefixWord ++ tailWord_1131401) baseStart_1131401 baseEnd_1131401 := by
    simpa [prefixWord, tailWord_1131401, baseEnd_1131401] using wordTrace_append hprefix tailTrace_1131401
  have hstable : (prefixWord ++ tailWord_1131401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131401).length < 2 ^ (prefixWord ++ tailWord_1131401).sum := by decide
  have hdescent : baseEnd_1131401 < baseStart_1131401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131536 : List Nat := [2, 1, 1, 1, 1, 1, 1, 3, 10]
def baseStart_1131536 : Nat := 118140960795 + 1131536 * 2 ^ 59
def prefixEnd_1131536 : Nat := 4983230072969 + 3 ^ 40 * 1131536 * 2
def baseEnd_1131536 : Nat := 258231931495995597287185

theorem tailTrace_1131536 : CollatzResearch.WordTrace tailWord_1131536 prefixEnd_1131536 258231931495995597287185 := by
  unfold tailWord_1131536
  simp only [CollatzResearch.WordTrace]
  refine ⟨20635254214322898904207231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27513672285763865205609641 20635254214322898904207231)
  ·
    refine ⟨30952881321484348356310847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20635254214322898904207231 30952881321484348356310847)
    ·
      refine ⟨46429321982226522534466271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30952881321484348356310847 46429321982226522534466271)
      ·
        refine ⟨69643982973339783801699407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46429321982226522534466271 69643982973339783801699407)
        ·
          refine ⟨104465974460009675702549111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69643982973339783801699407 104465974460009675702549111)
          ·
            refine ⟨156698961690014513553823667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104465974460009675702549111 156698961690014513553823667)
            ·
              refine ⟨235048442535021770330735501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156698961690014513553823667 235048442535021770330735501)
              ·
                refine ⟨88143165950633163874025813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235048442535021770330735501 88143165950633163874025813)
                ·
                  refine ⟨258231931495995597287185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 88143165950633163874025813 258231931495995597287185)
                  ·
                    rfl

theorem cell21_1131536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_1131536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131536 prefixEnd_1131536 := by exact prefixLift 1131536
  have htrace : WordTrace (prefixWord ++ tailWord_1131536) baseStart_1131536 baseEnd_1131536 := by
    simpa [prefixWord, tailWord_1131536, baseEnd_1131536] using wordTrace_append hprefix tailTrace_1131536
  have hstable : (prefixWord ++ tailWord_1131536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131536).length < 2 ^ (prefixWord ++ tailWord_1131536).sum := by decide
  have hdescent : baseEnd_1131536 < baseStart_1131536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131553 : List Nat := [1, 2, 3, 2, 3, 1, 1, 2, 6]
def baseStart_1131553 : Nat := 118140960795 + 1131553 * 2 ^ 59
def prefixEnd_1131553 : Nat := 4983230072969 + 3 ^ 40 * 1131553 * 2
def baseEnd_1131553 : Nat := 258235811127607345503817

theorem tailTrace_1131553 : CollatzResearch.WordTrace tailWord_1131553 prefixEnd_1131553 258235811127607345503817 := by
  unfold tailWord_1131553
  simp only [CollatzResearch.WordTrace]
  refine ⟨41271128469584209711783313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27514085646389473141188875 41271128469584209711783313)
  ·
    refine ⟨30953346352188157283837485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41271128469584209711783313 30953346352188157283837485)
    ·
      refine ⟨11607504882070558981439057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30953346352188157283837485 11607504882070558981439057)
      ·
        refine ⟨8705628661552919236079293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11607504882070558981439057 8705628661552919236079293)
        ·
          refine ⟨3264610748082344713529735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8705628661552919236079293 3264610748082344713529735)
          ·
            refine ⟨4896916122123517070294603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3264610748082344713529735 4896916122123517070294603)
            ·
              refine ⟨7345374183185275605441905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4896916122123517070294603 7345374183185275605441905)
              ·
                refine ⟨5509030637388956704081429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7345374183185275605441905 5509030637388956704081429)
                ·
                  refine ⟨258235811127607345503817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5509030637388956704081429 258235811127607345503817)
                  ·
                    rfl

theorem cell21_1131553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_1131553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131553 prefixEnd_1131553 := by exact prefixLift 1131553
  have htrace : WordTrace (prefixWord ++ tailWord_1131553) baseStart_1131553 baseEnd_1131553 := by
    simpa [prefixWord, tailWord_1131553, baseEnd_1131553] using wordTrace_append hprefix tailTrace_1131553
  have hstable : (prefixWord ++ tailWord_1131553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131553).length < 2 ^ (prefixWord ++ tailWord_1131553).sum := by decide
  have hdescent : baseEnd_1131553 < baseStart_1131553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131598 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1131598 : Nat := 118140960795 + 1131598 * 2 ^ 59
def prefixEnd_1131598 : Nat := 4983230072969 + 3 ^ 40 * 1131598 * 2
def baseEnd_1131598 : Nat := 258246080740697267253725

theorem tailTrace_1131598 : CollatzResearch.WordTrace tailWord_1131598 prefixEnd_1131598 258246080740697267253725 := by
  unfold tailWord_1131598
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159096219302647799646431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27515179836280788264780965 5159096219302647799646431)
  ·
    refine ⟨7738644328953971699469647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5159096219302647799646431 7738644328953971699469647)
    ·
      refine ⟨11607966493430957549204471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7738644328953971699469647 11607966493430957549204471)
      ·
        refine ⟨17411949740146436323806707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11607966493430957549204471 17411949740146436323806707)
        ·
          refine ⟨26117924610219654485710061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17411949740146436323806707 26117924610219654485710061)
          ·
            refine ⟨9794221728832370432141273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26117924610219654485710061 9794221728832370432141273)
            ·
              refine ⟨7345666296624277824105955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9794221728832370432141273 7345666296624277824105955)
              ·
                refine ⟨11018499444936416736158933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7345666296624277824105955 11018499444936416736158933)
                ·
                  refine ⟨258246080740697267253725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11018499444936416736158933 258246080740697267253725)
                  ·
                    rfl

theorem cell21_1131598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1131598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131598 prefixEnd_1131598 := by exact prefixLift 1131598
  have htrace : WordTrace (prefixWord ++ tailWord_1131598) baseStart_1131598 baseEnd_1131598 := by
    simpa [prefixWord, tailWord_1131598, baseEnd_1131598] using wordTrace_append hprefix tailTrace_1131598
  have hstable : (prefixWord ++ tailWord_1131598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131598).length < 2 ^ (prefixWord ++ tailWord_1131598).sum := by decide
  have hdescent : baseEnd_1131598 < baseStart_1131598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131615 : List Nat := [1, 1, 2, 3, 1, 1, 4, 5, 3]
def baseStart_1131615 : Nat := 118140960795 + 1131615 * 2 ^ 59
def prefixEnd_1131615 : Nat := 4983230072969 + 3 ^ 40 * 1131615 * 2
def baseEnd_1131615 : Nat := 258249960372309015470357

theorem tailTrace_1131615 : CollatzResearch.WordTrace tailWord_1131615 prefixEnd_1131615 258249960372309015470357 := by
  unfold tailWord_1131615
  simp only [CollatzResearch.WordTrace]
  refine ⟨41273389795359594300540299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27515593196906396200360199 41273389795359594300540299)
  ·
    refine ⟨61910084693039391450810449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41273389795359594300540299 61910084693039391450810449)
    ·
      refine ⟨46432563519779543588107837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61910084693039391450810449 46432563519779543588107837)
      ·
        refine ⟨17412211319917328845540439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46432563519779543588107837 17412211319917328845540439)
        ·
          refine ⟨26118316979875993268310659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17412211319917328845540439 26118316979875993268310659)
          ·
            refine ⟨39177475469813989902465989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26118316979875993268310659 39177475469813989902465989)
            ·
              refine ⟨7345776650590123106712373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39177475469813989902465989 7345776650590123106712373)
              ·
                refine ⟨688666560992824041254285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7345776650590123106712373 688666560992824041254285)
                ·
                  refine ⟨258249960372309015470357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688666560992824041254285 258249960372309015470357)
                  ·
                    rfl

theorem cell21_1131615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 5, 3].length) (baseStart_1131615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131615 prefixEnd_1131615 := by exact prefixLift 1131615
  have htrace : WordTrace (prefixWord ++ tailWord_1131615) baseStart_1131615 baseEnd_1131615 := by
    simpa [prefixWord, tailWord_1131615, baseEnd_1131615] using wordTrace_append hprefix tailTrace_1131615
  have hstable : (prefixWord ++ tailWord_1131615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131615).length < 2 ^ (prefixWord ++ tailWord_1131615).sum := by decide
  have hdescent : baseEnd_1131615 < baseStart_1131615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131736 : List Nat := [2, 1, 2, 2, 5, 2, 7]
def baseStart_1131736 : Nat := 118140960795 + 1131736 * 2 ^ 59
def prefixEnd_1131736 : Nat := 4983230072969 + 3 ^ 40 * 1131736 * 2
def baseEnd_1131736 : Nat := 28697508246759965994827

theorem tailTrace_1131736 : CollatzResearch.WordTrace tailWord_1131736 prefixEnd_1131736 28697508246759965994827 := by
  unfold tailWord_1131736
  simp only [CollatzResearch.WordTrace]
  refine ⟨20638901513960615982847531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27518535351947487977130041 20638901513960615982847531)
  ·
    refine ⟨30958352270940923974271297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20638901513960615982847531 30958352270940923974271297)
    ·
      refine ⟨23218764203205692980703473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30958352270940923974271297 23218764203205692980703473)
      ·
        refine ⟨17414073152404269735527605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23218764203205692980703473 17414073152404269735527605)
        ·
          refine ⟨1632569358037900287705713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17414073152404269735527605 1632569358037900287705713)
          ·
            refine ⟨1224427018528425215779285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1632569358037900287705713 1224427018528425215779285)
            ·
              refine ⟨28697508246759965994827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1224427018528425215779285 28697508246759965994827)
              ·
                rfl

theorem cell21_1131736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 7].length) (baseStart_1131736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131736 prefixEnd_1131736 := by exact prefixLift 1131736
  have htrace : WordTrace (prefixWord ++ tailWord_1131736) baseStart_1131736 baseEnd_1131736 := by
    simpa [prefixWord, tailWord_1131736, baseEnd_1131736] using wordTrace_append hprefix tailTrace_1131736
  have hstable : (prefixWord ++ tailWord_1131736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131736).length < 2 ^ (prefixWord ++ tailWord_1131736).sum := by decide
  have hdescent : baseEnd_1131736 < baseStart_1131736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131826 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 7]
def baseStart_1131826 : Nat := 118140960795 + 1131826 * 2 ^ 59
def prefixEnd_1131826 : Nat := 4983230072969 + 3 ^ 40 * 1131826 * 2
def baseEnd_1131826 : Nat := 258298113447019537453259

theorem tailTrace_1131826 : CollatzResearch.WordTrace tailWord_1131826 prefixEnd_1131826 258298113447019537453259 := by
  unfold tailWord_1131826
  simp only [CollatzResearch.WordTrace]
  refine ⟨10320271399398794334117833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27520723731730118224314221 10320271399398794334117833)
  ·
    refine ⟨7740203549549095750588375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10320271399398794334117833 7740203549549095750588375)
    ·
      refine ⟨11610305324323643625882563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7740203549549095750588375 11610305324323643625882563)
      ·
        refine ⟨17415457986485465438823845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11610305324323643625882563 17415457986485465438823845)
        ·
          refine ⟨3265398372466024769779471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17415457986485465438823845 3265398372466024769779471)
          ·
            refine ⟨4898097558699037154669207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3265398372466024769779471 4898097558699037154669207)
            ·
              refine ⟨7347146338048555732003811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4898097558699037154669207 7347146338048555732003811)
              ·
                refine ⟨11020719507072833598005717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7347146338048555732003811 11020719507072833598005717)
                ·
                  refine ⟨258298113447019537453259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11020719507072833598005717 258298113447019537453259)
                  ·
                    rfl

theorem cell21_1131826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_1131826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131826 prefixEnd_1131826 := by exact prefixLift 1131826
  have htrace : WordTrace (prefixWord ++ tailWord_1131826) baseStart_1131826 baseEnd_1131826 := by
    simpa [prefixWord, tailWord_1131826, baseEnd_1131826] using wordTrace_append hprefix tailTrace_1131826
  have hstable : (prefixWord ++ tailWord_1131826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131826).length < 2 ^ (prefixWord ++ tailWord_1131826).sum := by decide
  have hdescent : baseEnd_1131826 < baseStart_1131826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131840 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 6]
def baseStart_1131840 : Nat := 118140960795 + 1131840 * 2 ^ 59
def prefixEnd_1131840 : Nat := 4983230072969 + 3 ^ 40 * 1131840 * 2
def baseEnd_1131840 : Nat := 258301308437758624219897

theorem tailTrace_1131840 : CollatzResearch.WordTrace tailWord_1131840 prefixEnd_1131840 258301308437758624219897 := by
  unfold tailWord_1131840
  simp only [CollatzResearch.WordTrace]
  refine ⟨20640798109772228863740487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27521064146362971818320649 20640798109772228863740487)
  ·
    refine ⟨30961197164658343295610731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20640798109772228863740487 30961197164658343295610731)
    ·
      refine ⟨46441795746987514943416097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30961197164658343295610731 46441795746987514943416097)
      ·
        refine ⟨34831346810240636207562073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46441795746987514943416097 34831346810240636207562073)
        ·
          refine ⟨26123510107680477155671555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34831346810240636207562073 26123510107680477155671555)
          ·
            refine ⟨39185265161520715733507333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26123510107680477155671555 39185265161520715733507333)
            ·
              refine ⟨7347237217785134200032625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39185265161520715733507333 7347237217785134200032625)
              ·
                refine ⟨5510427913338850650024469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7347237217785134200032625 5510427913338850650024469)
                ·
                  refine ⟨258301308437758624219897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5510427913338850650024469 258301308437758624219897)
                  ·
                    rfl

theorem cell21_1131840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_1131840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131840 prefixEnd_1131840 := by exact prefixLift 1131840
  have htrace : WordTrace (prefixWord ++ tailWord_1131840) baseStart_1131840 baseEnd_1131840 := by
    simpa [prefixWord, tailWord_1131840, baseEnd_1131840] using wordTrace_append hprefix tailTrace_1131840
  have hstable : (prefixWord ++ tailWord_1131840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131840).length < 2 ^ (prefixWord ++ tailWord_1131840).sum := by decide
  have hdescent : baseEnd_1131840 < baseStart_1131840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131846 : List Nat := [6, 1, 1, 3, 1, 1, 8]
def baseStart_1131846 : Nat := 118140960795 + 1131846 * 2 ^ 59
def prefixEnd_1131846 : Nat := 4983230072969 + 3 ^ 40 * 1131846 * 2
def baseEnd_1131846 : Nat := 28700297524389327457765

theorem tailTrace_1131846 : CollatzResearch.WordTrace tailWord_1131846 prefixEnd_1131846 28700297524389327457765 := by
  unfold tailWord_1131846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1290056720547585023506231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27521210038348480501466261 1290056720547585023506231)
  ·
    refine ⟨1935085080821377535259347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1290056720547585023506231 1935085080821377535259347)
    ·
      refine ⟨2902627621232066302889021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935085080821377535259347 2902627621232066302889021)
      ·
        refine ⟨1088485357962024863583383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2902627621232066302889021 1088485357962024863583383)
        ·
          refine ⟨1632728036943037295375075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088485357962024863583383 1632728036943037295375075)
          ·
            refine ⟨2449092055414555943062613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1632728036943037295375075 2449092055414555943062613)
            ·
              refine ⟨28700297524389327457765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2449092055414555943062613 28700297524389327457765)
              ·
                rfl

theorem cell21_1131846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 8].length) (baseStart_1131846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131846 prefixEnd_1131846 := by exact prefixLift 1131846
  have htrace : WordTrace (prefixWord ++ tailWord_1131846) baseStart_1131846 baseEnd_1131846 := by
    simpa [prefixWord, tailWord_1131846, baseEnd_1131846] using wordTrace_append hprefix tailTrace_1131846
  have hstable : (prefixWord ++ tailWord_1131846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131846).length < 2 ^ (prefixWord ++ tailWord_1131846).sum := by decide
  have hdescent : baseEnd_1131846 < baseStart_1131846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131905 : List Nat := [1, 2, 4, 3, 3, 1, 7]
def baseStart_1131905 : Nat := 118140960795 + 1131905 * 2 ^ 59
def prefixEnd_1131905 : Nat := 4983230072969 + 3 ^ 40 * 1131905 * 2
def baseEnd_1131905 : Nat := 28701793591481439515159

theorem tailTrace_1131905 : CollatzResearch.WordTrace tailWord_1131905 prefixEnd_1131905 28701793591481439515159 := by
  unfold tailWord_1131905
  simp only [CollatzResearch.WordTrace]
  refine ⟨41283966964308973828597169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27522644642872649219064779 41283966964308973828597169)
  ·
    refine ⟨30962975223231730371447877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41283966964308973828597169 30962975223231730371447877)
    ·
      refine ⟨5805557854355949444646477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30962975223231730371447877 5805557854355949444646477)
      ·
        refine ⟨2177084195383481041742429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5805557854355949444646477 2177084195383481041742429)
        ·
          refine ⟨816406573268805390653411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2177084195383481041742429 816406573268805390653411)
          ·
            refine ⟨1224609859903208085980117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816406573268805390653411 1224609859903208085980117)
            ·
              refine ⟨28701793591481439515159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1224609859903208085980117 28701793591481439515159)
              ·
                rfl

theorem cell21_1131905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 7].length) (baseStart_1131905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131905 prefixEnd_1131905 := by exact prefixLift 1131905
  have htrace : WordTrace (prefixWord ++ tailWord_1131905) baseStart_1131905 baseEnd_1131905 := by
    simpa [prefixWord, tailWord_1131905, baseEnd_1131905] using wordTrace_append hprefix tailTrace_1131905
  have hstable : (prefixWord ++ tailWord_1131905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131905).length < 2 ^ (prefixWord ++ tailWord_1131905).sum := by decide
  have hdescent : baseEnd_1131905 < baseStart_1131905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131916 : List Nat := [2, 2, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1131916 : Nat := 118140960795 + 1131916 * 2 ^ 59
def prefixEnd_1131916 : Nat := 4983230072969 + 3 ^ 40 * 1131916 * 2
def baseEnd_1131916 : Nat := 258318652673199380953075

theorem tailTrace_1131916 : CollatzResearch.WordTrace tailWord_1131916 prefixEnd_1131916 258318652673199380953075 := by
  unfold tailWord_1131916
  simp only [CollatzResearch.WordTrace]
  refine ⟨20642184083634561353623801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27522912111512748471498401 20642184083634561353623801)
  ·
    refine ⟨15481638062725921015217851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20642184083634561353623801 15481638062725921015217851)
    ·
      refine ⟨23222457094088881522826777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15481638062725921015217851 23222457094088881522826777)
      ·
        refine ⟨17416842820566661142120083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23222457094088881522826777 17416842820566661142120083)
        ·
          refine ⟨26125264230849991713180125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17416842820566661142120083 26125264230849991713180125)
          ·
            refine ⟨9796974086568746892442547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26125264230849991713180125 9796974086568746892442547)
            ·
              refine ⟨14695461129853120338663821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9796974086568746892442547 14695461129853120338663821)
              ·
                refine ⟨5510797923694920126998933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14695461129853120338663821 5510797923694920126998933)
                ·
                  refine ⟨258318652673199380953075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5510797923694920126998933 258318652673199380953075)
                  ·
                    rfl

theorem cell21_1131916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1131916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131916 prefixEnd_1131916 := by exact prefixLift 1131916
  have htrace : WordTrace (prefixWord ++ tailWord_1131916) baseStart_1131916 baseEnd_1131916 := by
    simpa [prefixWord, tailWord_1131916, baseEnd_1131916] using wordTrace_append hprefix tailTrace_1131916
  have hstable : (prefixWord ++ tailWord_1131916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131916).length < 2 ^ (prefixWord ++ tailWord_1131916).sum := by decide
  have hdescent : baseEnd_1131916 < baseStart_1131916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1131964 : List Nat := [2, 2, 2, 4, 3, 8]
def baseStart_1131964 : Nat := 118140960795 + 1131964 * 2 ^ 59
def prefixEnd_1131964 : Nat := 4983230072969 + 3 ^ 40 * 1131964 * 2
def baseEnd_1131964 : Nat := 9567763219524517190851

theorem tailTrace_1131964 : CollatzResearch.WordTrace tailWord_1131964 prefixEnd_1131964 9567763219524517190851 := by
  unfold tailWord_1131964
  simp only [CollatzResearch.WordTrace]
  refine ⟨20643059435547613452497473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27524079247396817936663297 20643059435547613452497473)
  ·
    refine ⟨15482294576660710089373105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20643059435547613452497473 15482294576660710089373105)
    ·
      refine ⟨11611720932495532567029829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15482294576660710089373105 11611720932495532567029829)
      ·
        refine ⟨2177197674842912356318093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11611720932495532567029829 2177197674842912356318093)
        ·
          refine ⟨816449128066092133619285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2177197674842912356318093 816449128066092133619285)
          ·
            refine ⟨9567763219524517190851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 816449128066092133619285 9567763219524517190851)
            ·
              rfl

theorem cell21_1131964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 8].length) (baseStart_1131964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1131964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1131964 prefixEnd_1131964 := by exact prefixLift 1131964
  have htrace : WordTrace (prefixWord ++ tailWord_1131964) baseStart_1131964 baseEnd_1131964 := by
    simpa [prefixWord, tailWord_1131964, baseEnd_1131964] using wordTrace_append hprefix tailTrace_1131964
  have hstable : (prefixWord ++ tailWord_1131964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1131964).length < 2 ^ (prefixWord ++ tailWord_1131964).sum := by decide
  have hdescent : baseEnd_1131964 < baseStart_1131964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1131964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132088 : List Nat := [2, 1, 2, 1, 4, 3, 3, 2, 3]
def baseStart_1132088 : Nat := 118140960795 + 1132088 * 2 ^ 59
def prefixEnd_1132088 : Nat := 4983230072969 + 3 ^ 40 * 1132088 * 2
def baseEnd_1132088 : Nat := 258357905416565304086057

theorem tailTrace_1132088 : CollatzResearch.WordTrace tailWord_1132088 prefixEnd_1132088 258357905416565304086057 := by
  unfold tailWord_1132088
  simp only [CollatzResearch.WordTrace]
  refine ⟨20645320761322998041254459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27527094348430664055005945 20645320761322998041254459)
  ·
    refine ⟨30967981141984497061881689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20645320761322998041254459 30967981141984497061881689)
    ·
      refine ⟨23225985856488372796411267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30967981141984497061881689 23225985856488372796411267)
      ·
        refine ⟨34838978784732559194616901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23225985856488372796411267 34838978784732559194616901)
        ·
          refine ⟨6532308522137354848990669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34838978784732559194616901 6532308522137354848990669)
          ·
            refine ⟨2449615695801508068371501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6532308522137354848990669 2449615695801508068371501)
            ·
              refine ⟨918605885925565525639313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2449615695801508068371501 918605885925565525639313)
              ·
                refine ⟨688954414444174144229485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918605885925565525639313 688954414444174144229485)
                ·
                  refine ⟨258357905416565304086057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688954414444174144229485 258357905416565304086057)
                  ·
                    rfl

theorem cell21_1132088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 2, 3].length) (baseStart_1132088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132088 prefixEnd_1132088 := by exact prefixLift 1132088
  have htrace : WordTrace (prefixWord ++ tailWord_1132088) baseStart_1132088 baseEnd_1132088 := by
    simpa [prefixWord, tailWord_1132088, baseEnd_1132088] using wordTrace_append hprefix tailTrace_1132088
  have hstable : (prefixWord ++ tailWord_1132088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132088).length < 2 ^ (prefixWord ++ tailWord_1132088).sum := by decide
  have hdescent : baseEnd_1132088 < baseStart_1132088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132113 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 7]
def baseStart_1132113 : Nat := 118140960795 + 1132113 * 2 ^ 59
def prefixEnd_1132113 : Nat := 4983230072969 + 3 ^ 40 * 1132113 * 2
def baseEnd_1132113 : Nat := 258363610757170816169339

theorem tailTrace_1132113 : CollatzResearch.WordTrace tailWord_1132113 prefixEnd_1132113 258363610757170816169339 := by
  unfold tailWord_1132113
  simp only [CollatzResearch.WordTrace]
  refine ⟨41291553347555425352168993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27527702231703616901445995 41291553347555425352168993)
  ·
    refine ⟨30968665010666569014126745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41291553347555425352168993 30968665010666569014126745)
    ·
      refine ⟨23226498757999926760595059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30968665010666569014126745 23226498757999926760595059)
      ·
        refine ⟨34839748136999890140892589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23226498757999926760595059 34839748136999890140892589)
        ·
          refine ⟨13064905551374958802834721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34839748136999890140892589 13064905551374958802834721)
          ·
            refine ⟨9798679163531219102126041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13064905551374958802834721 9798679163531219102126041)
            ·
              refine ⟨7349009372648414326594531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9798679163531219102126041 7349009372648414326594531)
              ·
                refine ⟨11023514058972621489891797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7349009372648414326594531 11023514058972621489891797)
                ·
                  refine ⟨258363610757170816169339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11023514058972621489891797 258363610757170816169339)
                  ·
                    rfl

theorem cell21_1132113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 7].length) (baseStart_1132113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132113 prefixEnd_1132113 := by exact prefixLift 1132113
  have htrace : WordTrace (prefixWord ++ tailWord_1132113) baseStart_1132113 baseEnd_1132113 := by
    simpa [prefixWord, tailWord_1132113, baseEnd_1132113] using wordTrace_append hprefix tailTrace_1132113
  have hstable : (prefixWord ++ tailWord_1132113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132113).length < 2 ^ (prefixWord ++ tailWord_1132113).sum := by decide
  have hdescent : baseEnd_1132113 < baseStart_1132113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132161 : List Nat := [1, 2, 4, 2, 1, 2, 2, 3, 4]
def baseStart_1132161 : Nat := 118140960795 + 1132161 * 2 ^ 59
def prefixEnd_1132161 : Nat := 4983230072969 + 3 ^ 40 * 1132161 * 2
def baseEnd_1132161 : Nat := 258374565011133399369241

theorem tailTrace_1132161 : CollatzResearch.WordTrace tailWord_1132161 prefixEnd_1132161 258374565011133399369241 := by
  unfold tailWord_1132161
  simp only [CollatzResearch.WordTrace]
  refine ⟨41293304051381529549916337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27528869367587686366610891 41293304051381529549916337)
  ·
    refine ⟨30969978038536147162437253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41293304051381529549916337 30969978038536147162437253)
    ·
      refine ⟨5806870882225527592956985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30969978038536147162437253 5806870882225527592956985)
      ·
        refine ⟨4355153161669145694717739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5806870882225527592956985 4355153161669145694717739)
        ·
          refine ⟨6532729742503718542076609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355153161669145694717739 6532729742503718542076609)
          ·
            refine ⟨4899547306877788906557457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6532729742503718542076609 4899547306877788906557457)
            ·
              refine ⟨3674660480158341679918093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4899547306877788906557457 3674660480158341679918093)
              ·
                refine ⟨1377997680059378129969285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3674660480158341679918093 1377997680059378129969285)
                ·
                  refine ⟨258374565011133399369241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1377997680059378129969285 258374565011133399369241)
                  ·
                    rfl

theorem cell21_1132161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 3, 4].length) (baseStart_1132161 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132161 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132161 prefixEnd_1132161 := by exact prefixLift 1132161
  have htrace : WordTrace (prefixWord ++ tailWord_1132161) baseStart_1132161 baseEnd_1132161 := by
    simpa [prefixWord, tailWord_1132161, baseEnd_1132161] using wordTrace_append hprefix tailTrace_1132161
  have hstable : (prefixWord ++ tailWord_1132161).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132161).length < 2 ^ (prefixWord ++ tailWord_1132161).sum := by decide
  have hdescent : baseEnd_1132161 < baseStart_1132161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132189 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 9]
def baseStart_1132189 : Nat := 118140960795 + 1132189 * 2 ^ 59
def prefixEnd_1132189 : Nat := 4983230072969 + 3 ^ 40 * 1132189 * 2
def baseEnd_1132189 : Nat := 258380954992611572902517

theorem tailTrace_1132189 : CollatzResearch.WordTrace tailWord_1132189 prefixEnd_1132189 258380954992611572902517 := by
  unfold tailWord_1132189
  simp only [CollatzResearch.WordTrace]
  refine ⟨41294325295280090331935621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27529550196853393554623747 41294325295280090331935621)
  ·
    refine ⟨7742685992865016937237929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41294325295280090331935621 7742685992865016937237929)
    ·
      refine ⟨5807014494648762702928447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7742685992865016937237929 5807014494648762702928447)
      ·
        refine ⟨8710521741973144054392671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5807014494648762702928447 8710521741973144054392671)
        ·
          refine ⟨13065782612959716081589007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8710521741973144054392671 13065782612959716081589007)
          ·
            refine ⟨19598673919439574122383511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13065782612959716081589007 19598673919439574122383511)
            ·
              refine ⟨29398010879159361183575267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19598673919439574122383511 29398010879159361183575267)
              ·
                refine ⟨44097016318739041775362901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29398010879159361183575267 44097016318739041775362901)
                ·
                  refine ⟨258380954992611572902517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44097016318739041775362901 258380954992611572902517)
                  ·
                    rfl

theorem cell21_1132189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_1132189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132189 prefixEnd_1132189 := by exact prefixLift 1132189
  have htrace : WordTrace (prefixWord ++ tailWord_1132189) baseStart_1132189 baseEnd_1132189 := by
    simpa [prefixWord, tailWord_1132189, baseEnd_1132189] using wordTrace_append hprefix tailTrace_1132189
  have hstable : (prefixWord ++ tailWord_1132189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132189).length < 2 ^ (prefixWord ++ tailWord_1132189).sum := by decide
  have hdescent : baseEnd_1132189 < baseStart_1132189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132226 : List Nat := [3, 5, 1, 2, 1, 1, 1, 7]
def baseStart_1132226 : Nat := 118140960795 + 1132226 * 2 ^ 59
def prefixEnd_1132226 : Nat := 4983230072969 + 3 ^ 40 * 1132226 * 2
def baseEnd_1132226 : Nat := 86129799632235910261925

theorem tailTrace_1132226 : CollatzResearch.WordTrace tailWord_1132226 prefixEnd_1132226 86129799632235910261925 := by
  unfold tailWord_1132226
  simp only [CollatzResearch.WordTrace]
  refine ⟨10323918699036511412758133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27530449864097363767355021 10323918699036511412758133)
  ·
    refine ⟨967867378034672944946075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10323918699036511412758133 967867378034672944946075)
    ·
      refine ⟨1451801067052009417419113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967867378034672944946075 1451801067052009417419113)
      ·
        refine ⟨1088850800289007063064335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451801067052009417419113 1088850800289007063064335)
        ·
          refine ⟨1633276200433510594596503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1088850800289007063064335 1633276200433510594596503)
          ·
            refine ⟨2449914300650265891894755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633276200433510594596503 2449914300650265891894755)
            ·
              refine ⟨3674871450975398837842133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449914300650265891894755 3674871450975398837842133)
              ·
                refine ⟨86129799632235910261925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3674871450975398837842133 86129799632235910261925)
                ·
                  rfl

theorem cell21_1132226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_1132226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132226 prefixEnd_1132226 := by exact prefixLift 1132226
  have htrace : WordTrace (prefixWord ++ tailWord_1132226) baseStart_1132226 baseEnd_1132226 := by
    simpa [prefixWord, tailWord_1132226, baseEnd_1132226] using wordTrace_append hprefix tailTrace_1132226
  have hstable : (prefixWord ++ tailWord_1132226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132226).length < 2 ^ (prefixWord ++ tailWord_1132226).sum := by decide
  have hdescent : baseEnd_1132226 < baseStart_1132226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132308 : List Nat := [2, 4, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1132308 : Nat := 118140960795 + 1132308 * 2 ^ 59
def prefixEnd_1132308 : Nat := 4983230072969 + 3 ^ 40 * 1132308 * 2
def baseEnd_1132308 : Nat := 258408112413893810418941

theorem tailTrace_1132308 : CollatzResearch.WordTrace tailWord_1132308 prefixEnd_1132308 258408112413893810418941 := by
  unfold tailWord_1132308
  simp only [CollatzResearch.WordTrace]
  refine ⟨20649332790924486827758789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27532443721232649103678385 20649332790924486827758789)
  ·
    refine ⟨3871749898298341280204773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20649332790924486827758789 3871749898298341280204773)
    ·
      refine ⟨725953105930938990038395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3871749898298341280204773 725953105930938990038395)
      ·
        refine ⟨1088929658896408485057593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 725953105930938990038395 1088929658896408485057593)
        ·
          refine ⟨816697244172306363793195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1088929658896408485057593 816697244172306363793195)
          ·
            refine ⟨1225045866258459545689793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816697244172306363793195 1225045866258459545689793)
            ·
              refine ⟨918784399693844659267345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225045866258459545689793 918784399693844659267345)
              ·
                refine ⟨689088299770383494450509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918784399693844659267345 689088299770383494450509)
                ·
                  refine ⟨258408112413893810418941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689088299770383494450509 258408112413893810418941)
                  ·
                    rfl

theorem cell21_1132308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1132308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132308 prefixEnd_1132308 := by exact prefixLift 1132308
  have htrace : WordTrace (prefixWord ++ tailWord_1132308) baseStart_1132308 baseEnd_1132308 := by
    simpa [prefixWord, tailWord_1132308, baseEnd_1132308] using wordTrace_append hprefix tailTrace_1132308
  have hstable : (prefixWord ++ tailWord_1132308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132308).length < 2 ^ (prefixWord ++ tailWord_1132308).sum := by decide
  have hdescent : baseEnd_1132308 < baseStart_1132308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132440 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 4]
def baseStart_1132440 : Nat := 118140960795 + 1132440 * 2 ^ 59
def prefixEnd_1132440 : Nat := 4983230072969 + 3 ^ 40 * 1132440 * 2
def baseEnd_1132440 : Nat := 258438236612290914218671

theorem tailTrace_1132440 : CollatzResearch.WordTrace tailWord_1132440 prefixEnd_1132440 258438236612290914218671 := by
  unfold tailWord_1132440
  simp only [CollatzResearch.WordTrace]
  refine ⟨20651740008685380099661387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27535653344913840132881849 20651740008685380099661387)
  ·
    refine ⟨30977610013028070149492081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20651740008685380099661387 30977610013028070149492081)
    ·
      refine ⟨23233207509771052612119061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30977610013028070149492081 23233207509771052612119061)
      ·
        refine ⟨1089056602020518091193081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 23233207509771052612119061 1089056602020518091193081)
        ·
          refine ⟨816792451515388568394811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1089056602020518091193081 816792451515388568394811)
          ·
            refine ⟨1225188677273082852592217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 816792451515388568394811 1225188677273082852592217)
            ·
              refine ⟨918891507954812139444163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225188677273082852592217 918891507954812139444163)
              ·
                refine ⟨1378337261932218209166245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 918891507954812139444163 1378337261932218209166245)
                ·
                  refine ⟨258438236612290914218671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378337261932218209166245 258438236612290914218671)
                  ·
                    rfl

theorem cell21_1132440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 4].length) (baseStart_1132440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132440 prefixEnd_1132440 := by exact prefixLift 1132440
  have htrace : WordTrace (prefixWord ++ tailWord_1132440) baseStart_1132440 baseEnd_1132440 := by
    simpa [prefixWord, tailWord_1132440, baseEnd_1132440] using wordTrace_append hprefix tailTrace_1132440
  have hstable : (prefixWord ++ tailWord_1132440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132440).length < 2 ^ (prefixWord ++ tailWord_1132440).sum := by decide
  have hdescent : baseEnd_1132440 < baseStart_1132440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132572 : List Nat := [2, 2, 3, 1, 3, 3, 2, 5]
def baseStart_1132572 : Nat := 118140960795 + 1132572 * 2 ^ 59
def prefixEnd_1132572 : Nat := 4983230072969 + 3 ^ 40 * 1132572 * 2
def baseEnd_1132572 : Nat := 86156120270229339339467

theorem tailTrace_1132572 : CollatzResearch.WordTrace tailWord_1132572 prefixEnd_1132572 86156120270229339339467 := by
  unfold tailWord_1132572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20654147226446273371563985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27538862968595031162085313 20654147226446273371563985)
  ·
    refine ⟨15490610419834705028672989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20654147226446273371563985 15490610419834705028672989)
    ·
      refine ⟨5808978907438014385752371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15490610419834705028672989 5808978907438014385752371)
      ·
        refine ⟨8713468361157021578628557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808978907438014385752371 8713468361157021578628557)
        ·
          refine ⟨3267550635433883091985709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8713468361157021578628557 3267550635433883091985709)
          ·
            refine ⟨1225331488287706159494641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3267550635433883091985709 1225331488287706159494641)
            ·
              refine ⟨918998616215779619620981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225331488287706159494641 918998616215779619620981)
              ·
                refine ⟨86156120270229339339467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 918998616215779619620981 86156120270229339339467)
                ·
                  rfl

theorem cell21_1132572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_1132572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132572 prefixEnd_1132572 := by exact prefixLift 1132572
  have htrace : WordTrace (prefixWord ++ tailWord_1132572) baseStart_1132572 baseEnd_1132572 := by
    simpa [prefixWord, tailWord_1132572, baseEnd_1132572] using wordTrace_append hprefix tailTrace_1132572
  have hstable : (prefixWord ++ tailWord_1132572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132572).length < 2 ^ (prefixWord ++ tailWord_1132572).sum := by decide
  have hdescent : baseEnd_1132572 < baseStart_1132572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132676 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1132676 : Nat := 118140960795 + 1132676 * 2 ^ 59
def prefixEnd_1132676 : Nat := 4983230072969 + 3 ^ 40 * 1132676 * 2
def baseEnd_1132676 : Nat := 258492095027606948284855

theorem tailTrace_1132676 : CollatzResearch.WordTrace tailWord_1132676 prefixEnd_1132676 258492095027606948284855 := by
  unfold tailWord_1132676
  simp only [CollatzResearch.WordTrace]
  refine ⟨20656043822257886252456941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27541391763010515003275921 20656043822257886252456941)
  ·
    refine ⟨7746016433346707344671353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20656043822257886252456941 7746016433346707344671353)
    ·
      refine ⟨5809512325010030508503515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7746016433346707344671353 5809512325010030508503515)
      ·
        refine ⟨8714268487515045762755273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809512325010030508503515 8714268487515045762755273)
        ·
          refine ⟨6535701365636284322066455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8714268487515045762755273 6535701365636284322066455)
          ·
            refine ⟨9803552048454426483099683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535701365636284322066455 9803552048454426483099683)
            ·
              refine ⟨14705328072681639724649525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9803552048454426483099683 14705328072681639724649525)
              ·
                refine ⟨1378624506813903724185893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14705328072681639724649525 1378624506813903724185893)
                ·
                  refine ⟨258492095027606948284855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378624506813903724185893 258492095027606948284855)
                  ·
                    rfl

theorem cell21_1132676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1132676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132676 prefixEnd_1132676 := by exact prefixLift 1132676
  have htrace : WordTrace (prefixWord ++ tailWord_1132676) baseStart_1132676 baseEnd_1132676 := by
    simpa [prefixWord, tailWord_1132676, baseEnd_1132676] using wordTrace_append hprefix tailTrace_1132676
  have hstable : (prefixWord ++ tailWord_1132676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132676).length < 2 ^ (prefixWord ++ tailWord_1132676).sum := by decide
  have hdescent : baseEnd_1132676 < baseStart_1132676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132786 : List Nat := [3, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_1132786 : Nat := 118140960795 + 1132786 * 2 ^ 59
def prefixEnd_1132786 : Nat := 4983230072969 + 3 ^ 40 * 1132786 * 2
def baseEnd_1132786 : Nat := 258517198526271201451297

theorem tailTrace_1132786 : CollatzResearch.WordTrace tailWord_1132786 prefixEnd_1132786 258517198526271201451297 := by
  unfold tailWord_1132786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10329024918529315322854553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27544066449411507527612141 10329024918529315322854553)
  ·
    refine ⟨7746768688896986492140915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10329024918529315322854553 7746768688896986492140915)
    ·
      refine ⟨11620153033345479738211373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7746768688896986492140915 11620153033345479738211373)
      ·
        refine ⟨4357557387504554901829265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11620153033345479738211373 4357557387504554901829265)
        ·
          refine ⟨3268168040628416176371949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4357557387504554901829265 3268168040628416176371949)
          ·
            refine ⟨1225563015235656066139481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3268168040628416176371949 1225563015235656066139481)
            ·
              refine ⟨919172261426742049604611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225563015235656066139481 919172261426742049604611)
              ·
                refine ⟨1378758392140113074406917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919172261426742049604611 1378758392140113074406917)
                ·
                  refine ⟨258517198526271201451297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1378758392140113074406917 258517198526271201451297)
                  ·
                    rfl

theorem cell21_1132786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_1132786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132786 prefixEnd_1132786 := by exact prefixLift 1132786
  have htrace : WordTrace (prefixWord ++ tailWord_1132786) baseStart_1132786 baseEnd_1132786 := by
    simpa [prefixWord, tailWord_1132786, baseEnd_1132786] using wordTrace_append hprefix tailTrace_1132786
  have hstable : (prefixWord ++ tailWord_1132786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132786).length < 2 ^ (prefixWord ++ tailWord_1132786).sum := by decide
  have hdescent : baseEnd_1132786 < baseStart_1132786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132814 : List Nat := [4, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_1132814 : Nat := 118140960795 + 1132814 * 2 ^ 59
def prefixEnd_1132814 : Nat := 4983230072969 + 3 ^ 40 * 1132814 * 2
def baseEnd_1132814 : Nat := 258523588507749374984573

theorem tailTrace_1132814 : CollatzResearch.WordTrace tailWord_1132814 prefixEnd_1132814 258523588507749374984573 := by
  unfold tailWord_1132814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5164640114751977759179687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27544747278677214715624997 5164640114751977759179687)
  ·
    refine ⟨7746960172127966638769531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5164640114751977759179687 7746960172127966638769531)
    ·
      refine ⟨11620440258191949958154297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7746960172127966638769531 11620440258191949958154297)
      ·
        refine ⟨8715330193643962468615723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11620440258191949958154297 8715330193643962468615723)
        ·
          refine ⟨13072995290465943702923585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715330193643962468615723 13072995290465943702923585)
          ·
            refine ⟨9804746467849457777192689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13072995290465943702923585 9804746467849457777192689)
            ·
              refine ⟨7353559850887093332894517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9804746467849457777192689 7353559850887093332894517)
              ·
                refine ⟨689396236020664999958861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7353559850887093332894517 689396236020664999958861)
                ·
                  refine ⟨258523588507749374984573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689396236020664999958861 258523588507749374984573)
                  ·
                    rfl

theorem cell21_1132814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_1132814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132814 prefixEnd_1132814 := by exact prefixLift 1132814
  have htrace : WordTrace (prefixWord ++ tailWord_1132814) baseStart_1132814 baseEnd_1132814 := by
    simpa [prefixWord, tailWord_1132814, baseEnd_1132814] using wordTrace_append hprefix tailTrace_1132814
  have hstable : (prefixWord ++ tailWord_1132814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132814).length < 2 ^ (prefixWord ++ tailWord_1132814).sum := by decide
  have hdescent : baseEnd_1132814 < baseStart_1132814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132831 : List Nat := [1, 1, 2, 4, 3, 1, 4, 2, 3]
def baseStart_1132831 : Nat := 118140960795 + 1132831 * 2 ^ 59
def prefixEnd_1132831 : Nat := 4983230072969 + 3 ^ 40 * 1132831 * 2
def baseEnd_1132831 : Nat := 258527468139361123201205

theorem tailTrace_1132831 : CollatzResearch.WordTrace tailWord_1132831 prefixEnd_1132831 258527468139361123201205 := by
  unfold tailWord_1132831
  simp only [CollatzResearch.WordTrace]
  refine ⟨41317740958954233976806347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27545160639302822651204231 41317740958954233976806347)
  ·
    refine ⟨61976611438431350965209521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41317740958954233976806347 61976611438431350965209521)
    ·
      refine ⟨46482458578823513223907141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61976611438431350965209521 46482458578823513223907141)
      ·
        refine ⟨8715460983529408729482589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46482458578823513223907141 8715460983529408729482589)
        ·
          refine ⟨3268297868823528273555971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8715460983529408729482589 3268297868823528273555971)
          ·
            refine ⟨4902446803235292410333957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268297868823528273555971 4902446803235292410333957)
            ·
              refine ⟨919208775606617326937617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4902446803235292410333957 919208775606617326937617)
              ·
                refine ⟨689406581704962995203213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919208775606617326937617 689406581704962995203213)
                ·
                  refine ⟨258527468139361123201205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689406581704962995203213 258527468139361123201205)
                  ·
                    rfl

theorem cell21_1132831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 2, 3].length) (baseStart_1132831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132831 prefixEnd_1132831 := by exact prefixLift 1132831
  have htrace : WordTrace (prefixWord ++ tailWord_1132831) baseStart_1132831 baseEnd_1132831 := by
    simpa [prefixWord, tailWord_1132831, baseEnd_1132831] using wordTrace_append hprefix tailTrace_1132831
  have hstable : (prefixWord ++ tailWord_1132831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132831).length < 2 ^ (prefixWord ++ tailWord_1132831).sum := by decide
  have hdescent : baseEnd_1132831 < baseStart_1132831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132856 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 7]
def baseStart_1132856 : Nat := 118140960795 + 1132856 * 2 ^ 59
def prefixEnd_1132856 : Nat := 4983230072969 + 3 ^ 40 * 1132856 * 2
def baseEnd_1132856 : Nat := 258533173479966635284487

theorem tailTrace_1132856 : CollatzResearch.WordTrace tailWord_1132856 prefixEnd_1132856 258533173479966635284487 := by
  unfold tailWord_1132856
  simp only [CollatzResearch.WordTrace]
  refine ⟨20659326391931831623233211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27545768522575775497644281 20659326391931831623233211)
  ·
    refine ⟨30988989587897747434849817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20659326391931831623233211 30988989587897747434849817)
    ·
      refine ⟨23241742190923310576137363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30988989587897747434849817 23241742190923310576137363)
      ·
        refine ⟨34862613286384965864206045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23241742190923310576137363 34862613286384965864206045)
        ·
          refine ⟨13073479982394362199077267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34862613286384965864206045 13073479982394362199077267)
          ·
            refine ⟨19610219973591543298615901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13073479982394362199077267 19610219973591543298615901)
            ·
              refine ⟨7353832490096828736980963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19610219973591543298615901 7353832490096828736980963)
              ·
                refine ⟨11030748735145243105471445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7353832490096828736980963 11030748735145243105471445)
                ·
                  refine ⟨258533173479966635284487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11030748735145243105471445 258533173479966635284487)
                  ·
                    rfl

theorem cell21_1132856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_1132856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132856 prefixEnd_1132856 := by exact prefixLift 1132856
  have htrace : WordTrace (prefixWord ++ tailWord_1132856) baseStart_1132856 baseEnd_1132856 := by
    simpa [prefixWord, tailWord_1132856, baseEnd_1132856] using wordTrace_append hprefix tailTrace_1132856
  have hstable : (prefixWord ++ tailWord_1132856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132856).length < 2 ^ (prefixWord ++ tailWord_1132856).sum := by decide
  have hdescent : baseEnd_1132856 < baseStart_1132856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1132887 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 6]
def baseStart_1132887 : Nat := 118140960795 + 1132887 * 2 ^ 59
def prefixEnd_1132887 : Nat := 4983230072969 + 3 ^ 40 * 1132887 * 2
def baseEnd_1132887 : Nat := 258540248102317470267757

theorem tailTrace_1132887 : CollatzResearch.WordTrace tailWord_1132887 prefixEnd_1132887 258540248102317470267757 := by
  unfold tailWord_1132887
  simp only [CollatzResearch.WordTrace]
  refine ⟨41319783446751355540844915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27546522297834237027229943 41319783446751355540844915)
  ·
    refine ⟨61979675170127033311267373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41319783446751355540844915 61979675170127033311267373)
    ·
      refine ⟨23242378188797637491725265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61979675170127033311267373 23242378188797637491725265)
      ·
        refine ⟨17431783641598228118793949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23242378188797637491725265 17431783641598228118793949)
        ·
          refine ⟨6536918865599335544547731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17431783641598228118793949 6536918865599335544547731)
          ·
            refine ⟨9805378298399003316821597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6536918865599335544547731 9805378298399003316821597)
            ·
              refine ⟨3677016861899626243808099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9805378298399003316821597 3677016861899626243808099)
              ·
                refine ⟨5515525292849439365712149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677016861899626243808099 5515525292849439365712149)
                ·
                  refine ⟨258540248102317470267757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5515525292849439365712149 258540248102317470267757)
                  ·
                    rfl

theorem cell21_1132887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 6].length) (baseStart_1132887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1132887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1132887 prefixEnd_1132887 := by exact prefixLift 1132887
  have htrace : WordTrace (prefixWord ++ tailWord_1132887) baseStart_1132887 baseEnd_1132887 := by
    simpa [prefixWord, tailWord_1132887, baseEnd_1132887] using wordTrace_append hprefix tailTrace_1132887
  have hstable : (prefixWord ++ tailWord_1132887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1132887).length < 2 ^ (prefixWord ++ tailWord_1132887).sum := by decide
  have hdescent : baseEnd_1132887 < baseStart_1132887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1132887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133053 : List Nat := [1, 4, 1, 1, 1, 3, 10]
def baseStart_1133053 : Nat := 118140960795 + 1133053 * 2 ^ 59
def prefixEnd_1133053 : Nat := 4983230072969 + 3 ^ 40 * 1133053 * 2
def baseEnd_1133053 : Nat := 28730903507104230055639

theorem tailTrace_1133053 : CollatzResearch.WordTrace tailWord_1133053 prefixEnd_1133053 28730903507104230055639 := by
  unfold tailWord_1133053
  simp only [CollatzResearch.WordTrace]
  refine ⟨41325837964149965891387813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27550558642766643927591875 41325837964149965891387813)
  ·
    refine ⟨7748594618278118604635215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41325837964149965891387813 7748594618278118604635215)
    ·
      refine ⟨11622891927417177906952823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748594618278118604635215 11622891927417177906952823)
      ·
        refine ⟨17434337891125766860429235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11622891927417177906952823 17434337891125766860429235)
        ·
          refine ⟨26151506836688650290643853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17434337891125766860429235 26151506836688650290643853)
          ·
            refine ⟨9806815063758243858991445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26151506836688650290643853 9806815063758243858991445)
            ·
              refine ⟨28730903507104230055639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9806815063758243858991445 28730903507104230055639)
              ·
                rfl

theorem cell21_1133053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 10].length) (baseStart_1133053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133053 prefixEnd_1133053 := by exact prefixLift 1133053
  have htrace : WordTrace (prefixWord ++ tailWord_1133053) baseStart_1133053 baseEnd_1133053 := by
    simpa [prefixWord, tailWord_1133053, baseEnd_1133053] using wordTrace_append hprefix tailTrace_1133053
  have hstable : (prefixWord ++ tailWord_1133053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133053).length < 2 ^ (prefixWord ++ tailWord_1133053).sum := by decide
  have hdescent : baseEnd_1133053 < baseStart_1133053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133124 : List Nat := [2, 3, 5, 1, 1, 2, 2, 1, 4]
def baseStart_1133124 : Nat := 118140960795 + 1133124 * 2 ^ 59
def prefixEnd_1133124 : Nat := 4983230072969 + 3 ^ 40 * 1133124 * 2
def baseEnd_1133124 : Nat := 258594334731257724817273

theorem tailTrace_1133124 : CollatzResearch.WordTrace tailWord_1133124 prefixEnd_1133124 258594334731257724817273 := by
  unfold tailWord_1133124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20664213773446372508611213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27552285031261830011481617 20664213773446372508611213)
  ·
    refine ⟨7749080165042389690729205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20664213773446372508611213 7749080165042389690729205)
    ·
      refine ⟨726476265472724033505863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7749080165042389690729205 726476265472724033505863)
      ·
        refine ⟨1089714398209086050258795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726476265472724033505863 1089714398209086050258795)
        ·
          refine ⟨1634571597313629075388193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089714398209086050258795 1634571597313629075388193)
          ·
            refine ⟨1225928697985221806541145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1634571597313629075388193 1225928697985221806541145)
            ·
              refine ⟨919446523488916354905859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225928697985221806541145 919446523488916354905859)
              ·
                refine ⟨1379169785233374532358789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919446523488916354905859 1379169785233374532358789)
                ·
                  refine ⟨258594334731257724817273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379169785233374532358789 258594334731257724817273)
                  ·
                    rfl

theorem cell21_1133124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_1133124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133124 prefixEnd_1133124 := by exact prefixLift 1133124
  have htrace : WordTrace (prefixWord ++ tailWord_1133124) baseStart_1133124 baseEnd_1133124 := by
    simpa [prefixWord, tailWord_1133124, baseEnd_1133124] using wordTrace_append hprefix tailTrace_1133124
  have hstable : (prefixWord ++ tailWord_1133124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133124).length < 2 ^ (prefixWord ++ tailWord_1133124).sum := by decide
  have hdescent : baseEnd_1133124 < baseStart_1133124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133191 : List Nat := [1, 1, 4, 2, 1, 2, 1, 5, 4]
def baseStart_1133191 : Nat := 118140960795 + 1133191 * 2 ^ 59
def prefixEnd_1133191 : Nat := 4983230072969 + 3 ^ 40 * 1133191 * 2
def baseEnd_1133191 : Nat := 258609625044080497200469

theorem tailTrace_1133191 : CollatzResearch.WordTrace tailWord_1133191 prefixEnd_1133191 258609625044080497200469 := by
  unfold tailWord_1133191
  simp only [CollatzResearch.WordTrace]
  refine ⟨41330871237650015459911427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27553914158433343639940951 41330871237650015459911427)
  ·
    refine ⟨61996306856475023189867141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41330871237650015459911427 61996306856475023189867141)
    ·
      refine ⟨11624307535589066848100089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61996306856475023189867141 11624307535589066848100089)
      ·
        refine ⟨8718230651691800136075067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11624307535589066848100089 8718230651691800136075067)
        ·
          refine ⟨13077345977537700204112601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8718230651691800136075067 13077345977537700204112601)
          ·
            refine ⟨9808009483153275153084451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13077345977537700204112601 9808009483153275153084451)
            ·
              refine ⟨14712014224729912729626677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9808009483153275153084451 14712014224729912729626677)
              ·
                refine ⟨1379251333568429318402501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14712014224729912729626677 1379251333568429318402501)
                ·
                  refine ⟨258609625044080497200469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379251333568429318402501 258609625044080497200469)
                  ·
                    rfl

theorem cell21_1133191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 5, 4].length) (baseStart_1133191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133191 prefixEnd_1133191 := by exact prefixLift 1133191
  have htrace : WordTrace (prefixWord ++ tailWord_1133191) baseStart_1133191 baseEnd_1133191 := by
    simpa [prefixWord, tailWord_1133191, baseEnd_1133191] using wordTrace_append hprefix tailTrace_1133191
  have hstable : (prefixWord ++ tailWord_1133191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133191).length < 2 ^ (prefixWord ++ tailWord_1133191).sum := by decide
  have hdescent : baseEnd_1133191 < baseStart_1133191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133281 : List Nat := [1, 2, 3, 1, 4, 1, 9]
def baseStart_1133281 : Nat := 118140960795 + 1133281 * 2 ^ 59
def prefixEnd_1133281 : Nat := 4983230072969 + 3 ^ 40 * 1133281 * 2
def baseEnd_1133281 : Nat := 28736684918917815633365

theorem tailTrace_1133281 : CollatzResearch.WordTrace tailWord_1133281 prefixEnd_1133281 28736684918917815633365 := by
  unfold tailWord_1133281
  simp only [CollatzResearch.WordTrace]
  refine ⟨41334153807323960830687697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27556102538215973887125131 41334153807323960830687697)
  ·
    refine ⟨31000615355492970623015773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41334153807323960830687697 31000615355492970623015773)
    ·
      refine ⟨11625230758309863983630915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31000615355492970623015773 11625230758309863983630915)
      ·
        refine ⟨17437846137464795975446373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11625230758309863983630915 17437846137464795975446373)
        ·
          refine ⟨3269596150774649245396195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17437846137464795975446373 3269596150774649245396195)
          ·
            refine ⟨4904394226161973868094293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269596150774649245396195 4904394226161973868094293)
            ·
              refine ⟨28736684918917815633365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4904394226161973868094293 28736684918917815633365)
              ·
                rfl

theorem cell21_1133281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 9].length) (baseStart_1133281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133281 prefixEnd_1133281 := by exact prefixLift 1133281
  have htrace : WordTrace (prefixWord ++ tailWord_1133281) baseStart_1133281 baseEnd_1133281 := by
    simpa [prefixWord, tailWord_1133281, baseEnd_1133281] using wordTrace_append hprefix tailTrace_1133281
  have hstable : (prefixWord ++ tailWord_1133281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133281).length < 2 ^ (prefixWord ++ tailWord_1133281).sum := by decide
  have hdescent : baseEnd_1133281 < baseStart_1133281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133298 : List Nat := [3, 2, 1, 3, 1, 3, 2, 6]
def baseStart_1133298 : Nat := 118140960795 + 1133298 * 2 ^ 59
def prefixEnd_1133298 : Nat := 4983230072969 + 3 ^ 40 * 1133298 * 2
def baseEnd_1133298 : Nat := 86211347967290696305639

theorem tailTrace_1133298 : CollatzResearch.WordTrace tailWord_1133298 prefixEnd_1133298 86211347967290696305639 := by
  unfold tailWord_1133298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10333693462065593183514137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27556515898841581822704365 10333693462065593183514137)
  ·
    refine ⟨7750270096549194887635603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10333693462065593183514137 7750270096549194887635603)
    ·
      refine ⟨11625405144823792331453405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7750270096549194887635603 11625405144823792331453405)
      ·
        refine ⟨4359526929308922124295027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11625405144823792331453405 4359526929308922124295027)
        ·
          refine ⟨6539290393963383186442541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359526929308922124295027 6539290393963383186442541)
          ·
            refine ⟨2452233897736268694915953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6539290393963383186442541 2452233897736268694915953)
            ·
              refine ⟨1839175423302201521186965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452233897736268694915953 1839175423302201521186965)
              ·
                refine ⟨86211347967290696305639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1839175423302201521186965 86211347967290696305639)
                ·
                  rfl

theorem cell21_1133298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_1133298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133298 prefixEnd_1133298 := by exact prefixLift 1133298
  have htrace : WordTrace (prefixWord ++ tailWord_1133298) baseStart_1133298 baseEnd_1133298 := by
    simpa [prefixWord, tailWord_1133298, baseEnd_1133298] using wordTrace_append hprefix tailTrace_1133298
  have hstable : (prefixWord ++ tailWord_1133298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133298).length < 2 ^ (prefixWord ++ tailWord_1133298).sum := by decide
  have hdescent : baseEnd_1133298 < baseStart_1133298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133343 : List Nat := [1, 1, 2, 4, 2, 2, 1, 4, 4]
def baseStart_1133343 : Nat := 118140960795 + 1133343 * 2 ^ 59
def prefixEnd_1133343 : Nat := 4983230072969 + 3 ^ 40 * 1133343 * 2
def baseEnd_1133343 : Nat := 258644313514962010666825

theorem tailTrace_1133343 : CollatzResearch.WordTrace tailWord_1133343 prefixEnd_1133343 258644313514962010666825 := by
  unfold tailWord_1133343
  simp only [CollatzResearch.WordTrace]
  refine ⟨41336415133099345419444683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27557610088732896946296455 41336415133099345419444683)
  ·
    refine ⟨62004622699649018129167025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41336415133099345419444683 62004622699649018129167025)
    ·
      refine ⟨46503467024736763596875269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62004622699649018129167025 46503467024736763596875269)
      ·
        refine ⟨8719400067138143174414113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46503467024736763596875269 8719400067138143174414113)
        ·
          refine ⟨6539550050353607380810585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8719400067138143174414113 6539550050353607380810585)
          ·
            refine ⟨4904662537765205535607939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6539550050353607380810585 4904662537765205535607939)
            ·
              refine ⟨7356993806647808303411909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904662537765205535607939 7356993806647808303411909)
              ·
                refine ⟨1379436338746464056889733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7356993806647808303411909 1379436338746464056889733)
                ·
                  refine ⟨258644313514962010666825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379436338746464056889733 258644313514962010666825)
                  ·
                    rfl

theorem cell21_1133343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 4, 4].length) (baseStart_1133343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133343 prefixEnd_1133343 := by exact prefixLift 1133343
  have htrace : WordTrace (prefixWord ++ tailWord_1133343) baseStart_1133343 baseEnd_1133343 := by
    simpa [prefixWord, tailWord_1133343, baseEnd_1133343] using wordTrace_append hprefix tailTrace_1133343
  have hstable : (prefixWord ++ tailWord_1133343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133343).length < 2 ^ (prefixWord ++ tailWord_1133343).sum := by decide
  have hdescent : baseEnd_1133343 < baseStart_1133343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133346 : List Nat := [3, 3, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1133346 : Nat := 118140960795 + 1133346 * 2 ^ 59
def prefixEnd_1133346 : Nat := 4983230072969 + 3 ^ 40 * 1133346 * 2
def baseEnd_1133346 : Nat := 258644998155834672116819

theorem tailTrace_1133346 : CollatzResearch.WordTrace tailWord_1133346 prefixEnd_1133346 258644998155834672116819 := by
  unfold tailWord_1133346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10334131138022119232950973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27557683034725651287869261 10334131138022119232950973)
  ·
    refine ⟨3875299176758294712356615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10334131138022119232950973 3875299176758294712356615)
    ·
      refine ⟨5812948765137442068534923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875299176758294712356615 5812948765137442068534923)
      ·
        refine ⟨8719423147706163102802385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812948765137442068534923 8719423147706163102802385)
        ·
          refine ⟨6539567360779622327101789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8719423147706163102802385 6539567360779622327101789)
          ·
            refine ⟨2452337760292358372663171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6539567360779622327101789 2452337760292358372663171)
            ·
              refine ⟨3678506640438537558994757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452337760292358372663171 3678506640438537558994757)
              ·
                refine ⟨689719995082225792311517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3678506640438537558994757 689719995082225792311517)
                ·
                  refine ⟨258644998155834672116819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689719995082225792311517 258644998155834672116819)
                  ·
                    rfl

theorem cell21_1133346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1133346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133346 prefixEnd_1133346 := by exact prefixLift 1133346
  have htrace : WordTrace (prefixWord ++ tailWord_1133346) baseStart_1133346 baseEnd_1133346 := by
    simpa [prefixWord, tailWord_1133346, baseEnd_1133346] using wordTrace_append hprefix tailTrace_1133346
  have hstable : (prefixWord ++ tailWord_1133346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133346).length < 2 ^ (prefixWord ++ tailWord_1133346).sum := by decide
  have hdescent : baseEnd_1133346 < baseStart_1133346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133380 : List Nat := [2, 3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_1133380 : Nat := 118140960795 + 1133380 * 2 ^ 59
def prefixEnd_1133380 : Nat := 4983230072969 + 3 ^ 40 * 1133380 * 2
def baseEnd_1133380 : Nat := 258652757419058168550083

theorem tailTrace_1133380 : CollatzResearch.WordTrace tailWord_1133380 prefixEnd_1133380 258652757419058168550083 := by
  unfold tailWord_1133380
  simp only [CollatzResearch.WordTrace]
  refine ⟨20668882316982650369270797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27558509755976867159027729 20668882316982650369270797)
  ·
    refine ⟨7750830868868493888476549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20668882316982650369270797 7750830868868493888476549)
    ·
      refine ⟨1453280787912842604089353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7750830868868493888476549 1453280787912842604089353)
      ·
        refine ⟨1089960590934631953067015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1453280787912842604089353 1089960590934631953067015)
        ·
          refine ⟨1634940886401947929600523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089960590934631953067015 1634940886401947929600523)
          ·
            refine ⟨2452411329602921894400785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634940886401947929600523 2452411329602921894400785)
            ·
              refine ⟨1839308497202191420800589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452411329602921894400785 1839308497202191420800589)
              ·
                refine ⟨689740686450821782800221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1839308497202191420800589 689740686450821782800221)
                ·
                  refine ⟨258652757419058168550083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689740686450821782800221 258652757419058168550083)
                  ·
                    rfl

theorem cell21_1133380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_1133380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133380 prefixEnd_1133380 := by exact prefixLift 1133380
  have htrace : WordTrace (prefixWord ++ tailWord_1133380) baseStart_1133380 baseEnd_1133380 := by
    simpa [prefixWord, tailWord_1133380, baseEnd_1133380] using wordTrace_append hprefix tailTrace_1133380
  have hstable : (prefixWord ++ tailWord_1133380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133380).length < 2 ^ (prefixWord ++ tailWord_1133380).sum := by decide
  have hdescent : baseEnd_1133380 < baseStart_1133380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133433 : List Nat := [1, 2, 1, 3, 2, 4, 1, 7]
def baseStart_1133433 : Nat := 118140960795 + 1133433 * 2 ^ 59
def prefixEnd_1133433 : Nat := 4983230072969 + 3 ^ 40 * 1133433 * 2
def baseEnd_1133433 : Nat := 86221617580380618055547

theorem tailTrace_1133433 : CollatzResearch.WordTrace tailWord_1133433 prefixEnd_1133433 86221617580380618055547 := by
  unfold tailWord_1133433
  simp only [CollatzResearch.WordTrace]
  refine ⟨41339697702773290790220953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27559798468515527193480635 41339697702773290790220953)
  ·
    refine ⟨31004773277079968092665715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41339697702773290790220953 31004773277079968092665715)
    ·
      refine ⟨46507159915619952138998573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31004773277079968092665715 46507159915619952138998573)
      ·
        refine ⟨17440184968357482052124465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46507159915619952138998573 17440184968357482052124465)
        ·
          refine ⟨13080138726268111539093349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17440184968357482052124465 13080138726268111539093349)
          ·
            refine ⟨2452526011175270913580003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13080138726268111539093349 2452526011175270913580003)
            ·
              refine ⟨3678789016762906370370005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452526011175270913580003 3678789016762906370370005)
              ·
                refine ⟨86221617580380618055547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3678789016762906370370005 86221617580380618055547)
                ·
                  rfl

theorem cell21_1133433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 7].length) (baseStart_1133433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133433 prefixEnd_1133433 := by exact prefixLift 1133433
  have htrace : WordTrace (prefixWord ++ tailWord_1133433) baseStart_1133433 baseEnd_1133433 := by
    simpa [prefixWord, tailWord_1133433, baseEnd_1133433] using wordTrace_append hprefix tailTrace_1133433
  have hstable : (prefixWord ++ tailWord_1133433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133433).length < 2 ^ (prefixWord ++ tailWord_1133433).sum := by decide
  have hdescent : baseEnd_1133433 < baseStart_1133433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133450 : List Nat := [3, 1, 2, 4, 1, 3, 7]
def baseStart_1133450 : Nat := 118140960795 + 1133450 * 2 ^ 59
def prefixEnd_1133450 : Nat := 4983230072969 + 3 ^ 40 * 1133450 * 2
def baseEnd_1133450 : Nat := 28740970263639289153697

theorem tailTrace_1133450 : CollatzResearch.WordTrace tailWord_1133450 prefixEnd_1133450 28740970263639289153697 := by
  unfold tailWord_1133450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335079435927925673397451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27560211829141135129059869 10335079435927925673397451)
  ·
    refine ⟨15502619153891888510096177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10335079435927925673397451 15502619153891888510096177)
    ·
      refine ⟨11626964365418916382572133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15502619153891888510096177 11626964365418916382572133)
      ·
        refine ⟨2180055818516046821732275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11626964365418916382572133 2180055818516046821732275)
        ·
          refine ⟨3270083727774070232598413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180055818516046821732275 3270083727774070232598413)
          ·
            refine ⟨1226281397915276337224405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3270083727774070232598413 1226281397915276337224405)
            ·
              refine ⟨28740970263639289153697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1226281397915276337224405 28740970263639289153697)
              ·
                rfl

theorem cell21_1133450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 7].length) (baseStart_1133450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133450 prefixEnd_1133450 := by exact prefixLift 1133450
  have htrace : WordTrace (prefixWord ++ tailWord_1133450) baseStart_1133450 baseEnd_1133450 := by
    simpa [prefixWord, tailWord_1133450, baseEnd_1133450] using wordTrace_append hprefix tailTrace_1133450
  have hstable : (prefixWord ++ tailWord_1133450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133450).length < 2 ^ (prefixWord ++ tailWord_1133450).sum := by decide
  have hdescent : baseEnd_1133450 < baseStart_1133450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133512 : List Nat := [2, 1, 3, 1, 5, 1, 2, 2, 4]
def baseStart_1133512 : Nat := 118140960795 + 1133512 * 2 ^ 59
def prefixEnd_1133512 : Nat := 4983230072969 + 3 ^ 40 * 1133512 * 2
def baseEnd_1133512 : Nat := 258682881617455272349813

theorem tailTrace_1133512 : CollatzResearch.WordTrace tailWord_1133512 prefixEnd_1133512 258682881617455272349813 := by
  unfold tailWord_1133512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20671289534743543641173395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27561719379658058188231193 20671289534743543641173395)
  ·
    refine ⟨31006934302115315461760093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20671289534743543641173395 31006934302115315461760093)
    ·
      refine ⟨11627600363293243298160035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31006934302115315461760093 11627600363293243298160035)
      ·
        refine ⟨17441400544939864947240053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11627600363293243298160035 17441400544939864947240053)
        ·
          refine ⟨1635131301088112338803755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17441400544939864947240053 1635131301088112338803755)
          ·
            refine ⟨2452696951632168508205633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635131301088112338803755 2452696951632168508205633)
            ·
              refine ⟨1839522713724126381154225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452696951632168508205633 1839522713724126381154225)
              ·
                refine ⟨1379642035293094785865669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839522713724126381154225 1379642035293094785865669)
                ·
                  refine ⟨258682881617455272349813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1379642035293094785865669 258682881617455272349813)
                  ·
                    rfl

theorem cell21_1133512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_1133512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133512 prefixEnd_1133512 := by exact prefixLift 1133512
  have htrace : WordTrace (prefixWord ++ tailWord_1133512) baseStart_1133512 baseEnd_1133512 := by
    simpa [prefixWord, tailWord_1133512, baseEnd_1133512] using wordTrace_append hprefix tailTrace_1133512
  have hstable : (prefixWord ++ tailWord_1133512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133512).length < 2 ^ (prefixWord ++ tailWord_1133512).sum := by decide
  have hdescent : baseEnd_1133512 < baseStart_1133512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133602 : List Nat := [3, 3, 1, 1, 1, 3, 4, 5]
def baseStart_1133602 : Nat := 118140960795 + 1133602 * 2 ^ 59
def prefixEnd_1133602 : Nat := 4983230072969 + 3 ^ 40 * 1133602 * 2
def baseEnd_1133602 : Nat := 86234473614545038616543

theorem tailTrace_1133602 : CollatzResearch.WordTrace tailWord_1133602 prefixEnd_1133602 86234473614545038616543 := by
  unfold tailWord_1133602
  simp only [CollatzResearch.WordTrace]
  refine ⟨10336465409790258163280765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27563907759440688435415373 10336465409790258163280765)
  ·
    refine ⟨3876174528671346811230287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10336465409790258163280765 3876174528671346811230287)
    ·
      refine ⟨5814261793007020216845431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3876174528671346811230287 5814261793007020216845431)
      ·
        refine ⟨8721392689510530325268147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814261793007020216845431 8721392689510530325268147)
        ·
          refine ⟨13082089034265795487902221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8721392689510530325268147 13082089034265795487902221)
          ·
            refine ⟨4905783387849673307963333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13082089034265795487902221 4905783387849673307963333)
            ·
              refine ⟨919834385221813745243125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4905783387849673307963333 919834385221813745243125)
              ·
                refine ⟨86234473614545038616543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 919834385221813745243125 86234473614545038616543)
                ·
                  rfl

theorem cell21_1133602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_1133602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133602 prefixEnd_1133602 := by exact prefixLift 1133602
  have htrace : WordTrace (prefixWord ++ tailWord_1133602) baseStart_1133602 baseEnd_1133602 := by
    simpa [prefixWord, tailWord_1133602, baseEnd_1133602] using wordTrace_append hprefix tailTrace_1133602
  have hstable : (prefixWord ++ tailWord_1133602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133602).length < 2 ^ (prefixWord ++ tailWord_1133602).sum := by decide
  have hdescent : baseEnd_1133602 < baseStart_1133602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133726 : List Nat := [4, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1133726 : Nat := 118140960795 + 1133726 * 2 ^ 59
def prefixEnd_1133726 : Nat := 4983230072969 + 3 ^ 40 * 1133726 * 2
def baseEnd_1133726 : Nat := 258731719333038455782709

theorem tailTrace_1133726 : CollatzResearch.WordTrace tailWord_1133726 prefixEnd_1133726 258731719333038455782709 := by
  unfold tailWord_1133726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168798036338975228829629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27566922860474534553758021 5168798036338975228829629)
  ·
    refine ⟨1938299263627115710811111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5168798036338975228829629 1938299263627115710811111)
    ·
      refine ⟨2907448895440673566216667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1938299263627115710811111 2907448895440673566216667)
      ·
        refine ⟨4361173343161010349325001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907448895440673566216667 4361173343161010349325001)
        ·
          refine ⟨3270880007370757761993751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361173343161010349325001 3270880007370757761993751)
          ·
            refine ⟨4906320011056136642990627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270880007370757761993751 4906320011056136642990627)
            ·
              refine ⟨7359480016584204964485941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906320011056136642990627 7359480016584204964485941)
              ·
                refine ⟨689951251554769215420557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7359480016584204964485941 689951251554769215420557)
                ·
                  refine ⟨258731719333038455782709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689951251554769215420557 258731719333038455782709)
                  ·
                    rfl

theorem cell21_1133726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1133726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133726 prefixEnd_1133726 := by exact prefixLift 1133726
  have htrace : WordTrace (prefixWord ++ tailWord_1133726) baseStart_1133726 baseEnd_1133726 := by
    simpa [prefixWord, tailWord_1133726, baseEnd_1133726] using wordTrace_append hprefix tailTrace_1133726
  have hstable : (prefixWord ++ tailWord_1133726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133726).length < 2 ^ (prefixWord ++ tailWord_1133726).sum := by decide
  have hdescent : baseEnd_1133726 < baseStart_1133726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133796 : List Nat := [2, 3, 1, 1, 1, 2, 11]
def baseStart_1133796 : Nat := 118140960795 + 1133796 * 2 ^ 59
def prefixEnd_1133796 : Nat := 4983230072969 + 3 ^ 40 * 1133796 * 2
def baseEnd_1133796 : Nat := 28749743809637098846211

theorem tailTrace_1133796 : CollatzResearch.WordTrace tailWord_1133796 prefixEnd_1133796 28749743809637098846211 := by
  unfold tailWord_1133796
  simp only [CollatzResearch.WordTrace]
  refine ⟨20676468700229101892842621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27568624933638802523790161 20676468700229101892842621)
  ·
    refine ⟨7753675762585913209815983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20676468700229101892842621 7753675762585913209815983)
    ·
      refine ⟨11630513643878869814723975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7753675762585913209815983 11630513643878869814723975)
      ·
        refine ⟨17445770465818304722085963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11630513643878869814723975 17445770465818304722085963)
        ·
          refine ⟨26168655698727457083128945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17445770465818304722085963 26168655698727457083128945)
          ·
            refine ⟨19626491774045592812346709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26168655698727457083128945 19626491774045592812346709)
            ·
              refine ⟨28749743809637098846211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19626491774045592812346709 28749743809637098846211)
              ·
                rfl

theorem cell21_1133796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 11].length) (baseStart_1133796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133796 prefixEnd_1133796 := by exact prefixLift 1133796
  have htrace : WordTrace (prefixWord ++ tailWord_1133796) baseStart_1133796 baseEnd_1133796 := by
    simpa [prefixWord, tailWord_1133796, baseEnd_1133796] using wordTrace_append hprefix tailTrace_1133796
  have hstable : (prefixWord ++ tailWord_1133796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133796).length < 2 ^ (prefixWord ++ tailWord_1133796).sum := by decide
  have hdescent : baseEnd_1133796 < baseStart_1133796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133802 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 3]
def baseStart_1133802 : Nat := 118140960795 + 1133802 * 2 ^ 59
def prefixEnd_1133802 : Nat := 4983230072969 + 3 ^ 40 * 1133802 * 2
def baseEnd_1133802 : Nat := 258749063568479212515887

theorem tailTrace_1133802 : CollatzResearch.WordTrace tailWord_1133802 prefixEnd_1133802 258749063568479212515887 := by
  unfold tailWord_1133802
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338289059609116702600915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27568770825624311206935773 10338289059609116702600915)
  ·
    refine ⟨15507433589413675053901373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10338289059609116702600915 15507433589413675053901373)
    ·
      refine ⟨5815287596030128145213015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15507433589413675053901373 5815287596030128145213015)
      ·
        refine ⟨8722931394045192217819523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815287596030128145213015 8722931394045192217819523)
        ·
          refine ⟨13084397091067788326729285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8722931394045192217819523 13084397091067788326729285)
          ·
            refine ⟨2453324454575210311261741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13084397091067788326729285 2453324454575210311261741)
            ·
              refine ⟨919996670465703866723153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2453324454575210311261741 919996670465703866723153)
              ·
                refine ⟨689997502849277900042365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 919996670465703866723153 689997502849277900042365)
                ·
                  refine ⟨258749063568479212515887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689997502849277900042365 258749063568479212515887)
                  ·
                    rfl

theorem cell21_1133802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_1133802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133802 prefixEnd_1133802 := by exact prefixLift 1133802
  have htrace : WordTrace (prefixWord ++ tailWord_1133802) baseStart_1133802 baseEnd_1133802 := by
    simpa [prefixWord, tailWord_1133802, baseEnd_1133802] using wordTrace_append hprefix tailTrace_1133802
  have hstable : (prefixWord ++ tailWord_1133802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133802).length < 2 ^ (prefixWord ++ tailWord_1133802).sum := by decide
  have hdescent : baseEnd_1133802 < baseStart_1133802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133861 : List Nat := [1, 3, 1, 2, 4, 2, 1, 4, 3]
def baseStart_1133861 : Nat := 118140960795 + 1133861 * 2 ^ 59
def prefixEnd_1133861 : Nat := 4983230072969 + 3 ^ 40 * 1133861 * 2
def baseEnd_1133861 : Nat := 258762528172308221032433

theorem tailTrace_1133861 : CollatzResearch.WordTrace tailWord_1133861 prefixEnd_1133861 258762528172308221032433 := by
  unfold tailWord_1133861
  simp only [CollatzResearch.WordTrace]
  refine ⟨41355308145222719886801437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27570205430148479924534291 41355308145222719886801437)
  ·
    refine ⟨15508240554458519957550539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41355308145222719886801437 15508240554458519957550539)
    ·
      refine ⟨23262360831687779936325809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15508240554458519957550539 23262360831687779936325809)
      ·
        refine ⟨17446770623765834952244357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23262360831687779936325809 17446770623765834952244357)
        ·
          refine ⟨3271269491956094053545817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17446770623765834952244357 3271269491956094053545817)
          ·
            refine ⟨2453452118967070540159363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271269491956094053545817 2453452118967070540159363)
            ·
              refine ⟨3680178178450605810239045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453452118967070540159363 3680178178450605810239045)
              ·
                refine ⟨690033408459488589419821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3680178178450605810239045 690033408459488589419821)
                ·
                  refine ⟨258762528172308221032433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690033408459488589419821 258762528172308221032433)
                  ·
                    rfl

theorem cell21_1133861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_1133861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133861 prefixEnd_1133861 := by exact prefixLift 1133861
  have htrace : WordTrace (prefixWord ++ tailWord_1133861) baseStart_1133861 baseEnd_1133861 := by
    simpa [prefixWord, tailWord_1133861, baseEnd_1133861] using wordTrace_append hprefix tailTrace_1133861
  have hstable : (prefixWord ++ tailWord_1133861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133861).length < 2 ^ (prefixWord ++ tailWord_1133861).sum := by decide
  have hdescent : baseEnd_1133861 < baseStart_1133861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133878 : List Nat := [5, 1, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1133878 : Nat := 118140960795 + 1133878 * 2 ^ 59
def prefixEnd_1133878 : Nat := 4983230072969 + 3 ^ 40 * 1133878 * 2
def baseEnd_1133878 : Nat := 258766407803919969249065

theorem tailTrace_1133878 : CollatzResearch.WordTrace tailWord_1133878 prefixEnd_1133878 258766407803919969249065 := by
  unfold tailWord_1133878
  simp only [CollatzResearch.WordTrace]
  refine ⟨2584745511635070736885643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27570618790774087860113525 2584745511635070736885643)
  ·
    refine ⟨3877118267452606105328465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2584745511635070736885643 3877118267452606105328465)
    ·
      refine ⟨2907838700589454578996349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3877118267452606105328465 2907838700589454578996349)
      ·
        refine ⟨1090439512721045467123631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2907838700589454578996349 1090439512721045467123631)
        ·
          refine ⟨1635659269081568200685447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1090439512721045467123631 1635659269081568200685447)
          ·
            refine ⟨2453488903622352301028171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635659269081568200685447 2453488903622352301028171)
            ·
              refine ⟨3680233355433528451542257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453488903622352301028171 3680233355433528451542257)
              ·
                refine ⟨2760175016575146338656693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680233355433528451542257 2760175016575146338656693)
                ·
                  refine ⟨258766407803919969249065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760175016575146338656693 258766407803919969249065)
                  ·
                    rfl

theorem cell21_1133878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1133878 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133878 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133878 prefixEnd_1133878 := by exact prefixLift 1133878
  have htrace : WordTrace (prefixWord ++ tailWord_1133878) baseStart_1133878 baseEnd_1133878 := by
    simpa [prefixWord, tailWord_1133878, baseEnd_1133878] using wordTrace_append hprefix tailTrace_1133878
  have hstable : (prefixWord ++ tailWord_1133878).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133878).length < 2 ^ (prefixWord ++ tailWord_1133878).sum := by decide
  have hdescent : baseEnd_1133878 < baseStart_1133878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133920 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_1133920 : Nat := 118140960795 + 1133920 * 2 ^ 59
def prefixEnd_1133920 : Nat := 4983230072969 + 3 ^ 40 * 1133920 * 2
def baseEnd_1133920 : Nat := 258775992776137229548979

theorem tailTrace_1133920 : CollatzResearch.WordTrace tailWord_1133920 prefixEnd_1133920 258775992776137229548979 := by
  unfold tailWord_1133920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20678730026004486481599607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27571640034672648642132809 20678730026004486481599607)
  ·
    refine ⟨31018095039006729722399411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20678730026004486481599607 31018095039006729722399411)
    ·
      refine ⟨46527142558510094583599117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31018095039006729722399411 46527142558510094583599117)
      ·
        refine ⟨17447678459441285468849669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46527142558510094583599117 17447678459441285468849669)
        ·
          refine ⟨3271439711145241025409313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17447678459441285468849669 3271439711145241025409313)
          ·
            refine ⟨2453579783358930769056985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271439711145241025409313 2453579783358930769056985)
            ·
              refine ⟨1840184837519198076792739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2453579783358930769056985 1840184837519198076792739)
              ·
                refine ⟨2760277256278797115189109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840184837519198076792739 2760277256278797115189109)
                ·
                  refine ⟨258775992776137229548979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760277256278797115189109 258775992776137229548979)
                  ·
                    rfl

theorem cell21_1133920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_1133920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133920 prefixEnd_1133920 := by exact prefixLift 1133920
  have htrace : WordTrace (prefixWord ++ tailWord_1133920) baseStart_1133920 baseEnd_1133920 := by
    simpa [prefixWord, tailWord_1133920, baseEnd_1133920] using wordTrace_append hprefix tailTrace_1133920
  have hstable : (prefixWord ++ tailWord_1133920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133920).length < 2 ^ (prefixWord ++ tailWord_1133920).sum := by decide
  have hdescent : baseEnd_1133920 < baseStart_1133920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1133948 : List Nat := [2, 2, 2, 1, 1, 1, 5, 7]
def baseStart_1133948 : Nat := 118140960795 + 1133948 * 2 ^ 59
def prefixEnd_1133948 : Nat := 4983230072969 + 3 ^ 40 * 1133948 * 2
def baseEnd_1133948 : Nat := 86260794252538467694085

theorem tailTrace_1133948 : CollatzResearch.WordTrace tailWord_1133948 prefixEnd_1133948 86260794252538467694085 := by
  unfold tailWord_1133948
  simp only [CollatzResearch.WordTrace]
  refine ⟨20679240647953766872609249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27572320863938355830145665 20679240647953766872609249)
  ·
    refine ⟨15509430485965325154456937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20679240647953766872609249 15509430485965325154456937)
    ·
      refine ⟨11632072864473993865842703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15509430485965325154456937 11632072864473993865842703)
      ·
        refine ⟨17448109296710990798764055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11632072864473993865842703 17448109296710990798764055)
        ·
          refine ⟨26172163945066486198146083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17448109296710990798764055 26172163945066486198146083)
          ·
            refine ⟨39258245917599729297219125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26172163945066486198146083 39258245917599729297219125)
            ·
              refine ⟨3680460554774974621614293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39258245917599729297219125 3680460554774974621614293)
              ·
                refine ⟨86260794252538467694085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3680460554774974621614293 86260794252538467694085)
                ·
                  rfl

theorem cell21_1133948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 7].length) (baseStart_1133948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1133948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1133948 prefixEnd_1133948 := by exact prefixLift 1133948
  have htrace : WordTrace (prefixWord ++ tailWord_1133948) baseStart_1133948 baseEnd_1133948 := by
    simpa [prefixWord, tailWord_1133948, baseEnd_1133948] using wordTrace_append hprefix tailTrace_1133948
  have hstable : (prefixWord ++ tailWord_1133948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1133948).length < 2 ^ (prefixWord ++ tailWord_1133948).sum := by decide
  have hdescent : baseEnd_1133948 < baseStart_1133948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1133948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134041 : List Nat := [1, 2, 1, 2, 4, 4, 1, 6]
def baseStart_1134041 : Nat := 118140960795 + 1134041 * 2 ^ 59
def prefixEnd_1134041 : Nat := 4983230072969 + 3 ^ 40 * 1134041 * 2
def baseEnd_1134041 : Nat := 86267868874889302677355

theorem tailTrace_1134041 : CollatzResearch.WordTrace tailWord_1134041 prefixEnd_1134041 86267868874889302677355 := by
  unfold tailWord_1134041
  simp only [CollatzResearch.WordTrace]
  refine ⟨41361873284570610628353977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27574582189713740418902651 41361873284570610628353977)
  ·
    refine ⟨31021404963427957971265483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41361873284570610628353977 31021404963427957971265483)
    ·
      refine ⟨46532107445141936956898225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31021404963427957971265483 46532107445141936956898225)
      ·
        refine ⟨34899080583856452717673669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46532107445141936956898225 34899080583856452717673669)
        ·
          refine ⟨6543577609473084884563813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34899080583856452717673669 6543577609473084884563813)
          ·
            refine ⟨1226920801776203415855715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6543577609473084884563813 1226920801776203415855715)
            ·
              refine ⟨1840381202664305123783573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226920801776203415855715 1840381202664305123783573)
              ·
                refine ⟨86267868874889302677355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1840381202664305123783573 86267868874889302677355)
                ·
                  rfl

theorem cell21_1134041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 6].length) (baseStart_1134041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134041 prefixEnd_1134041 := by exact prefixLift 1134041
  have htrace : WordTrace (prefixWord ++ tailWord_1134041) baseStart_1134041 baseEnd_1134041 := by
    simpa [prefixWord, tailWord_1134041, baseEnd_1134041] using wordTrace_append hprefix tailTrace_1134041
  have hstable : (prefixWord ++ tailWord_1134041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134041).length < 2 ^ (prefixWord ++ tailWord_1134041).sum := by decide
  have hdescent : baseEnd_1134041 < baseStart_1134041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134055 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 7]
def baseStart_1134055 : Nat := 118140960795 + 1134055 * 2 ^ 59
def prefixEnd_1134055 : Nat := 4983230072969 + 3 ^ 40 * 1134055 * 2
def baseEnd_1134055 : Nat := 258806801615406994798703

theorem tailTrace_1134055 : CollatzResearch.WordTrace tailWord_1134055 prefixEnd_1134055 258806801615406994798703 := by
  unfold tailWord_1134055
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362383906519891019363619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27574922604346594012909079 41362383906519891019363619)
  ·
    refine ⟨62043575859779836529045429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41362383906519891019363619 62043575859779836529045429)
    ·
      refine ⟨5816585236854359674598009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62043575859779836529045429 5816585236854359674598009)
      ·
        refine ⟨4362438927640769755948507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5816585236854359674598009 4362438927640769755948507)
        ·
          refine ⟨6543658391461154633922761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362438927640769755948507 6543658391461154633922761)
          ·
            refine ⟨4907743793595865975442071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6543658391461154633922761 4907743793595865975442071)
            ·
              refine ⟨7361615690393798963163107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907743793595865975442071 7361615690393798963163107)
              ·
                refine ⟨11042423535590698444744661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7361615690393798963163107 11042423535590698444744661)
                ·
                  refine ⟨258806801615406994798703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11042423535590698444744661 258806801615406994798703)
                  ·
                    rfl

theorem cell21_1134055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 7].length) (baseStart_1134055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134055 prefixEnd_1134055 := by exact prefixLift 1134055
  have htrace : WordTrace (prefixWord ++ tailWord_1134055) baseStart_1134055 baseEnd_1134055 := by
    simpa [prefixWord, tailWord_1134055, baseEnd_1134055] using wordTrace_append hprefix tailTrace_1134055
  have hstable : (prefixWord ++ tailWord_1134055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134055).length < 2 ^ (prefixWord ++ tailWord_1134055).sum := by decide
  have hdescent : baseEnd_1134055 < baseStart_1134055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134058 : List Nat := [3, 1, 3, 1, 4, 1, 3, 5]
def baseStart_1134058 : Nat := 118140960795 + 1134058 * 2 ^ 59
def prefixEnd_1134058 : Nat := 4983230072969 + 3 ^ 40 * 1134058 * 2
def baseEnd_1134058 : Nat := 86269162085426552082899

theorem tailTrace_1134058 : CollatzResearch.WordTrace tailWord_1134058 prefixEnd_1134058 86269162085426552082899 := by
  unfold tailWord_1134058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10340623331377255632930707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27574995550339348354481885 10340623331377255632930707)
  ·
    refine ⟨15510934997065883449396061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10340623331377255632930707 15510934997065883449396061)
    ·
      refine ⟨5816600623899706293523523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15510934997065883449396061 5816600623899706293523523)
      ·
        refine ⟨8724900935849559440285285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5816600623899706293523523 8724900935849559440285285)
        ·
          refine ⟨1635918925471792395053491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8724900935849559440285285 1635918925471792395053491)
          ·
            refine ⟨2453878388207688592580237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635918925471792395053491 2453878388207688592580237)
            ·
              refine ⟨920204395577883222217589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2453878388207688592580237 920204395577883222217589)
              ·
                refine ⟨86269162085426552082899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 920204395577883222217589 86269162085426552082899)
                ·
                  rfl

theorem cell21_1134058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 5].length) (baseStart_1134058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134058 prefixEnd_1134058 := by exact prefixLift 1134058
  have htrace : WordTrace (prefixWord ++ tailWord_1134058) baseStart_1134058 baseEnd_1134058 := by
    simpa [prefixWord, tailWord_1134058, baseEnd_1134058] using wordTrace_append hprefix tailTrace_1134058
  have hstable : (prefixWord ++ tailWord_1134058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134058).length < 2 ^ (prefixWord ++ tailWord_1134058).sum := by decide
  have hdescent : baseEnd_1134058 < baseStart_1134058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134072 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 3]
def baseStart_1134072 : Nat := 118140960795 + 1134072 * 2 ^ 59
def prefixEnd_1134072 : Nat := 4983230072969 + 3 ^ 40 * 1134072 * 2
def baseEnd_1134072 : Nat := 258810681247018743015335

theorem tailTrace_1134072 : CollatzResearch.WordTrace tailWord_1134072 prefixEnd_1134072 258810681247018743015335 := by
  unfold tailWord_1134072
  simp only [CollatzResearch.WordTrace]
  refine ⟨20681501973729151461366235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27575335964972201948488313 20681501973729151461366235)
  ·
    refine ⟨31022252960593727192049353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20681501973729151461366235 31022252960593727192049353)
    ·
      refine ⟨23266689720445295394037015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31022252960593727192049353 23266689720445295394037015)
      ·
        refine ⟨34900034580667943091055523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23266689720445295394037015 34900034580667943091055523)
        ·
          refine ⟨52350051871001914636583285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34900034580667943091055523 52350051871001914636583285)
          ·
            refine ⟨4907817362906429497179683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52350051871001914636583285 4907817362906429497179683)
            ·
              refine ⟨7361726044359644245769525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907817362906429497179683 7361726044359644245769525)
              ·
                refine ⟨690161816658716648040893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7361726044359644245769525 690161816658716648040893)
                ·
                  refine ⟨258810681247018743015335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690161816658716648040893 258810681247018743015335)
                  ·
                    rfl

theorem cell21_1134072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 3].length) (baseStart_1134072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134072 prefixEnd_1134072 := by exact prefixLift 1134072
  have htrace : WordTrace (prefixWord ++ tailWord_1134072) baseStart_1134072 baseEnd_1134072 := by
    simpa [prefixWord, tailWord_1134072, baseEnd_1134072] using wordTrace_append hprefix tailTrace_1134072
  have hstable : (prefixWord ++ tailWord_1134072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134072).length < 2 ^ (prefixWord ++ tailWord_1134072).sum := by decide
  have hdescent : baseEnd_1134072 < baseStart_1134072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134078 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 4]
def baseStart_1134078 : Nat := 118140960795 + 1134078 * 2 ^ 59
def prefixEnd_1134078 : Nat := 4983230072969 + 3 ^ 40 * 1134078 * 2
def baseEnd_1134078 : Nat := 258812050528764065915323

theorem tailTrace_1134078 : CollatzResearch.WordTrace tailWord_1134078 prefixEnd_1134078 258812050528764065915323 := by
  unfold tailWord_1134078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170402848179570743431361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27575481856957710631633925 5170402848179570743431361)
  ·
    refine ⟨3877802136134678057573521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5170402848179570743431361 3877802136134678057573521)
    ·
      refine ⟨2908351602101008543180141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3877802136134678057573521 2908351602101008543180141)
      ·
        refine ⟨1090631850787878203692553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2908351602101008543180141 1090631850787878203692553)
        ·
          refine ⟨817973888090908652769415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1090631850787878203692553 817973888090908652769415)
          ·
            refine ⟨1226960832136362979154123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817973888090908652769415 1226960832136362979154123)
            ·
              refine ⟨1840441248204544468731185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1226960832136362979154123 1840441248204544468731185)
              ·
                refine ⟨1380330936153408351548389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1840441248204544468731185 1380330936153408351548389)
                ·
                  refine ⟨258812050528764065915323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380330936153408351548389 258812050528764065915323)
                  ·
                    rfl

theorem cell21_1134078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_1134078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134078 prefixEnd_1134078 := by exact prefixLift 1134078
  have htrace : WordTrace (prefixWord ++ tailWord_1134078) baseStart_1134078 baseEnd_1134078 := by
    simpa [prefixWord, tailWord_1134078, baseEnd_1134078] using wordTrace_append hprefix tailTrace_1134078
  have hstable : (prefixWord ++ tailWord_1134078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134078).length < 2 ^ (prefixWord ++ tailWord_1134078).sum := by decide
  have hdescent : baseEnd_1134078 < baseStart_1134078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134134 : List Nat := [5, 1, 2, 1, 3, 2, 7]
def baseStart_1134134 : Nat := 118140960795 + 1134134 * 2 ^ 59
def prefixEnd_1134134 : Nat := 4983230072969 + 3 ^ 40 * 1134134 * 2
def baseEnd_1134134 : Nat := 28758314499080045886875

theorem tailTrace_1134134 : CollatzResearch.WordTrace tailWord_1134134 prefixEnd_1134134 28758314499080045886875 := by
  unfold tailWord_1134134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585329079577105469468091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27576843515489125007659637 2585329079577105469468091)
  ·
    refine ⟨3877993619365658204202137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2585329079577105469468091 3877993619365658204202137)
    ·
      refine ⟨2908495214524243653151603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3877993619365658204202137 2908495214524243653151603)
      ·
        refine ⟨4362742821786365479727405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908495214524243653151603 4362742821786365479727405)
        ·
          refine ⟨1636028558169887054897777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4362742821786365479727405 1636028558169887054897777)
          ·
            refine ⟨1227021418627415291173333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1636028558169887054897777 1227021418627415291173333)
            ·
              refine ⟨28758314499080045886875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1227021418627415291173333 28758314499080045886875)
              ·
                rfl

theorem cell21_1134134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 7].length) (baseStart_1134134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134134 prefixEnd_1134134 := by exact prefixLift 1134134
  have htrace : WordTrace (prefixWord ++ tailWord_1134134) baseStart_1134134 baseEnd_1134134 := by
    simpa [prefixWord, tailWord_1134134, baseEnd_1134134] using wordTrace_append hprefix tailTrace_1134134
  have hstable : (prefixWord ++ tailWord_1134134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134134).length < 2 ^ (prefixWord ++ tailWord_1134134).sum := by decide
  have hdescent : baseEnd_1134134 < baseStart_1134134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134241 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 3]
def baseStart_1134241 : Nat := 118140960795 + 1134241 * 2 ^ 59
def prefixEnd_1134241 : Nat := 4983230072969 + 3 ^ 40 * 1134241 * 2
def baseEnd_1134241 : Nat := 258849249349512004698323

theorem tailTrace_1134241 : CollatzResearch.WordTrace tailWord_1134241 prefixEnd_1134241 258849249349512004698323 := by
  unfold tailWord_1134241
  simp only [CollatzResearch.WordTrace]
  refine ⟨41369167883846044785634577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27579445255897363190423051 41369167883846044785634577)
  ·
    refine ⟨31026875912884533589225933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41369167883846044785634577 31026875912884533589225933)
    ·
      refine ⟨11635078467331700095959725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31026875912884533589225933 11635078467331700095959725)
      ·
        refine ⟨4363154425249387535984897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11635078467331700095959725 4363154425249387535984897)
        ·
          refine ⟨3272365818937040651988673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4363154425249387535984897 3272365818937040651988673)
          ·
            refine ⟨2454274364202780488991505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3272365818937040651988673 2454274364202780488991505)
            ·
              refine ⟨1840705773152085366743629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454274364202780488991505 1840705773152085366743629)
              ·
                refine ⟨690264664932032012528861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1840705773152085366743629 690264664932032012528861)
                ·
                  refine ⟨258849249349512004698323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690264664932032012528861 258849249349512004698323)
                  ·
                    rfl

theorem cell21_1134241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_1134241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134241 prefixEnd_1134241 := by exact prefixLift 1134241
  have htrace : WordTrace (prefixWord ++ tailWord_1134241) baseStart_1134241 baseEnd_1134241 := by
    simpa [prefixWord, tailWord_1134241, baseEnd_1134241] using wordTrace_append hprefix tailTrace_1134241
  have hstable : (prefixWord ++ tailWord_1134241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134241).length < 2 ^ (prefixWord ++ tailWord_1134241).sum := by decide
  have hdescent : baseEnd_1134241 < baseStart_1134241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134297 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 6]
def baseStart_1134297 : Nat := 118140960795 + 1134297 * 2 ^ 59
def prefixEnd_1134297 : Nat := 4983230072969 + 3 ^ 40 * 1134297 * 2
def baseEnd_1134297 : Nat := 258862029312468351764875

theorem tailTrace_1134297 : CollatzResearch.WordTrace tailWord_1134297 prefixEnd_1134297 258862029312468351764875 := by
  unfold tailWord_1134297
  simp only [CollatzResearch.WordTrace]
  refine ⟨41371210371643166349673145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27580806914428777566448763 41371210371643166349673145)
  ·
    refine ⟨31028407778732374762254859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41371210371643166349673145 31028407778732374762254859)
    ·
      refine ⟨46542611668098562143382289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31028407778732374762254859 46542611668098562143382289)
      ·
        refine ⟨34906958751073921607536717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46542611668098562143382289 34906958751073921607536717)
        ·
          refine ⟨13090109531652720602826269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34906958751073921607536717 13090109531652720602826269)
          ·
            refine ⟨4908791074369770226059851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13090109531652720602826269 4908791074369770226059851)
            ·
              refine ⟨7363186611554655339089777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908791074369770226059851 7363186611554655339089777)
              ·
                refine ⟨5522389958665991504317333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7363186611554655339089777 5522389958665991504317333)
                ·
                  refine ⟨258862029312468351764875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5522389958665991504317333 258862029312468351764875)
                  ·
                    rfl

theorem cell21_1134297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 6].length) (baseStart_1134297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134297 prefixEnd_1134297 := by exact prefixLift 1134297
  have htrace : WordTrace (prefixWord ++ tailWord_1134297) baseStart_1134297 baseEnd_1134297 := by
    simpa [prefixWord, tailWord_1134297, baseEnd_1134297] using wordTrace_append hprefix tailTrace_1134297
  have hstable : (prefixWord ++ tailWord_1134297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134297).length < 2 ^ (prefixWord ++ tailWord_1134297).sum := by decide
  have hdescent : baseEnd_1134297 < baseStart_1134297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134497 : List Nat := [1, 2, 3, 4, 2, 1, 2, 6]
def baseStart_1134497 : Nat := 118140960795 + 1134497 * 2 ^ 59
def prefixEnd_1134497 : Nat := 4983230072969 + 3 ^ 40 * 1134497 * 2
def baseEnd_1134497 : Nat := 86302557345770816143711

theorem tailTrace_1134497 : CollatzResearch.WordTrace tailWord_1134497 prefixEnd_1134497 86302557345770816143711 := by
  unfold tailWord_1134497
  simp only [CollatzResearch.WordTrace]
  refine ⟨41378504970918600506953745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27585669980612400337969163 41378504970918600506953745)
  ·
    refine ⟨31033878728188950380215309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41378504970918600506953745 31033878728188950380215309)
    ·
      refine ⟨11637704523070856392580741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31033878728188950380215309 11637704523070856392580741)
      ·
        refine ⟨2182069598075785573608889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11637704523070856392580741 2182069598075785573608889)
        ·
          refine ⟨1636552198556839180206667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2182069598075785573608889 1636552198556839180206667)
          ·
            refine ⟨2454828297835258770310001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636552198556839180206667 2454828297835258770310001)
            ·
              refine ⟨1841121223376444077732501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2454828297835258770310001 1841121223376444077732501)
              ·
                refine ⟨86302557345770816143711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1841121223376444077732501 86302557345770816143711)
                ·
                  rfl

theorem cell21_1134497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 6].length) (baseStart_1134497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134497 prefixEnd_1134497 := by exact prefixLift 1134497
  have htrace : WordTrace (prefixWord ++ tailWord_1134497) baseStart_1134497 baseEnd_1134497 := by
    simpa [prefixWord, tailWord_1134497, baseEnd_1134497] using wordTrace_append hprefix tailTrace_1134497
  have hstable : (prefixWord ++ tailWord_1134497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134497).length < 2 ^ (prefixWord ++ tailWord_1134497).sum := by decide
  have hdescent : baseEnd_1134497 < baseStart_1134497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134542 : List Nat := [4, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_1134542 : Nat := 118140960795 + 1134542 * 2 ^ 59
def prefixEnd_1134542 : Nat := 4983230072969 + 3 ^ 40 * 1134542 * 2
def baseEnd_1134542 : Nat := 258917941650402370181041

theorem tailTrace_1134542 : CollatzResearch.WordTrace tailWord_1134542 prefixEnd_1134542 258917941650402370181041 := by
  unfold tailWord_1134542
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172518281969446649042735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27586764170503715461561253 5172518281969446649042735)
  ·
    refine ⟨7758777422954169973564103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5172518281969446649042735 7758777422954169973564103)
    ·
      refine ⟨11638166134431254960346155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758777422954169973564103 11638166134431254960346155)
      ·
        refine ⟨17457249201646882440519233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11638166134431254960346155 17457249201646882440519233)
        ·
          refine ⟨13092936901235161830389425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17457249201646882440519233 13092936901235161830389425)
          ·
            refine ⟨9819702675926371372792069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13092936901235161830389425 9819702675926371372792069)
            ·
              refine ⟨1841194251736194632398513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9819702675926371372792069 1841194251736194632398513)
              ·
                refine ⟨1380895688802145974298885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841194251736194632398513 1380895688802145974298885)
                ·
                  refine ⟨258917941650402370181041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1380895688802145974298885 258917941650402370181041)
                  ·
                    rfl

theorem cell21_1134542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_1134542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134542 prefixEnd_1134542 := by exact prefixLift 1134542
  have htrace : WordTrace (prefixWord ++ tailWord_1134542) baseStart_1134542 baseEnd_1134542 := by
    simpa [prefixWord, tailWord_1134542, baseEnd_1134542] using wordTrace_append hprefix tailTrace_1134542
  have hstable : (prefixWord ++ tailWord_1134542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134542).length < 2 ^ (prefixWord ++ tailWord_1134542).sum := by decide
  have hdescent : baseEnd_1134542 < baseStart_1134542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134587 : List Nat := [1, 1, 1, 1, 1, 3, 5, 5, 3]
def baseStart_1134587 : Nat := 118140960795 + 1134587 * 2 ^ 59
def prefixEnd_1134587 : Nat := 4983230072969 + 3 ^ 40 * 1134587 * 2
def baseEnd_1134587 : Nat := 258928211263492291930949

theorem tailTrace_1134587 : CollatzResearch.WordTrace tailWord_1134587 prefixEnd_1134587 258928211263492291930949 := by
  unfold tailWord_1134587
  simp only [CollatzResearch.WordTrace]
  refine ⟨41381787540592545877730015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27587858360395030585153343 41381787540592545877730015)
  ·
    refine ⟨62072681310888818816595023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41381787540592545877730015 62072681310888818816595023)
    ·
      refine ⟨93109021966333228224892535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62072681310888818816595023 93109021966333228224892535)
      ·
        refine ⟨139663532949499842337338803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93109021966333228224892535 139663532949499842337338803)
        ·
          refine ⟨209495299424249763506008205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139663532949499842337338803 209495299424249763506008205)
          ·
            refine ⟨78560737284093661314753077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209495299424249763506008205 78560737284093661314753077)
            ·
              refine ⟨7365069120383780748258101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78560737284093661314753077 7365069120383780748258101)
              ·
                refine ⟨690475230035979445149197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7365069120383780748258101 690475230035979445149197)
                ·
                  refine ⟨258928211263492291930949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690475230035979445149197 258928211263492291930949)
                  ·
                    rfl

theorem cell21_1134587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 5, 3].length) (baseStart_1134587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134587 prefixEnd_1134587 := by exact prefixLift 1134587
  have htrace : WordTrace (prefixWord ++ tailWord_1134587) baseStart_1134587 baseEnd_1134587 := by
    simpa [prefixWord, tailWord_1134587, baseEnd_1134587] using wordTrace_append hprefix tailTrace_1134587
  have hstable : (prefixWord ++ tailWord_1134587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134587).length < 2 ^ (prefixWord ++ tailWord_1134587).sum := by decide
  have hdescent : baseEnd_1134587 < baseStart_1134587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134649 : List Nat := [1, 2, 1, 5, 4, 1, 7]
def baseStart_1134649 : Nat := 118140960795 + 1134649 * 2 ^ 59
def prefixEnd_1134649 : Nat := 4983230072969 + 3 ^ 40 * 1134649 * 2
def baseEnd_1134649 : Nat := 28771373389799329099721

theorem tailTrace_1134649 : CollatzResearch.WordTrace tailWord_1134649 prefixEnd_1134649 28771373389799329099721 := by
  unfold tailWord_1134649
  simp only [CollatzResearch.WordTrace]
  refine ⟨41384048866367930466487001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27589365910911953644324667 41384048866367930466487001)
  ·
    refine ⟨31038036649775947849865251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41384048866367930466487001 31038036649775947849865251)
    ·
      refine ⟨46557054974663921774797877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31038036649775947849865251 46557054974663921774797877)
      ·
        refine ⟨4364723903874742666387301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46557054974663921774797877 4364723903874742666387301)
        ·
          refine ⟨818385731976514249947619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4364723903874742666387301 818385731976514249947619)
          ·
            refine ⟨1227578597964771374921429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818385731976514249947619 1227578597964771374921429)
            ·
              refine ⟨28771373389799329099721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1227578597964771374921429 28771373389799329099721)
              ·
                rfl

theorem cell21_1134649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 7].length) (baseStart_1134649 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134649 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134649 prefixEnd_1134649 := by exact prefixLift 1134649
  have htrace : WordTrace (prefixWord ++ tailWord_1134649) baseStart_1134649 baseEnd_1134649 := by
    simpa [prefixWord, tailWord_1134649, baseEnd_1134649] using wordTrace_append hprefix tailTrace_1134649
  have hstable : (prefixWord ++ tailWord_1134649).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134649).length < 2 ^ (prefixWord ++ tailWord_1134649).sum := by decide
  have hdescent : baseEnd_1134649 < baseStart_1134649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134691 : List Nat := [1, 1, 1, 5, 1, 1, 4, 7]
def baseStart_1134691 : Nat := 118140960795 + 1134691 * 2 ^ 59
def prefixEnd_1134691 : Nat := 4983230072969 + 3 ^ 40 * 1134691 * 2
def baseEnd_1134691 : Nat := 86317315160137074065801

theorem tailTrace_1134691 : CollatzResearch.WordTrace tailWord_1134691 prefixEnd_1134691 86317315160137074065801 := by
  unfold tailWord_1134691
  simp only [CollatzResearch.WordTrace]
  refine ⟨41385580732215771639515927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27590387154810514426343951 41385580732215771639515927)
  ·
    refine ⟨62078371098323657459273891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41385580732215771639515927 62078371098323657459273891)
    ·
      refine ⟨93117556647485486188910837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62078371098323657459273891 93117556647485486188910837)
      ·
        refine ⟨8729770935701764330210391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93117556647485486188910837 8729770935701764330210391)
        ·
          refine ⟨13094656403552646495315587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8729770935701764330210391 13094656403552646495315587)
          ·
            refine ⟨19641984605328969742973381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13094656403552646495315587 19641984605328969742973381)
            ·
              refine ⟨3682872113499181826807509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19641984605328969742973381 3682872113499181826807509)
              ·
                refine ⟨86317315160137074065801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3682872113499181826807509 86317315160137074065801)
                ·
                  rfl

theorem cell21_1134691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 7].length) (baseStart_1134691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134691 prefixEnd_1134691 := by exact prefixLift 1134691
  have htrace : WordTrace (prefixWord ++ tailWord_1134691) baseStart_1134691 baseEnd_1134691 := by
    simpa [prefixWord, tailWord_1134691, baseEnd_1134691] using wordTrace_append hprefix tailTrace_1134691
  have hstable : (prefixWord ++ tailWord_1134691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134691).length < 2 ^ (prefixWord ++ tailWord_1134691).sum := by decide
  have hdescent : baseEnd_1134691 < baseStart_1134691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134846 : List Nat := [4, 2, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1134846 : Nat := 118140960795 + 1134846 * 2 ^ 59
def prefixEnd_1134846 : Nat := 4983230072969 + 3 ^ 40 * 1134846 * 2
def baseEnd_1134846 : Nat := 258987318592165397113753

theorem tailTrace_1134846 : CollatzResearch.WordTrace tailWord_1134846 prefixEnd_1134846 258987318592165397113753 := by
  unfold tailWord_1134846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173904255831779138926049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27594156031102822074272261 5173904255831779138926049)
  ·
    refine ⟨3880428191873834354194537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5173904255831779138926049 3880428191873834354194537)
    ·
      refine ⟨2910321143905375765645903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3880428191873834354194537 2910321143905375765645903)
      ·
        refine ⟨4365481715858063648468855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910321143905375765645903 4365481715858063648468855)
        ·
          refine ⟨6548222573787095472703283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365481715858063648468855 6548222573787095472703283)
          ·
            refine ⟨9822333860680643209054925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6548222573787095472703283 9822333860680643209054925)
            ·
              refine ⟨3683375197755241203395597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9822333860680643209054925 3683375197755241203395597)
              ·
                refine ⟨1381265699158215451273349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3683375197755241203395597 1381265699158215451273349)
                ·
                  refine ⟨258987318592165397113753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1381265699158215451273349 258987318592165397113753)
                  ·
                    rfl

theorem cell21_1134846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1134846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134846 prefixEnd_1134846 := by exact prefixLift 1134846
  have htrace : WordTrace (prefixWord ++ tailWord_1134846) baseStart_1134846 baseEnd_1134846 := by
    simpa [prefixWord, tailWord_1134846, baseEnd_1134846] using wordTrace_append hprefix tailTrace_1134846
  have hstable : (prefixWord ++ tailWord_1134846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134846).length < 2 ^ (prefixWord ++ tailWord_1134846).sum := by decide
  have hdescent : baseEnd_1134846 < baseStart_1134846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1134894 : List Nat := [4, 1, 3, 3, 1, 2, 1, 6]
def baseStart_1134894 : Nat := 118140960795 + 1134894 * 2 ^ 59
def prefixEnd_1134894 : Nat := 4983230072969 + 3 ^ 40 * 1134894 * 2
def baseEnd_1134894 : Nat := 86332757615375993437885

theorem tailTrace_1134894 : CollatzResearch.WordTrace tailWord_1134894 prefixEnd_1134894 86332757615375993437885 := by
  unfold tailWord_1134894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174123093810042163644467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27595323166986891539437157 5174123093810042163644467)
  ·
    refine ⟨7761184640715063245466701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174123093810042163644467 7761184640715063245466701)
    ·
      refine ⟨2910444240268148717050013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7761184640715063245466701 2910444240268148717050013)
      ·
        refine ⟨1091416590100555768893755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2910444240268148717050013 1091416590100555768893755)
        ·
          refine ⟨1637124885150833653340633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1091416590100555768893755 1637124885150833653340633)
          ·
            refine ⟨1227843663863125240005475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637124885150833653340633 1227843663863125240005475)
            ·
              refine ⟨1841765495794687860008213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1227843663863125240005475 1841765495794687860008213)
              ·
                refine ⟨86332757615375993437885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1841765495794687860008213 86332757615375993437885)
                ·
                  rfl

theorem cell21_1134894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_1134894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1134894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1134894 prefixEnd_1134894 := by exact prefixLift 1134894
  have htrace : WordTrace (prefixWord ++ tailWord_1134894) baseStart_1134894 baseEnd_1134894 := by
    simpa [prefixWord, tailWord_1134894, baseEnd_1134894] using wordTrace_append hprefix tailTrace_1134894
  have hstable : (prefixWord ++ tailWord_1134894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1134894).length < 2 ^ (prefixWord ++ tailWord_1134894).sum := by decide
  have hdescent : baseEnd_1134894 < baseStart_1134894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1134894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135015 : List Nat := [1, 1, 6, 1, 1, 4, 2, 1, 4]
def baseStart_1135015 : Nat := 118140960795 + 1135015 * 2 ^ 59
def prefixEnd_1135015 : Nat := 4983230072969 + 3 ^ 40 * 1135015 * 2
def baseEnd_1135015 : Nat := 259025886694658658796741

theorem tailTrace_1135015 : CollatzResearch.WordTrace tailWord_1135015 prefixEnd_1135015 259025886694658658796741 := by
  unfold tailWord_1135015
  simp only [CollatzResearch.WordTrace]
  refine ⟨41397397983041974974310499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27598265322027983316206999 41397397983041974974310499)
  ·
    refine ⟨62096096974562962461465749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41397397983041974974310499 62096096974562962461465749)
    ·
      refine ⟨2910754545682638865381207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62096096974562962461465749 2910754545682638865381207)
      ·
        refine ⟨4366131818523958298071811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910754545682638865381207 4366131818523958298071811)
        ·
          refine ⟨6549197727785937447107717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4366131818523958298071811 6549197727785937447107717)
          ·
            refine ⟨1227974573959863271332697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6549197727785937447107717 1227974573959863271332697)
            ·
              refine ⟨920980930469897453499523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227974573959863271332697 920980930469897453499523)
              ·
                refine ⟨1381471395704846180249285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 920980930469897453499523 1381471395704846180249285)
                ·
                  refine ⟨259025886694658658796741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1381471395704846180249285 259025886694658658796741)
                  ·
                    rfl

theorem cell21_1135015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 1, 4].length) (baseStart_1135015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135015 prefixEnd_1135015 := by exact prefixLift 1135015
  have htrace : WordTrace (prefixWord ++ tailWord_1135015) baseStart_1135015 baseEnd_1135015 := by
    simpa [prefixWord, tailWord_1135015, baseEnd_1135015] using wordTrace_append hprefix tailTrace_1135015
  have hstable : (prefixWord ++ tailWord_1135015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135015).length < 2 ^ (prefixWord ++ tailWord_1135015).sum := by decide
  have hdescent : baseEnd_1135015 < baseStart_1135015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135060 : List Nat := [2, 4, 1, 2, 2, 2, 1, 4, 3]
def baseStart_1135060 : Nat := 118140960795 + 1135060 * 2 ^ 59
def prefixEnd_1135060 : Nat := 4983230072969 + 3 ^ 40 * 1135060 * 2
def baseEnd_1135060 : Nat := 259036156307748580546649

theorem tailTrace_1135060 : CollatzResearch.WordTrace tailWord_1135060 prefixEnd_1135060 259036156307748580546649 := by
  unfold tailWord_1135060
  simp only [CollatzResearch.WordTrace]
  refine ⟨20699519633939473829849317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27599359511919298439799089 20699519633939473829849317)
  ·
    refine ⟨3881159931363651343096747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20699519633939473829849317 3881159931363651343096747)
    ·
      refine ⟨5821739897045477014645121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3881159931363651343096747 5821739897045477014645121)
      ·
        refine ⟨4366304922784107760983841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5821739897045477014645121 4366304922784107760983841)
        ·
          refine ⟨3274728692088080820737881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4366304922784107760983841 3274728692088080820737881)
          ·
            refine ⟨2456046519066060615553411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274728692088080820737881 2456046519066060615553411)
            ·
              refine ⟨3684069778599090923330117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456046519066060615553411 3684069778599090923330117)
              ·
                refine ⟨690763083487329548124397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3684069778599090923330117 690763083487329548124397)
                ·
                  refine ⟨259036156307748580546649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690763083487329548124397 259036156307748580546649)
                  ·
                    rfl

theorem cell21_1135060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_1135060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135060 prefixEnd_1135060 := by exact prefixLift 1135060
  have htrace : WordTrace (prefixWord ++ tailWord_1135060) baseStart_1135060 baseEnd_1135060 := by
    simpa [prefixWord, tailWord_1135060, baseEnd_1135060] using wordTrace_append hprefix tailTrace_1135060
  have hstable : (prefixWord ++ tailWord_1135060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135060).length < 2 ^ (prefixWord ++ tailWord_1135060).sum := by decide
  have hdescent : baseEnd_1135060 < baseStart_1135060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135071 : List Nat := [1, 1, 2, 3, 3, 2, 3, 6]
def baseStart_1135071 : Nat := 118140960795 + 1135071 * 2 ^ 59
def prefixEnd_1135071 : Nat := 4983230072969 + 3 ^ 40 * 1135071 * 2
def baseEnd_1135071 : Nat := 86346222219205001954431

theorem tailTrace_1135071 : CollatzResearch.WordTrace tailWord_1135071 prefixEnd_1135071 86346222219205001954431 := by
  unfold tailWord_1135071
  simp only [CollatzResearch.WordTrace]
  refine ⟨41399440470839096538349067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27599626980559397692232711 41399440470839096538349067)
  ·
    refine ⟨62099160706258644807523601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41399440470839096538349067 62099160706258644807523601)
    ·
      refine ⟨46574370529693983605642701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62099160706258644807523601 46574370529693983605642701)
      ·
        refine ⟨17465388948635243852116013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46574370529693983605642701 17465388948635243852116013)
        ·
          refine ⟨6549520855738216444543505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17465388948635243852116013 6549520855738216444543505)
          ·
            refine ⟨4912140641803662333407629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6549520855738216444543505 4912140641803662333407629)
            ·
              refine ⟨1842052740676373375027861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4912140641803662333407629 1842052740676373375027861)
              ·
                refine ⟨86346222219205001954431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1842052740676373375027861 86346222219205001954431)
                ·
                  rfl

theorem cell21_1135071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 6].length) (baseStart_1135071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135071 prefixEnd_1135071 := by exact prefixLift 1135071
  have htrace : WordTrace (prefixWord ++ tailWord_1135071) baseStart_1135071 baseEnd_1135071 := by
    simpa [prefixWord, tailWord_1135071, baseEnd_1135071] using wordTrace_append hprefix tailTrace_1135071
  have hstable : (prefixWord ++ tailWord_1135071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135071).length < 2 ^ (prefixWord ++ tailWord_1135071).sum := by decide
  have hdescent : baseEnd_1135071 < baseStart_1135071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135178 : List Nat := [3, 1, 2, 1, 1, 4, 3, 1, 5]
def baseStart_1135178 : Nat := 118140960795 + 1135178 * 2 ^ 59
def prefixEnd_1135178 : Nat := 4983230072969 + 3 ^ 40 * 1135178 * 2
def baseEnd_1135178 : Nat := 259063085515406597579741

theorem tailTrace_1135178 : CollatzResearch.WordTrace tailWord_1135178 prefixEnd_1135178 259063085515406597579741 := by
  unfold tailWord_1135178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350835770362863453123547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27602228720967635874996125 10350835770362863453123547)
  ·
    refine ⟨15526253655544295179685321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10350835770362863453123547 15526253655544295179685321)
    ·
      refine ⟨11644690241658221384763991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15526253655544295179685321 11644690241658221384763991)
      ·
        refine ⟨17467035362487332077145987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11644690241658221384763991 17467035362487332077145987)
        ·
          refine ⟨26200553043730998115718981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17467035362487332077145987 26200553043730998115718981)
          ·
            refine ⟨4912603695699562146697309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26200553043730998115718981 4912603695699562146697309)
            ·
              refine ⟨1842226385887335805011491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4912603695699562146697309 1842226385887335805011491)
              ·
                refine ⟨2763339578831003707517237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842226385887335805011491 2763339578831003707517237)
                ·
                  refine ⟨259063085515406597579741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2763339578831003707517237 259063085515406597579741)
                  ·
                    rfl

theorem cell21_1135178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_1135178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135178 prefixEnd_1135178 := by exact prefixLift 1135178
  have htrace : WordTrace (prefixWord ++ tailWord_1135178) baseStart_1135178 baseEnd_1135178 := by
    simpa [prefixWord, tailWord_1135178, baseEnd_1135178] using wordTrace_append hprefix tailTrace_1135178
  have hstable : (prefixWord ++ tailWord_1135178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135178).length < 2 ^ (prefixWord ++ tailWord_1135178).sum := by decide
  have hdescent : baseEnd_1135178 < baseStart_1135178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135229 : List Nat := [1, 4, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1135229 : Nat := 118140960795 + 1135229 * 2 ^ 59
def prefixEnd_1135229 : Nat := 4983230072969 + 3 ^ 40 * 1135229 * 2
def baseEnd_1135229 : Nat := 259074724410241842229637

theorem tailTrace_1135229 : CollatzResearch.WordTrace tailWord_1135229 prefixEnd_1135229 259074724410241842229637 := by
  unfold tailWord_1135229
  simp only [CollatzResearch.WordTrace]
  refine ⟨41405203204266689522600741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27603468802844459681733827 41405203204266689522600741)
  ·
    refine ⟨7763475600800004285487639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41405203204266689522600741 7763475600800004285487639)
    ·
      refine ⟨11645213401200006428231459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7763475600800004285487639 11645213401200006428231459)
      ·
        refine ⟨17467820101800009642347189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11645213401200006428231459 17467820101800009642347189)
        ·
          refine ⟨1637608134543750903970049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17467820101800009642347189 1637608134543750903970049)
          ·
            refine ⟨1228206100907813177977537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1637608134543750903970049 1228206100907813177977537)
            ·
              refine ⟨921154575680859883483153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1228206100907813177977537 921154575680859883483153)
              ·
                refine ⟨690865931760644912612365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921154575680859883483153 690865931760644912612365)
                ·
                  refine ⟨259074724410241842229637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 690865931760644912612365 259074724410241842229637)
                  ·
                    rfl

theorem cell21_1135229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1135229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135229 prefixEnd_1135229 := by exact prefixLift 1135229
  have htrace : WordTrace (prefixWord ++ tailWord_1135229) baseStart_1135229 baseEnd_1135229 := by
    simpa [prefixWord, tailWord_1135229, baseEnd_1135229] using wordTrace_append hprefix tailTrace_1135229
  have hstable : (prefixWord ++ tailWord_1135229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135229).length < 2 ^ (prefixWord ++ tailWord_1135229).sum := by decide
  have hdescent : baseEnd_1135229 < baseStart_1135229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135268 : List Nat := [2, 3, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1135268 : Nat := 118140960795 + 1135268 * 2 ^ 59
def prefixEnd_1135268 : Nat := 4983230072969 + 3 ^ 40 * 1135268 * 2
def baseEnd_1135268 : Nat := 259083624741586441079557

theorem tailTrace_1135268 : CollatzResearch.WordTrace tailWord_1135268 prefixEnd_1135268 259083624741586441079557 := by
  unfold tailWord_1135268
  simp only [CollatzResearch.WordTrace]
  refine ⟨20703312825562699591635229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27604417100750266122180305 20703312825562699591635229)
  ·
    refine ⟨7763742309586012346863211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20703312825562699591635229 7763742309586012346863211)
    ·
      refine ⟨11645613464379018520294817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7763742309586012346863211 11645613464379018520294817)
      ·
        refine ⟨8734210098284263890221113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11645613464379018520294817 8734210098284263890221113)
        ·
          refine ⟨6550657573713197917665835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8734210098284263890221113 6550657573713197917665835)
          ·
            refine ⟨9825986360569796876498753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550657573713197917665835 9825986360569796876498753)
            ·
              refine ⟨7369489770427347657374065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9825986360569796876498753 7369489770427347657374065)
              ·
                refine ⟨5527117327820510743030549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7369489770427347657374065 5527117327820510743030549)
                ·
                  refine ⟨259083624741586441079557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5527117327820510743030549 259083624741586441079557)
                  ·
                    rfl

theorem cell21_1135268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1135268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135268 prefixEnd_1135268 := by exact prefixLift 1135268
  have htrace : WordTrace (prefixWord ++ tailWord_1135268) baseStart_1135268 baseEnd_1135268 := by
    simpa [prefixWord, tailWord_1135268, baseEnd_1135268] using wordTrace_append hprefix tailTrace_1135268
  have hstable : (prefixWord ++ tailWord_1135268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135268).length < 2 ^ (prefixWord ++ tailWord_1135268).sum := by decide
  have hdescent : baseEnd_1135268 < baseStart_1135268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135285 : List Nat := [1, 3, 3, 3, 1, 2, 1, 1, 6]
def baseStart_1135285 : Nat := 118140960795 + 1135285 * 2 ^ 59
def prefixEnd_1135285 : Nat := 4983230072969 + 3 ^ 40 * 1135285 * 2
def baseEnd_1135285 : Nat := 259087504373198189296189

theorem tailTrace_1135285 : CollatzResearch.WordTrace tailWord_1135285 prefixEnd_1135285 259087504373198189296189 := by
  unfold tailWord_1135285
  simp only [CollatzResearch.WordTrace]
  refine ⟨41407245692063811086639309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27604830461375874057759539 41407245692063811086639309)
  ·
    refine ⟨15527717134523929157489741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41407245692063811086639309 15527717134523929157489741)
    ·
      refine ⟨5822893925446473434058653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15527717134523929157489741 5822893925446473434058653)
      ·
        refine ⟨2183585222042427537771995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5822893925446473434058653 2183585222042427537771995)
        ·
          refine ⟨3275377833063641306657993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183585222042427537771995 3275377833063641306657993)
          ·
            refine ⟨2456533374797730979993495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275377833063641306657993 2456533374797730979993495)
            ·
              refine ⟨3684800062196596469990243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456533374797730979993495 3684800062196596469990243)
              ·
                refine ⟨5527200093294894704985365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684800062196596469990243 5527200093294894704985365)
                ·
                  refine ⟨259087504373198189296189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5527200093294894704985365 259087504373198189296189)
                  ·
                    rfl

theorem cell21_1135285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_1135285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135285 prefixEnd_1135285 := by exact prefixLift 1135285
  have htrace : WordTrace (prefixWord ++ tailWord_1135285) baseStart_1135285 baseEnd_1135285 := by
    simpa [prefixWord, tailWord_1135285, baseEnd_1135285] using wordTrace_append hprefix tailTrace_1135285
  have hstable : (prefixWord ++ tailWord_1135285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135285).length < 2 ^ (prefixWord ++ tailWord_1135285).sum := by decide
  have hdescent : baseEnd_1135285 < baseStart_1135285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135313 : List Nat := [1, 2, 2, 1, 2, 3, 1, 4, 5]
def baseStart_1135313 : Nat := 118140960795 + 1135313 * 2 ^ 59
def prefixEnd_1135313 : Nat := 4983230072969 + 3 ^ 40 * 1135313 * 2
def baseEnd_1135313 : Nat := 259093894354676362829465

theorem tailTrace_1135313 : CollatzResearch.WordTrace tailWord_1135313 prefixEnd_1135313 259093894354676362829465 := by
  unfold tailWord_1135313
  simp only [CollatzResearch.WordTrace]
  refine ⟨41408266935962371868658593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27605511290641581245772395 41408266935962371868658593)
  ·
    refine ⟨31056200201971778901493945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41408266935962371868658593 31056200201971778901493945)
    ·
      refine ⟨23292150151478834176120459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31056200201971778901493945 23292150151478834176120459)
      ·
        refine ⟨34938225227218251264180689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23292150151478834176120459 34938225227218251264180689)
        ·
          refine ⟨26203668920413688448135517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34938225227218251264180689 26203668920413688448135517)
          ·
            refine ⟨9826375845155133168050819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26203668920413688448135517 9826375845155133168050819)
            ·
              refine ⟨14739563767732699752076229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9826375845155133168050819 14739563767732699752076229)
              ·
                refine ⟨2763668206449881203514293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14739563767732699752076229 2763668206449881203514293)
                ·
                  refine ⟨259093894354676362829465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2763668206449881203514293 259093894354676362829465)
                  ·
                    rfl

theorem cell21_1135313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_1135313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135313 prefixEnd_1135313 := by exact prefixLift 1135313
  have htrace : WordTrace (prefixWord ++ tailWord_1135313) baseStart_1135313 baseEnd_1135313 := by
    simpa [prefixWord, tailWord_1135313, baseEnd_1135313] using wordTrace_append hprefix tailTrace_1135313
  have hstable : (prefixWord ++ tailWord_1135313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135313).length < 2 ^ (prefixWord ++ tailWord_1135313).sum := by decide
  have hdescent : baseEnd_1135313 < baseStart_1135313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135316 : List Nat := [2, 4, 1, 3, 2, 1, 1, 7]
def baseStart_1135316 : Nat := 118140960795 + 1135316 * 2 ^ 59
def prefixEnd_1135316 : Nat := 4983230072969 + 3 ^ 40 * 1135316 * 2
def baseEnd_1135316 : Nat := 86364859665183008093153

theorem tailTrace_1135316 : CollatzResearch.WordTrace tailWord_1135316 prefixEnd_1135316 86364859665183008093153 := by
  unfold tailWord_1135316
  simp only [CollatzResearch.WordTrace]
  refine ⟨20704188177475751690508901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27605584236634335587345201 20704188177475751690508901)
  ·
    refine ⟨3882035283276703441970419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20704188177475751690508901 3882035283276703441970419)
    ·
      refine ⟨5823052924915055162955629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3882035283276703441970419 5823052924915055162955629)
      ·
        refine ⟨2183644846843145686108361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5823052924915055162955629 2183644846843145686108361)
        ·
          refine ⟨1637733635132359264581271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2183644846843145686108361 1637733635132359264581271)
          ·
            refine ⟨2456600452698538896871907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637733635132359264581271 2456600452698538896871907)
            ·
              refine ⟨3684900679047808345307861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456600452698538896871907 3684900679047808345307861)
              ·
                refine ⟨86364859665183008093153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3684900679047808345307861 86364859665183008093153)
                ·
                  rfl

theorem cell21_1135316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 7].length) (baseStart_1135316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135316 prefixEnd_1135316 := by exact prefixLift 1135316
  have htrace : WordTrace (prefixWord ++ tailWord_1135316) baseStart_1135316 baseEnd_1135316 := by
    simpa [prefixWord, tailWord_1135316, baseEnd_1135316] using wordTrace_append hprefix tailTrace_1135316
  have hstable : (prefixWord ++ tailWord_1135316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135316).length < 2 ^ (prefixWord ++ tailWord_1135316).sum := by decide
  have hdescent : baseEnd_1135316 < baseStart_1135316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135344 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 4]
def baseStart_1135344 : Nat := 118140960795 + 1135344 * 2 ^ 59
def prefixEnd_1135344 : Nat := 4983230072969 + 3 ^ 40 * 1135344 * 2
def baseEnd_1135344 : Nat := 259100968977027197812735

theorem tailTrace_1135344 : CollatzResearch.WordTrace tailWord_1135344 prefixEnd_1135344 259100968977027197812735 := by
  unfold tailWord_1135344
  simp only [CollatzResearch.WordTrace]
  refine ⟨20704698799425032081518543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27606265065900042775358057 20704698799425032081518543)
  ·
    refine ⟨31057048199137548122277815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20704698799425032081518543 31057048199137548122277815)
    ·
      refine ⟨46585572298706322183416723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31057048199137548122277815 46585572298706322183416723)
      ·
        refine ⟨69878358448059483275125085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46585572298706322183416723 69878358448059483275125085)
        ·
          refine ⟨26204384418022306228171907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69878358448059483275125085 26204384418022306228171907)
          ·
            refine ⟨39306576627033459342257861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26204384418022306228171907 39306576627033459342257861)
            ·
              refine ⟨7369983117568773626673349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39306576627033459342257861 7369983117568773626673349)
              ·
                refine ⟨1381871834544145055001253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7369983117568773626673349 1381871834544145055001253)
                ·
                  refine ⟨259100968977027197812735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1381871834544145055001253 259100968977027197812735)
                  ·
                    rfl

theorem cell21_1135344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 4].length) (baseStart_1135344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135344 prefixEnd_1135344 := by exact prefixLift 1135344
  have htrace : WordTrace (prefixWord ++ tailWord_1135344) baseStart_1135344 baseEnd_1135344 := by
    simpa [prefixWord, tailWord_1135344, baseEnd_1135344] using wordTrace_append hprefix tailTrace_1135344
  have hstable : (prefixWord ++ tailWord_1135344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135344).length < 2 ^ (prefixWord ++ tailWord_1135344).sum := by decide
  have hdescent : baseEnd_1135344 < baseStart_1135344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135496 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 6]
def baseStart_1135496 : Nat := 118140960795 + 1135496 * 2 ^ 59
def prefixEnd_1135496 : Nat := 4983230072969 + 3 ^ 40 * 1135496 * 2
def baseEnd_1135496 : Nat := 259135657447908711279091

theorem tailTrace_1135496 : CollatzResearch.WordTrace tailWord_1135496 prefixEnd_1135496 259135657447908711279091 := by
  unfold tailWord_1135496
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707470747149697061285171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27609960996199596081713561 20707470747149697061285171)
  ·
    refine ⟨31061206120724545591927757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20707470747149697061285171 31061206120724545591927757)
    ·
      refine ⟨11647952295271704596972909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31061206120724545591927757 11647952295271704596972909)
      ·
        refine ⟨4367982110726889223864841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11647952295271704596972909 4367982110726889223864841)
        ·
          refine ⟨3275986583045166917898631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4367982110726889223864841 3275986583045166917898631)
          ·
            refine ⟨4913979874567750376847947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3275986583045166917898631 4913979874567750376847947)
            ·
              refine ⟨7370969811851625565271921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4913979874567750376847947 7370969811851625565271921)
              ·
                refine ⟨5528227358888719173953941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7370969811851625565271921 5528227358888719173953941)
                ·
                  refine ⟨259135657447908711279091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5528227358888719173953941 259135657447908711279091)
                  ·
                    rfl

theorem cell21_1135496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_1135496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135496 prefixEnd_1135496 := by exact prefixLift 1135496
  have htrace : WordTrace (prefixWord ++ tailWord_1135496) baseStart_1135496 baseEnd_1135496 := by
    simpa [prefixWord, tailWord_1135496, baseEnd_1135496] using wordTrace_append hprefix tailTrace_1135496
  have hstable : (prefixWord ++ tailWord_1135496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135496).length < 2 ^ (prefixWord ++ tailWord_1135496).sum := by decide
  have hdescent : baseEnd_1135496 < baseStart_1135496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135516 : List Nat := [2, 2, 3, 3, 3, 1, 1, 1, 5]
def baseStart_1135516 : Nat := 118140960795 + 1135516 * 2 ^ 59
def prefixEnd_1135516 : Nat := 4983230072969 + 3 ^ 40 * 1135516 * 2
def baseEnd_1135516 : Nat := 259140221720393120945717

theorem tailTrace_1135516 : CollatzResearch.WordTrace tailWord_1135516 prefixEnd_1135516 259140221720393120945717 := by
  unfold tailWord_1135516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20707835477113468769149201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27610447302817958358865601 20707835477113468769149201)
  ·
    refine ⟨15530876607835101576861901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20707835477113468769149201 15530876607835101576861901)
    ·
      refine ⟨5824078727938163091323213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15530876607835101576861901 5824078727938163091323213)
      ·
        refine ⟨2184029522976811159246205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5824078727938163091323213 2184029522976811159246205)
        ·
          refine ⟨819011071116304184717327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2184029522976811159246205 819011071116304184717327)
          ·
            refine ⟨1228516606674456277075991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819011071116304184717327 1228516606674456277075991)
            ·
              refine ⟨1842774910011684415613987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228516606674456277075991 1842774910011684415613987)
              ·
                refine ⟨2764162365017526623420981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842774910011684415613987 2764162365017526623420981)
                ·
                  refine ⟨259140221720393120945717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2764162365017526623420981 259140221720393120945717)
                  ·
                    rfl

theorem cell21_1135516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_1135516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135516 prefixEnd_1135516 := by exact prefixLift 1135516
  have htrace : WordTrace (prefixWord ++ tailWord_1135516) baseStart_1135516 baseEnd_1135516 := by
    simpa [prefixWord, tailWord_1135516, baseEnd_1135516] using wordTrace_append hprefix tailTrace_1135516
  have hstable : (prefixWord ++ tailWord_1135516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135516).length < 2 ^ (prefixWord ++ tailWord_1135516).sum := by decide
  have hdescent : baseEnd_1135516 < baseStart_1135516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135541 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 7]
def baseStart_1135541 : Nat := 118140960795 + 1135541 * 2 ^ 59
def prefixEnd_1135541 : Nat := 4983230072969 + 3 ^ 40 * 1135541 * 2
def baseEnd_1135541 : Nat := 259145927060998633028999

theorem tailTrace_1135541 : CollatzResearch.WordTrace tailWord_1135541 prefixEnd_1135541 259145927060998633028999 := by
  unfold tailWord_1135541
  simp only [CollatzResearch.WordTrace]
  refine ⟨41416582779136366807958477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27611055186090911205305651 41416582779136366807958477)
  ·
    refine ⟨15531218542176137552984429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41416582779136366807958477 15531218542176137552984429)
    ·
      refine ⟨5824206953316051582369161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15531218542176137552984429 5824206953316051582369161)
      ·
        refine ⟨4368155214987038686776871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5824206953316051582369161 4368155214987038686776871)
        ·
          refine ⟨6552232822480558030165307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368155214987038686776871 6552232822480558030165307)
          ·
            refine ⟨9828349233720837045247961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6552232822480558030165307 9828349233720837045247961)
            ·
              refine ⟨7371261925290627783935971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9828349233720837045247961 7371261925290627783935971)
              ·
                refine ⟨11056892887935941675903957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7371261925290627783935971 11056892887935941675903957)
                ·
                  refine ⟨259145927060998633028999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11056892887935941675903957 259145927060998633028999)
                  ·
                    rfl

theorem cell21_1135541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_1135541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135541 prefixEnd_1135541 := by exact prefixLift 1135541
  have htrace : WordTrace (prefixWord ++ tailWord_1135541) baseStart_1135541 baseEnd_1135541 := by
    simpa [prefixWord, tailWord_1135541, baseEnd_1135541] using wordTrace_append hprefix tailTrace_1135541
  have hstable : (prefixWord ++ tailWord_1135541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135541).length < 2 ^ (prefixWord ++ tailWord_1135541).sum := by decide
  have hdescent : baseEnd_1135541 < baseStart_1135541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135668 : List Nat := [2, 5, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1135668 : Nat := 118140960795 + 1135668 * 2 ^ 59
def prefixEnd_1135668 : Nat := 4983230072969 + 3 ^ 40 * 1135668 * 2
def baseEnd_1135668 : Nat := 259174910191274634412073

theorem tailTrace_1135668 : CollatzResearch.WordTrace tailWord_1135668 prefixEnd_1135668 259174910191274634412073 := by
  unfold tailWord_1135668
  simp only [CollatzResearch.WordTrace]
  refine ⟨20710607424838133748915829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27614143233117511665221105 20710607424838133748915829)
  ·
    refine ⟨1941619446078575038960859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20710607424838133748915829 1941619446078575038960859)
    ·
      refine ⟨2912429169117862558441289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1941619446078575038960859 2912429169117862558441289)
      ·
        refine ⟨2184321876838396918830967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912429169117862558441289 2184321876838396918830967)
        ·
          refine ⟨3276482815257595378246451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2184321876838396918830967 3276482815257595378246451)
          ·
            refine ⟨4914724222886393067369677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3276482815257595378246451 4914724222886393067369677)
            ·
              refine ⟨1843021583582397400263629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4914724222886393067369677 1843021583582397400263629)
              ·
                refine ⟨691133093843399025098861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1843021583582397400263629 691133093843399025098861)
                ·
                  refine ⟨259174910191274634412073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691133093843399025098861 259174910191274634412073)
                  ·
                    rfl

theorem cell21_1135668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1135668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135668 prefixEnd_1135668 := by exact prefixLift 1135668
  have htrace : WordTrace (prefixWord ++ tailWord_1135668) baseStart_1135668 baseEnd_1135668 := by
    simpa [prefixWord, tailWord_1135668, baseEnd_1135668] using wordTrace_append hprefix tailTrace_1135668
  have hstable : (prefixWord ++ tailWord_1135668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135668).length < 2 ^ (prefixWord ++ tailWord_1135668).sum := by decide
  have hdescent : baseEnd_1135668 < baseStart_1135668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135837 : List Nat := [1, 4, 3, 2, 3, 1, 1, 3, 3]
def baseStart_1135837 : Nat := 118140960795 + 1135837 * 2 ^ 59
def prefixEnd_1135837 : Nat := 4983230072969 + 3 ^ 40 * 1135837 * 2
def baseEnd_1135837 : Nat := 259213478293767896095061

theorem tailTrace_1135837 : CollatzResearch.WordTrace tailWord_1135837 prefixEnd_1135837 259213478293767896095061 := by
  unfold tailWord_1135837
  simp only [CollatzResearch.WordTrace]
  refine ⟨41427378786064009360733765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27618252524042672907155843 41427378786064009360733765)
  ·
    refine ⟨7767633522387001755137581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41427378786064009360733765 7767633522387001755137581)
    ·
      refine ⟨2912862570895125658176593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7767633522387001755137581 2912862570895125658176593)
      ·
        refine ⟨2184646928171344243632445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2912862570895125658176593 2184646928171344243632445)
        ·
          refine ⟨819242598064254091362167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2184646928171344243632445 819242598064254091362167)
          ·
            refine ⟨1228863897096381137043251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819242598064254091362167 1228863897096381137043251)
            ·
              refine ⟨1843295845644571705564877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228863897096381137043251 1843295845644571705564877)
              ·
                refine ⟨691235942116714389586829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1843295845644571705564877 691235942116714389586829)
                ·
                  refine ⟨259213478293767896095061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691235942116714389586829 259213478293767896095061)
                  ·
                    rfl

theorem cell21_1135837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_1135837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135837 prefixEnd_1135837 := by exact prefixLift 1135837
  have htrace : WordTrace (prefixWord ++ tailWord_1135837) baseStart_1135837 baseEnd_1135837 := by
    simpa [prefixWord, tailWord_1135837, baseEnd_1135837] using wordTrace_append hprefix tailTrace_1135837
  have hstable : (prefixWord ++ tailWord_1135837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135837).length < 2 ^ (prefixWord ++ tailWord_1135837).sum := by decide
  have hdescent : baseEnd_1135837 < baseStart_1135837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1135859 : List Nat := [1, 1, 1, 2, 2, 5, 2, 1, 6]
def baseStart_1135859 : Nat := 118140960795 + 1135859 * 2 ^ 59
def prefixEnd_1135859 : Nat := 4983230072969 + 3 ^ 40 * 1135859 * 2
def baseEnd_1135859 : Nat := 259218498993500746728349

theorem tailTrace_1135859 : CollatzResearch.WordTrace tailWord_1135859 prefixEnd_1135859 259218498993500746728349 := by
  unfold tailWord_1135859
  simp only [CollatzResearch.WordTrace]
  refine ⟨41428181191984307118034631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27618787461322871412023087 41428181191984307118034631)
  ·
    refine ⟨62142271787976460677051947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41428181191984307118034631 62142271787976460677051947)
    ·
      refine ⟨93213407681964691015577921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62142271787976460677051947 93213407681964691015577921)
      ·
        refine ⟨69910055761473518261683441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93213407681964691015577921 69910055761473518261683441)
        ·
          refine ⟨52432541821105138696262581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69910055761473518261683441 52432541821105138696262581)
          ·
            refine ⟨4915550795728606752774617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52432541821105138696262581 4915550795728606752774617)
            ·
              refine ⟨3686663096796455064580963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4915550795728606752774617 3686663096796455064580963)
              ·
                refine ⟨5529994645194682596871445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3686663096796455064580963 5529994645194682596871445)
                ·
                  refine ⟨259218498993500746728349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5529994645194682596871445 259218498993500746728349)
                  ·
                    rfl

theorem cell21_1135859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_1135859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1135859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1135859 prefixEnd_1135859 := by exact prefixLift 1135859
  have htrace : WordTrace (prefixWord ++ tailWord_1135859) baseStart_1135859 baseEnd_1135859 := by
    simpa [prefixWord, tailWord_1135859, baseEnd_1135859] using wordTrace_append hprefix tailTrace_1135859
  have hstable : (prefixWord ++ tailWord_1135859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1135859).length < 2 ^ (prefixWord ++ tailWord_1135859).sum := by decide
  have hdescent : baseEnd_1135859 < baseStart_1135859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1135859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136025 : List Nat := [1, 2, 1, 2, 1, 5, 9]
def baseStart_1136025 : Nat := 118140960795 + 1136025 * 2 ^ 59
def prefixEnd_1136025 : Nat := 4983230072969 + 3 ^ 40 * 1136025 * 2
def baseEnd_1136025 : Nat := 28806264717235705217927

theorem tailTrace_1136025 : CollatzResearch.WordTrace tailWord_1136025 prefixEnd_1136025 28806264717235705217927 := by
  unfold tailWord_1136025
  simp only [CollatzResearch.WordTrace]
  refine ⟨41434235709382917468577529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27622823806255278312385019 41434235709382917468577529)
  ·
    refine ⟨31075676782037188101433147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41434235709382917468577529 31075676782037188101433147)
    ·
      refine ⟨46613515173055782152149721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31075676782037188101433147 46613515173055782152149721)
      ·
        refine ⟨34960136379791836614112291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46613515173055782152149721 34960136379791836614112291)
        ·
          refine ⟨52440204569687754921168437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34960136379791836614112291 52440204569687754921168437)
          ·
            refine ⟨4916269178408227023859541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52440204569687754921168437 4916269178408227023859541)
            ·
              refine ⟨28806264717235705217927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4916269178408227023859541 28806264717235705217927)
              ·
                rfl

theorem cell21_1136025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 9].length) (baseStart_1136025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136025 prefixEnd_1136025 := by exact prefixLift 1136025
  have htrace : WordTrace (prefixWord ++ tailWord_1136025) baseStart_1136025 baseEnd_1136025 := by
    simpa [prefixWord, tailWord_1136025, baseEnd_1136025] using wordTrace_append hprefix tailTrace_1136025
  have hstable : (prefixWord ++ tailWord_1136025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136025).length < 2 ^ (prefixWord ++ tailWord_1136025).sum := by decide
  have hdescent : baseEnd_1136025 < baseStart_1136025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136031 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 3]
def baseStart_1136031 : Nat := 118140960795 + 1136031 * 2 ^ 59
def prefixEnd_1136031 : Nat := 4983230072969 + 3 ^ 40 * 1136031 * 2
def baseEnd_1136031 : Nat := 259257751736866669861331

theorem tailTrace_1136031 : CollatzResearch.WordTrace tailWord_1136031 prefixEnd_1136031 259257751736866669861331 := by
  unfold tailWord_1136031
  simp only [CollatzResearch.WordTrace]
  refine ⟨41434454547361180493295947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27622969698240786995530631 41434454547361180493295947)
  ·
    refine ⟨62151681821041770739943921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41434454547361180493295947 62151681821041770739943921)
    ·
      refine ⟨46613761365781328054957941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62151681821041770739943921 46613761365781328054957941)
      ·
        refine ⟨4370040128041999505152307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46613761365781328054957941 4370040128041999505152307)
        ·
          refine ⟨6555060192062999257728461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370040128041999505152307 6555060192062999257728461)
          ·
            refine ⟨2458147572023624721648173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6555060192062999257728461 2458147572023624721648173)
            ·
              refine ⟨921805339508859270618065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2458147572023624721648173 921805339508859270618065)
              ·
                refine ⟨691354004631644452963549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 921805339508859270618065 691354004631644452963549)
                ·
                  refine ⟨259257751736866669861331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691354004631644452963549 259257751736866669861331)
                  ·
                    rfl

theorem cell21_1136031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 3].length) (baseStart_1136031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136031 prefixEnd_1136031 := by exact prefixLift 1136031
  have htrace : WordTrace (prefixWord ++ tailWord_1136031) baseStart_1136031 baseEnd_1136031 := by
    simpa [prefixWord, tailWord_1136031, baseEnd_1136031] using wordTrace_append hprefix tailTrace_1136031
  have hstable : (prefixWord ++ tailWord_1136031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136031).length < 2 ^ (prefixWord ++ tailWord_1136031).sum := by decide
  have hdescent : baseEnd_1136031 < baseStart_1136031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136045 : List Nat := [1, 5, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1136045 : Nat := 118140960795 + 1136045 * 2 ^ 59
def prefixEnd_1136045 : Nat := 4983230072969 + 3 ^ 40 * 1136045 * 2
def baseEnd_1136045 : Nat := 259260946727605756627969

theorem tailTrace_1136045 : CollatzResearch.WordTrace tailWord_1136045 prefixEnd_1136045 259260946727605756627969 := by
  unfold tailWord_1136045
  simp only [CollatzResearch.WordTrace]
  refine ⟨41434965169310460884305589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27623310112873640589537059 41434965169310460884305589)
  ·
    refine ⟨3884527984622855707903649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41434965169310460884305589 3884527984622855707903649)
    ·
      refine ⟨2913395988467141780927737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3884527984622855707903649 2913395988467141780927737)
      ·
        refine ⟨2185046991350356335695803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2913395988467141780927737 2185046991350356335695803)
        ·
          refine ⟨3277570487025534503543705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2185046991350356335695803 3277570487025534503543705)
          ·
            refine ⟨2458177865269150877657779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3277570487025534503543705 2458177865269150877657779)
            ·
              refine ⟨3687266797903726316486669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458177865269150877657779 3687266797903726316486669)
              ·
                refine ⟨1382725049213897368682501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3687266797903726316486669 1382725049213897368682501)
                ·
                  refine ⟨259260946727605756627969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1382725049213897368682501 259260946727605756627969)
                  ·
                    rfl

theorem cell21_1136045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1136045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136045 prefixEnd_1136045 := by exact prefixLift 1136045
  have htrace : WordTrace (prefixWord ++ tailWord_1136045) baseStart_1136045 baseEnd_1136045 := by
    simpa [prefixWord, tailWord_1136045, baseEnd_1136045] using wordTrace_append hprefix tailTrace_1136045
  have hstable : (prefixWord ++ tailWord_1136045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136045).length < 2 ^ (prefixWord ++ tailWord_1136045).sum := by decide
  have hdescent : baseEnd_1136045 < baseStart_1136045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136056 : List Nat := [2, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_1136056 : Nat := 118140960795 + 1136056 * 2 ^ 59
def prefixEnd_1136056 : Nat := 4983230072969 + 3 ^ 40 * 1136056 * 2
def baseEnd_1136056 : Nat := 259263457077472181944613

theorem tailTrace_1136056 : CollatzResearch.WordTrace tailWord_1136056 prefixEnd_1136056 259263457077472181944613 := by
  unfold tailWord_1136056
  simp only [CollatzResearch.WordTrace]
  refine ⟨20717683186135304881478011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27623577581513739841970681 20717683186135304881478011)
  ·
    refine ⟨31076524779202957322217017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20717683186135304881478011 31076524779202957322217017)
    ·
      refine ⟨23307393584402217991662763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31076524779202957322217017 23307393584402217991662763)
      ·
        refine ⟨34961090376603326987494145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23307393584402217991662763 34961090376603326987494145)
        ·
          refine ⟨26220817782452495240620609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34961090376603326987494145 26220817782452495240620609)
          ·
            refine ⟨19665613336839371430465457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26220817782452495240620609 19665613336839371430465457)
            ·
              refine ⟨14749210002629528572849093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19665613336839371430465457 14749210002629528572849093)
              ·
                refine ⟨2765476875493036607409205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14749210002629528572849093 2765476875493036607409205)
                ·
                  refine ⟨259263457077472181944613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765476875493036607409205 259263457077472181944613)
                  ·
                    rfl

theorem cell21_1136056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_1136056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136056 prefixEnd_1136056 := by exact prefixLift 1136056
  have htrace : WordTrace (prefixWord ++ tailWord_1136056) baseStart_1136056 baseEnd_1136056 := by
    simpa [prefixWord, tailWord_1136056, baseEnd_1136056] using wordTrace_append hprefix tailTrace_1136056
  have hstable : (prefixWord ++ tailWord_1136056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136056).length < 2 ^ (prefixWord ++ tailWord_1136056).sum := by decide
  have hdescent : baseEnd_1136056 < baseStart_1136056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136073 : List Nat := [1, 2, 1, 1, 2, 1, 3, 7, 3]
def baseStart_1136073 : Nat := 118140960795 + 1136073 * 2 ^ 59
def prefixEnd_1136073 : Nat := 4983230072969 + 3 ^ 40 * 1136073 * 2
def baseEnd_1136073 : Nat := 259267336709083930161245

theorem tailTrace_1136073 : CollatzResearch.WordTrace tailWord_1136073 prefixEnd_1136073 259267336709083930161245 := by
  unfold tailWord_1136073
  simp only [CollatzResearch.WordTrace]
  refine ⟨41435986413209021666324873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27623990942139347777549915 41435986413209021666324873)
  ·
    refine ⟨31076989809906766249743655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41435986413209021666324873 31076989809906766249743655)
    ·
      refine ⟨46615484714860149374615483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31076989809906766249743655 46615484714860149374615483)
      ·
        refine ⟨69923227072290224061923225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46615484714860149374615483 69923227072290224061923225)
        ·
          refine ⟨52442420304217668046442419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69923227072290224061923225 52442420304217668046442419)
          ·
            refine ⟨78663630456326502069663629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52442420304217668046442419 78663630456326502069663629)
            ·
              refine ⟨29498861421122438276123861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78663630456326502069663629 29498861421122438276123861)
              ·
                refine ⟨691379564557557147096653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 29498861421122438276123861 691379564557557147096653)
                ·
                  refine ⟨259267336709083930161245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691379564557557147096653 259267336709083930161245)
                  ·
                    rfl

theorem cell21_1136073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 3].length) (baseStart_1136073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136073 prefixEnd_1136073 := by exact prefixLift 1136073
  have htrace : WordTrace (prefixWord ++ tailWord_1136073) baseStart_1136073 baseEnd_1136073 := by
    simpa [prefixWord, tailWord_1136073, baseEnd_1136073] using wordTrace_append hprefix tailTrace_1136073
  have hstable : (prefixWord ++ tailWord_1136073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136073).length < 2 ^ (prefixWord ++ tailWord_1136073).sum := by decide
  have hdescent : baseEnd_1136073 < baseStart_1136073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136090 : List Nat := [3, 1, 1, 2, 3, 3, 1, 4, 3]
def baseStart_1136090 : Nat := 118140960795 + 1136090 * 2 ^ 59
def prefixEnd_1136090 : Nat := 4983230072969 + 3 ^ 40 * 1136090 * 2
def baseEnd_1136090 : Nat := 259271216340695678377877

theorem tailTrace_1136090 : CollatzResearch.WordTrace tailWord_1136090 prefixEnd_1136090 259271216340695678377877 := by
  unfold tailWord_1136090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10359151613536858392423431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27624404302764955713129149 10359151613536858392423431)
  ·
    refine ⟨15538727420305287588635147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10359151613536858392423431 15538727420305287588635147)
    ·
      refine ⟨23308091130457931382952721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15538727420305287588635147 23308091130457931382952721)
      ·
        refine ⟨17481068347843448537214541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23308091130457931382952721 17481068347843448537214541)
        ·
          refine ⟨6555400630441293201455453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17481068347843448537214541 6555400630441293201455453)
          ·
            refine ⟨2458275236415484950545795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6555400630441293201455453 2458275236415484950545795)
            ·
              refine ⟨3687412854623227425818693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2458275236415484950545795 3687412854623227425818693)
              ·
                refine ⟨691389910241855142341005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3687412854623227425818693 691389910241855142341005)
                ·
                  refine ⟨259271216340695678377877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691389910241855142341005 259271216340695678377877)
                  ·
                    rfl

theorem cell21_1136090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 4, 3].length) (baseStart_1136090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136090 prefixEnd_1136090 := by exact prefixLift 1136090
  have htrace : WordTrace (prefixWord ++ tailWord_1136090) baseStart_1136090 baseEnd_1136090 := by
    simpa [prefixWord, tailWord_1136090, baseEnd_1136090] using wordTrace_append hprefix tailTrace_1136090
  have hstable : (prefixWord ++ tailWord_1136090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136090).length < 2 ^ (prefixWord ++ tailWord_1136090).sum := by decide
  have hdescent : baseEnd_1136090 < baseStart_1136090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136149 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 5]
def baseStart_1136149 : Nat := 118140960795 + 1136149 * 2 ^ 59
def prefixEnd_1136149 : Nat := 4983230072969 + 3 ^ 40 * 1136149 * 2
def baseEnd_1136149 : Nat := 259284680944524686894423

theorem tailTrace_1136149 : CollatzResearch.WordTrace tailWord_1136149 prefixEnd_1136149 259284680944524686894423 := by
  unfold tailWord_1136149
  simp only [CollatzResearch.WordTrace]
  refine ⟨41438758360933686646091501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27625838907289124430727667 41438758360933686646091501)
  ·
    refine ⟨15539534385350132492284313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41438758360933686646091501 15539534385350132492284313)
    ·
      refine ⟨11654650789012599369213235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15539534385350132492284313 11654650789012599369213235)
      ·
        refine ⟨17481976183518899053819853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11654650789012599369213235 17481976183518899053819853)
        ·
          refine ⟨6555741068819587145182445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17481976183518899053819853 6555741068819587145182445)
          ·
            refine ⟨2458402900807345179443417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6555741068819587145182445 2458402900807345179443417)
            ·
              refine ⟨1843802175605508884582563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2458402900807345179443417 1843802175605508884582563)
              ·
                refine ⟨2765703263408263326873845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1843802175605508884582563 2765703263408263326873845)
                ·
                  refine ⟨259284680944524686894423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2765703263408263326873845 259284680944524686894423)
                  ·
                    rfl

theorem cell21_1136149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_1136149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136149 prefixEnd_1136149 := by exact prefixLift 1136149
  have htrace : WordTrace (prefixWord ++ tailWord_1136149) baseStart_1136149 baseEnd_1136149 := by
    simpa [prefixWord, tailWord_1136149, baseEnd_1136149] using wordTrace_append hprefix tailTrace_1136149
  have hstable : (prefixWord ++ tailWord_1136149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136149).length < 2 ^ (prefixWord ++ tailWord_1136149).sum := by decide
  have hdescent : baseEnd_1136149 < baseStart_1136149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136253 : List Nat := [1, 4, 1, 1, 4, 10]
def baseStart_1136253 : Nat := 118140960795 + 1136253 * 2 ^ 59
def prefixEnd_1136253 : Nat := 4983230072969 + 3 ^ 40 * 1136253 * 2
def baseEnd_1136253 : Nat := 9604015376349763598551

theorem tailTrace_1136253 : CollatzResearch.WordTrace tailWord_1136253 prefixEnd_1136253 9604015376349763598551 := by
  unfold tailWord_1136253
  simp only [CollatzResearch.WordTrace]
  refine ⟨41442551552556912407877413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27628367701704608271918275 41442551552556912407877413)
  ·
    refine ⟨7770478416104421076477015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41442551552556912407877413 7770478416104421076477015)
    ·
      refine ⟨11655717624156631614715523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7770478416104421076477015 11655717624156631614715523)
      ·
        refine ⟨17483576436234947422073285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11655717624156631614715523 17483576436234947422073285)
        ·
          refine ⟨3278170581794052641638741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17483576436234947422073285 3278170581794052641638741)
          ·
            refine ⟨9604015376349763598551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3278170581794052641638741 9604015376349763598551)
            ·
              rfl

theorem cell21_1136253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 10].length) (baseStart_1136253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136253 prefixEnd_1136253 := by exact prefixLift 1136253
  have htrace : WordTrace (prefixWord ++ tailWord_1136253) baseStart_1136253 baseEnd_1136253 := by
    simpa [prefixWord, tailWord_1136253, baseEnd_1136253] using wordTrace_append hprefix tailTrace_1136253
  have hstable : (prefixWord ++ tailWord_1136253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136253).length < 2 ^ (prefixWord ++ tailWord_1136253).sum := by decide
  have hdescent : baseEnd_1136253 < baseStart_1136253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136270 : List Nat := [4, 1, 1, 3, 1, 2, 3, 6]
def baseStart_1136270 : Nat := 118140960795 + 1136270 * 2 ^ 59
def prefixEnd_1136270 : Nat := 4983230072969 + 3 ^ 40 * 1136270 * 2
def baseEnd_1136270 : Nat := 86437431597685121792503

theorem tailTrace_1136270 : CollatzResearch.WordTrace tailWord_1136270 prefixEnd_1136270 86437431597685121792503 := by
  unfold tailWord_1136270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180396449186915538905783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27628781062330216207497509 5180396449186915538905783)
  ·
    refine ⟨7770594673780373308358675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5180396449186915538905783 7770594673780373308358675)
    ·
      refine ⟨11655892010670559962538013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7770594673780373308358675 11655892010670559962538013)
      ·
        refine ⟨4370959504001459985951755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11655892010670559962538013 4370959504001459985951755)
        ·
          refine ⟨6556439256002189978927633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4370959504001459985951755 6556439256002189978927633)
          ·
            refine ⟨4917329442001642484195725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6556439256002189978927633 4917329442001642484195725)
            ·
              refine ⟨1843998540750615931573397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4917329442001642484195725 1843998540750615931573397)
              ·
                refine ⟨86437431597685121792503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1843998540750615931573397 86437431597685121792503)
                ·
                  rfl

theorem cell21_1136270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_1136270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136270 prefixEnd_1136270 := by exact prefixLift 1136270
  have htrace : WordTrace (prefixWord ++ tailWord_1136270) baseStart_1136270 baseEnd_1136270 := by
    simpa [prefixWord, tailWord_1136270, baseEnd_1136270] using wordTrace_append hprefix tailTrace_1136270
  have hstable : (prefixWord ++ tailWord_1136270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136270).length < 2 ^ (prefixWord ++ tailWord_1136270).sum := by decide
  have hdescent : baseEnd_1136270 < baseStart_1136270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136318 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 3]
def baseStart_1136318 : Nat := 118140960795 + 1136318 * 2 ^ 59
def prefixEnd_1136318 : Nat := 4983230072969 + 3 ^ 40 * 1136318 * 2
def baseEnd_1136318 : Nat := 259323249047017948577411

theorem tailTrace_1136318 : CollatzResearch.WordTrace tailWord_1136318 prefixEnd_1136318 259323249047017948577411 := by
  unfold tailWord_1136318
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180615287165178563624201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27629948198214285672662405 5180615287165178563624201)
  ·
    refine ⟨3885461465373883922718151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5180615287165178563624201 3885461465373883922718151)
    ·
      refine ⟨5828192198060825884077227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3885461465373883922718151 5828192198060825884077227)
      ·
        refine ⟨8742288297091238826115841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5828192198060825884077227 8742288297091238826115841)
        ·
          refine ⟨6556716222818429119586881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8742288297091238826115841 6556716222818429119586881)
          ·
            refine ⟨4917537167113821839690161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6556716222818429119586881 4917537167113821839690161)
            ·
              refine ⟨3688152875335366379767621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4917537167113821839690161 3688152875335366379767621)
              ·
                refine ⟨691528664125381196206429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3688152875335366379767621 691528664125381196206429)
                ·
                  refine ⟨259323249047017948577411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691528664125381196206429 259323249047017948577411)
                  ·
                    rfl

theorem cell21_1136318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_1136318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136318 prefixEnd_1136318 := by exact prefixLift 1136318
  have htrace : WordTrace (prefixWord ++ tailWord_1136318) baseStart_1136318 baseEnd_1136318 := by
    simpa [prefixWord, tailWord_1136318, baseEnd_1136318] using wordTrace_append hprefix tailTrace_1136318
  have hstable : (prefixWord ++ tailWord_1136318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136318).length < 2 ^ (prefixWord ++ tailWord_1136318).sum := by decide
  have hdescent : baseEnd_1136318 < baseStart_1136318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136346 : List Nat := [3, 1, 1, 2, 2, 3, 4, 5]
def baseStart_1136346 : Nat := 118140960795 + 1136346 * 2 ^ 59
def prefixEnd_1136346 : Nat := 4983230072969 + 3 ^ 40 * 1136346 * 2
def baseEnd_1136346 : Nat := 86443213009498707370229

theorem tailTrace_1136346 : CollatzResearch.WordTrace tailWord_1136346 prefixEnd_1136346 86443213009498707370229 := by
  unfold tailWord_1136346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10361485885304997322753223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27630629027479992860675261 10361485885304997322753223)
  ·
    refine ⟨15542228827957495984129835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10361485885304997322753223 15542228827957495984129835)
    ·
      refine ⟨23313343241936243976194753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15542228827957495984129835 23313343241936243976194753)
      ·
        refine ⟨17485007431452182982146065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23313343241936243976194753 17485007431452182982146065)
        ·
          refine ⟨13113755573589137236609549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17485007431452182982146065 13113755573589137236609549)
          ·
            refine ⟨4917658340095926463728581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13113755573589137236609549 4917658340095926463728581)
            ·
              refine ⟨922060938767986211949109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4917658340095926463728581 922060938767986211949109)
              ·
                refine ⟨86443213009498707370229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 922060938767986211949109 86443213009498707370229)
                ·
                  rfl

theorem cell21_1136346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_1136346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136346 prefixEnd_1136346 := by exact prefixLift 1136346
  have htrace : WordTrace (prefixWord ++ tailWord_1136346) baseStart_1136346 baseEnd_1136346 := by
    simpa [prefixWord, tailWord_1136346, baseEnd_1136346] using wordTrace_append hprefix tailTrace_1136346
  have hstable : (prefixWord ++ tailWord_1136346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136346).length < 2 ^ (prefixWord ++ tailWord_1136346).sum := by decide
  have hdescent : baseEnd_1136346 < baseStart_1136346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136405 : List Nat := [1, 3, 2, 1, 2, 3, 2, 7]
def baseStart_1136405 : Nat := 118140960795 + 1136405 * 2 ^ 59
def prefixEnd_1136405 : Nat := 4983230072969 + 3 ^ 40 * 1136405 * 2
def baseEnd_1136405 : Nat := 86447701210775043542411

theorem tailTrace_1136405 : CollatzResearch.WordTrace tailWord_1136405 prefixEnd_1136405 86447701210775043542411 := by
  unfold tailWord_1136405
  simp only [CollatzResearch.WordTrace]
  refine ⟨41448095448006242367410669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27632063632004161578273779 41448095448006242367410669)
  ·
    refine ⟨15543035793002340887779001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41448095448006242367410669 15543035793002340887779001)
    ·
      refine ⟨11657276844751755665834251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15543035793002340887779001 11657276844751755665834251)
      ·
        refine ⟨17485915267127633498751377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11657276844751755665834251 17485915267127633498751377)
        ·
          refine ⟨13114436450345725124063533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17485915267127633498751377 13114436450345725124063533)
          ·
            refine ⟨4917913668879646921523825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13114436450345725124063533 4917913668879646921523825)
            ·
              refine ⟨3688435251659735191142869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4917913668879646921523825 3688435251659735191142869)
              ·
                refine ⟨86447701210775043542411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3688435251659735191142869 86447701210775043542411)
                ·
                  rfl

theorem cell21_1136405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 7].length) (baseStart_1136405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136405 prefixEnd_1136405 := by exact prefixLift 1136405
  have htrace : WordTrace (prefixWord ++ tailWord_1136405) baseStart_1136405 baseEnd_1136405 := by
    simpa [prefixWord, tailWord_1136405, baseEnd_1136405] using wordTrace_append hprefix tailTrace_1136405
  have hstable : (prefixWord ++ tailWord_1136405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136405).length < 2 ^ (prefixWord ++ tailWord_1136405).sum := by decide
  have hdescent : baseEnd_1136405 < baseStart_1136405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136529 : List Nat := [1, 2, 2, 1, 1, 1, 7, 3, 3]
def baseStart_1136529 : Nat := 118140960795 + 1136529 * 2 ^ 59
def prefixEnd_1136529 : Nat := 4983230072969 + 3 ^ 40 * 1136529 * 2
def baseEnd_1136529 : Nat := 259371402121728470560313

theorem tailTrace_1136529 : CollatzResearch.WordTrace tailWord_1136529 prefixEnd_1136529 259371402121728470560313 := by
  unfold tailWord_1136529
  simp only [CollatzResearch.WordTrace]
  refine ⟨41452618099557011544924641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27635078733038007696616427 41452618099557011544924641)
  ·
    refine ⟨31089463574667758658693481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41452618099557011544924641 31089463574667758658693481)
    ·
      refine ⟨23317097681000818994020111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31089463574667758658693481 23317097681000818994020111)
      ·
        refine ⟨34975646521501228491030167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23317097681000818994020111 34975646521501228491030167)
        ·
          refine ⟨52463469782251842736545251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34975646521501228491030167 52463469782251842736545251)
          ·
            refine ⟨78695204673377764104817877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52463469782251842736545251 78695204673377764104817877)
            ·
              refine ⟨1844418859532291346206669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78695204673377764104817877 1844418859532291346206669)
              ·
                refine ⟨691657072324609254827501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1844418859532291346206669 691657072324609254827501)
                ·
                  refine ⟨259371402121728470560313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691657072324609254827501 259371402121728470560313)
                  ·
                    rfl

theorem cell21_1136529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 3].length) (baseStart_1136529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136529 prefixEnd_1136529 := by exact prefixLift 1136529
  have htrace : WordTrace (prefixWord ++ tailWord_1136529) baseStart_1136529 baseEnd_1136529 := by
    simpa [prefixWord, tailWord_1136529, baseEnd_1136529] using wordTrace_append hprefix tailTrace_1136529
  have hstable : (prefixWord ++ tailWord_1136529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136529).length < 2 ^ (prefixWord ++ tailWord_1136529).sum := by decide
  have hdescent : baseEnd_1136529 < baseStart_1136529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136546 : List Nat := [3, 3, 1, 2, 3, 2, 1, 1, 5]
def baseStart_1136546 : Nat := 118140960795 + 1136546 * 2 ^ 59
def prefixEnd_1136546 : Nat := 4983230072969 + 3 ^ 40 * 1136546 * 2
def baseEnd_1136546 : Nat := 259375281753340218776945

theorem tailTrace_1136546 : CollatzResearch.WordTrace tailWord_1136546 prefixEnd_1136546 259375281753340218776945 := by
  unfold tailWord_1136546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10363309535123855862073373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27635492093663615632195661 10363309535123855862073373)
  ·
    refine ⟨3886241075671445948277515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10363309535123855862073373 3886241075671445948277515)
    ·
      refine ⟨5829361613507168922416273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3886241075671445948277515 5829361613507168922416273)
      ·
        refine ⟨4372021210130376691812205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5829361613507168922416273 4372021210130376691812205)
        ·
          refine ⟨1639507953798891259429577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4372021210130376691812205 1639507953798891259429577)
          ·
            refine ⟨1229630965349168444572183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639507953798891259429577 1229630965349168444572183)
            ·
              refine ⟨1844446448023752666858275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229630965349168444572183 1844446448023752666858275)
              ·
                refine ⟨2766669672035629000287413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844446448023752666858275 2766669672035629000287413)
                ·
                  refine ⟨259375281753340218776945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2766669672035629000287413 259375281753340218776945)
                  ·
                    rfl

theorem cell21_1136546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_1136546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136546 prefixEnd_1136546 := by exact prefixLift 1136546
  have htrace : WordTrace (prefixWord ++ tailWord_1136546) baseStart_1136546 baseEnd_1136546 := by
    simpa [prefixWord, tailWord_1136546, baseEnd_1136546] using wordTrace_append hprefix tailTrace_1136546
  have hstable : (prefixWord ++ tailWord_1136546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136546).length < 2 ^ (prefixWord ++ tailWord_1136546).sum := by decide
  have hdescent : baseEnd_1136546 < baseStart_1136546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136664 : List Nat := [2, 1, 2, 3, 2, 1, 4, 1, 5]
def baseStart_1136664 : Nat := 118140960795 + 1136664 * 2 ^ 59
def prefixEnd_1136664 : Nat := 4983230072969 + 3 ^ 40 * 1136664 * 2
def baseEnd_1136664 : Nat := 259402210960998235810037

theorem tailTrace_1136664 : CollatzResearch.WordTrace tailWord_1136664 prefixEnd_1136664 259402210960998235810037 := by
  unfold tailWord_1136664
  simp only [CollatzResearch.WordTrace]
  refine ⟨20728770977033964800544523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27638361302711953067392697 20728770977033964800544523)
  ·
    refine ⟨31093156465550947200816785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20728770977033964800544523 31093156465550947200816785)
    ·
      refine ⟨23319867349163210400612589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31093156465550947200816785 23319867349163210400612589)
      ·
        refine ⟨8744950255936203900229721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23319867349163210400612589 8744950255936203900229721)
        ·
          refine ⟨6558712691952152925172291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8744950255936203900229721 6558712691952152925172291)
          ·
            refine ⟨9838069037928229387758437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558712691952152925172291 9838069037928229387758437)
            ·
              refine ⟨1844637944611543010204707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9838069037928229387758437 1844637944611543010204707)
              ·
                refine ⟨2766956916917314515307061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1844637944611543010204707 2766956916917314515307061)
                ·
                  refine ⟨259402210960998235810037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2766956916917314515307061 259402210960998235810037)
                  ·
                    rfl

theorem cell21_1136664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 5].length) (baseStart_1136664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136664 prefixEnd_1136664 := by exact prefixLift 1136664
  have htrace : WordTrace (prefixWord ++ tailWord_1136664) baseStart_1136664 baseEnd_1136664 := by
    simpa [prefixWord, tailWord_1136664, baseEnd_1136664] using wordTrace_append hprefix tailTrace_1136664
  have hstable : (prefixWord ++ tailWord_1136664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136664).length < 2 ^ (prefixWord ++ tailWord_1136664).sum := by decide
  have hdescent : baseEnd_1136664 < baseStart_1136664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136771 : List Nat := [1, 1, 1, 3, 3, 4, 2, 2, 4]
def baseStart_1136771 : Nat := 118140960795 + 1136771 * 2 ^ 59
def prefixEnd_1136771 : Nat := 4983230072969 + 3 ^ 40 * 1136771 * 2
def baseEnd_1136771 : Nat := 259426629818789827526485

theorem tailTrace_1136771 : CollatzResearch.WordTrace tailWord_1136771 prefixEnd_1136771 259426629818789827526485 := by
  unfold tailWord_1136771
  simp only [CollatzResearch.WordTrace]
  refine ⟨41461444564680286875234167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27640963043120191250156111 41461444564680286875234167)
  ·
    refine ⟨62192166847020430312851251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41461444564680286875234167 62192166847020430312851251)
    ·
      refine ⟨93288250270530645469276877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62192166847020430312851251 93288250270530645469276877)
      ·
        refine ⟨34983093851448992050978829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93288250270530645469276877 34983093851448992050978829)
        ·
          refine ⟨13118660194293372019117061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34983093851448992050978829 13118660194293372019117061)
          ·
            refine ⟨2459748786430007253584449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13118660194293372019117061 2459748786430007253584449)
            ·
              refine ⟨1844811589822505440188337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2459748786430007253584449 1844811589822505440188337)
              ·
                refine ⟨1383608692366879080141253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1844811589822505440188337 1383608692366879080141253)
                ·
                  refine ⟨259426629818789827526485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383608692366879080141253 259426629818789827526485)
                  ·
                    rfl

theorem cell21_1136771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 2, 4].length) (baseStart_1136771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136771 prefixEnd_1136771 := by exact prefixLift 1136771
  have htrace : WordTrace (prefixWord ++ tailWord_1136771) baseStart_1136771 baseEnd_1136771 := by
    simpa [prefixWord, tailWord_1136771, baseEnd_1136771] using wordTrace_append hprefix tailTrace_1136771
  have hstable : (prefixWord ++ tailWord_1136771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136771).length < 2 ^ (prefixWord ++ tailWord_1136771).sum := by decide
  have hdescent : baseEnd_1136771 < baseStart_1136771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136847 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 4]
def baseStart_1136847 : Nat := 118140960795 + 1136847 * 2 ^ 59
def prefixEnd_1136847 : Nat := 4983230072969 + 3 ^ 40 * 1136847 * 2
def baseEnd_1136847 : Nat := 259443974054230584259663

theorem tailTrace_1136847 : CollatzResearch.WordTrace tailWord_1136847 prefixEnd_1136847 259443974054230584259663 := by
  unfold tailWord_1136847
  simp only [CollatzResearch.WordTrace]
  refine ⟨41464216512404951855000795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27642811008269967903333863 41464216512404951855000795)
  ·
    refine ⟨62196324768607427782501193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41464216512404951855000795 62196324768607427782501193)
    ·
      refine ⟨46647243576455570836875895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62196324768607427782501193 46647243576455570836875895)
      ·
        refine ⟨69970865364683356255313843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46647243576455570836875895 69970865364683356255313843)
        ·
          refine ⟨104956298047025034382970765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69970865364683356255313843 104956298047025034382970765)
          ·
            refine ⟨39358611767634387893614037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104956298047025034382970765 39358611767634387893614037)
            ·
              refine ⟨922467463303930966256579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39358611767634387893614037 922467463303930966256579)
              ·
                refine ⟨1383701194955896449384869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 922467463303930966256579 1383701194955896449384869)
                ·
                  refine ⟨259443974054230584259663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383701194955896449384869 259443974054230584259663)
                  ·
                    rfl

theorem cell21_1136847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 4].length) (baseStart_1136847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136847 prefixEnd_1136847 := by exact prefixLift 1136847
  have htrace : WordTrace (prefixWord ++ tailWord_1136847) baseStart_1136847 baseEnd_1136847 := by
    simpa [prefixWord, tailWord_1136847, baseEnd_1136847] using wordTrace_append hprefix tailTrace_1136847
  have hstable : (prefixWord ++ tailWord_1136847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136847).length < 2 ^ (prefixWord ++ tailWord_1136847).sum := by decide
  have hdescent : baseEnd_1136847 < baseStart_1136847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136867 : List Nat := [1, 1, 1, 8, 1, 2, 1, 3, 3]
def baseStart_1136867 : Nat := 118140960795 + 1136867 * 2 ^ 59
def prefixEnd_1136867 : Nat := 4983230072969 + 3 ^ 40 * 1136867 * 2
def baseEnd_1136867 : Nat := 259448538326714993926289

theorem tailTrace_1136867 : CollatzResearch.WordTrace tailWord_1136867 prefixEnd_1136867 259448538326714993926289 := by
  unfold tailWord_1136867
  simp only [CollatzResearch.WordTrace]
  refine ⟨41464945972332495270728855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27643297314888330180485903 41464945972332495270728855)
  ·
    refine ⟨62197418958498742906093283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41464945972332495270728855 62197418958498742906093283)
    ·
      refine ⟨93296128437748114359139925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62197418958498742906093283 93296128437748114359139925)
      ·
        refine ⟨1093314005129860715146171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 93296128437748114359139925 1093314005129860715146171)
        ·
          refine ⟨1639971007694791072719257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1093314005129860715146171 1639971007694791072719257)
          ·
            refine ⟨1229978255771093304539443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1639971007694791072719257 1229978255771093304539443)
            ·
              refine ⟨1844967383656639956809165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1229978255771093304539443 1844967383656639956809165)
              ·
                refine ⟨691862768871239983803437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1844967383656639956809165 691862768871239983803437)
                ·
                  refine ⟨259448538326714993926289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691862768871239983803437 259448538326714993926289)
                  ·
                    rfl

theorem cell21_1136867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 3, 3].length) (baseStart_1136867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136867 prefixEnd_1136867 := by exact prefixLift 1136867
  have htrace : WordTrace (prefixWord ++ tailWord_1136867) baseStart_1136867 baseEnd_1136867 := by
    simpa [prefixWord, tailWord_1136867, baseEnd_1136867] using wordTrace_append hprefix tailTrace_1136867
  have hstable : (prefixWord ++ tailWord_1136867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136867).length < 2 ^ (prefixWord ++ tailWord_1136867).sum := by decide
  have hdescent : baseEnd_1136867 < baseStart_1136867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136892 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 5]
def baseStart_1136892 : Nat := 118140960795 + 1136892 * 2 ^ 59
def prefixEnd_1136892 : Nat := 4983230072969 + 3 ^ 40 * 1136892 * 2
def baseEnd_1136892 : Nat := 259454243667320506009571

theorem tailTrace_1136892 : CollatzResearch.WordTrace tailWord_1136892 prefixEnd_1136892 259454243667320506009571 := by
  unfold tailWord_1136892
  simp only [CollatzResearch.WordTrace]
  refine ⟨20732928898620962270194465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27643905198161283026925953 20732928898620962270194465)
  ·
    refine ⟨15549696673965721702645849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20732928898620962270194465 15549696673965721702645849)
    ·
      refine ⟨11662272505474291276984387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15549696673965721702645849 11662272505474291276984387)
      ·
        refine ⟨17493408758211436915476581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11662272505474291276984387 17493408758211436915476581)
        ·
          refine ⟨3280014142164644421651859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17493408758211436915476581 3280014142164644421651859)
          ·
            refine ⟨4920021213246966632477789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280014142164644421651859 4920021213246966632477789)
            ·
              refine ⟨1845007954967612487179171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4920021213246966632477789 1845007954967612487179171)
              ·
                refine ⟨2767511932451418730768757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845007954967612487179171 2767511932451418730768757)
                ·
                  refine ⟨259454243667320506009571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2767511932451418730768757 259454243667320506009571)
                  ·
                    rfl

theorem cell21_1136892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_1136892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136892 prefixEnd_1136892 := by exact prefixLift 1136892
  have htrace : WordTrace (prefixWord ++ tailWord_1136892) baseStart_1136892 baseEnd_1136892 := by
    simpa [prefixWord, tailWord_1136892, baseEnd_1136892] using wordTrace_append hprefix tailTrace_1136892
  have hstable : (prefixWord ++ tailWord_1136892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136892).length < 2 ^ (prefixWord ++ tailWord_1136892).sum := by decide
  have hdescent : baseEnd_1136892 < baseStart_1136892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136920 : List Nat := [2, 1, 2, 3, 1, 2, 1, 9]
def baseStart_1136920 : Nat := 118140960795 + 1136920 * 2 ^ 59
def prefixEnd_1136920 : Nat := 4983230072969 + 3 ^ 40 * 1136920 * 2
def baseEnd_1136920 : Nat := 86486877882932893180949

theorem tailTrace_1136920 : CollatzResearch.WordTrace tailWord_1136920 prefixEnd_1136920 86486877882932893180949 := by
  unfold tailWord_1136920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20733439520570242661204107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27644586027426990214938809 20733439520570242661204107)
  ·
    refine ⟨31100159280855363991806161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20733439520570242661204107 31100159280855363991806161)
    ·
      refine ⟨23325119460641522993854621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31100159280855363991806161 23325119460641522993854621)
      ·
        refine ⟨8746919797740571122695483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23325119460641522993854621 8746919797740571122695483)
        ·
          refine ⟨13120379696610856684043225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8746919797740571122695483 13120379696610856684043225)
          ·
            refine ⟨9840284772458142513032419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13120379696610856684043225 9840284772458142513032419)
            ·
              refine ⟨14760427158687213769548629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9840284772458142513032419 14760427158687213769548629)
              ·
                refine ⟨86486877882932893180949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14760427158687213769548629 86486877882932893180949)
                ·
                  rfl

theorem cell21_1136920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_1136920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136920 prefixEnd_1136920 := by exact prefixLift 1136920
  have htrace : WordTrace (prefixWord ++ tailWord_1136920) baseStart_1136920 baseEnd_1136920 := by
    simpa [prefixWord, tailWord_1136920, baseEnd_1136920] using wordTrace_append hprefix tailTrace_1136920
  have hstable : (prefixWord ++ tailWord_1136920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136920).length < 2 ^ (prefixWord ++ tailWord_1136920).sum := by decide
  have hdescent : baseEnd_1136920 < baseStart_1136920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136965 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1136965 : Nat := 118140960795 + 1136965 * 2 ^ 59
def prefixEnd_1136965 : Nat := 4983230072969 + 3 ^ 40 * 1136965 * 2
def baseEnd_1136965 : Nat := 259470903261888601292755

theorem tailTrace_1136965 : CollatzResearch.WordTrace tailWord_1136965 prefixEnd_1136965 259470903261888601292755 := by
  unfold tailWord_1136965
  simp only [CollatzResearch.WordTrace]
  refine ⟨41468520325977458007796349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27645680217318305338530899 41468520325977458007796349)
  ·
    refine ⟨15550695122241546752923631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41468520325977458007796349 15550695122241546752923631)
    ·
      refine ⟨23326042683362320129385447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15550695122241546752923631 23326042683362320129385447)
      ·
        refine ⟨34989064025043480194078171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23326042683362320129385447 34989064025043480194078171)
        ·
          refine ⟨52483596037565220291117257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34989064025043480194078171 52483596037565220291117257)
          ·
            refine ⟨39362697028173915218337943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52483596037565220291117257 39362697028173915218337943)
            ·
              refine ⟨59044045542260872827506915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39362697028173915218337943 59044045542260872827506915)
              ·
                refine ⟨88566068313391309241260373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59044045542260872827506915 88566068313391309241260373)
                ·
                  refine ⟨259470903261888601292755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 88566068313391309241260373 259470903261888601292755)
                  ·
                    rfl

theorem cell21_1136965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1136965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136965 prefixEnd_1136965 := by exact prefixLift 1136965
  have htrace : WordTrace (prefixWord ++ tailWord_1136965) baseStart_1136965 baseEnd_1136965 := by
    simpa [prefixWord, tailWord_1136965, baseEnd_1136965] using wordTrace_append hprefix tailTrace_1136965
  have hstable : (prefixWord ++ tailWord_1136965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136965).length < 2 ^ (prefixWord ++ tailWord_1136965).sum := by decide
  have hdescent : baseEnd_1136965 < baseStart_1136965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136996 : List Nat := [2, 3, 1, 1, 3, 1, 10]
def baseStart_1136996 : Nat := 118140960795 + 1136996 * 2 ^ 59
def prefixEnd_1136996 : Nat := 4983230072969 + 3 ^ 40 * 1136996 * 2
def baseEnd_1136996 : Nat := 28830886431582159586225

theorem tailTrace_1136996 : CollatzResearch.WordTrace tailWord_1136996 prefixEnd_1136996 28830886431582159586225 := by
  unfold tailWord_1136996
  simp only [CollatzResearch.WordTrace]
  refine ⟨20734825494432575151087421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27646433992576766868116561 20734825494432575151087421)
  ·
    refine ⟨7775559560412215681657783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20734825494432575151087421 7775559560412215681657783)
    ·
      refine ⟨11663339340618323522486675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7775559560412215681657783 11663339340618323522486675)
      ·
        refine ⟨17495009010927485283730013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11663339340618323522486675 17495009010927485283730013)
        ·
          refine ⟨6560628379097806981398755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17495009010927485283730013 6560628379097806981398755)
          ·
            refine ⟨9840942568646710472098133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560628379097806981398755 9840942568646710472098133)
            ·
              refine ⟨28830886431582159586225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9840942568646710472098133 28830886431582159586225)
              ·
                rfl

theorem cell21_1136996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 10].length) (baseStart_1136996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136996 prefixEnd_1136996 := by exact prefixLift 1136996
  have htrace : WordTrace (prefixWord ++ tailWord_1136996) baseStart_1136996 baseEnd_1136996 := by
    simpa [prefixWord, tailWord_1136996, baseEnd_1136996] using wordTrace_append hprefix tailTrace_1136996
  have hstable : (prefixWord ++ tailWord_1136996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136996).length < 2 ^ (prefixWord ++ tailWord_1136996).sum := by decide
  have hdescent : baseEnd_1136996 < baseStart_1136996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1136999 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 4]
def baseStart_1136999 : Nat := 118140960795 + 1136999 * 2 ^ 59
def prefixEnd_1136999 : Nat := 4983230072969 + 3 ^ 40 * 1136999 * 2
def baseEnd_1136999 : Nat := 259478662525112097726019

theorem tailTrace_1136999 : CollatzResearch.WordTrace tailWord_1136999 prefixEnd_1136999 259478662525112097726019 := by
  unfold tailWord_1136999
  simp only [CollatzResearch.WordTrace]
  refine ⟨41469760407854281814534051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27646506938569521209689367 41469760407854281814534051)
  ·
    refine ⟨62204640611781422721801077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41469760407854281814534051 62204640611781422721801077)
    ·
      refine ⟨5831685057354508380168851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62204640611781422721801077 5831685057354508380168851)
      ·
        refine ⟨8747527586031762570253277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5831685057354508380168851 8747527586031762570253277)
        ·
          refine ⟨3280322844761910963844979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8747527586031762570253277 3280322844761910963844979)
          ·
            refine ⟨4920484267142866445767469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280322844761910963844979 4920484267142866445767469)
            ·
              refine ⟨1845181600178574917162801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4920484267142866445767469 1845181600178574917162801)
              ·
                refine ⟨1383886200133931187872101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1845181600178574917162801 1383886200133931187872101)
                ·
                  refine ⟨259478662525112097726019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1383886200133931187872101 259478662525112097726019)
                  ·
                    rfl

theorem cell21_1136999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 4].length) (baseStart_1136999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1136999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1136999 prefixEnd_1136999 := by exact prefixLift 1136999
  have htrace : WordTrace (prefixWord ++ tailWord_1136999) baseStart_1136999 baseEnd_1136999 := by
    simpa [prefixWord, tailWord_1136999, baseEnd_1136999] using wordTrace_append hprefix tailTrace_1136999
  have hstable : (prefixWord ++ tailWord_1136999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1136999).length < 2 ^ (prefixWord ++ tailWord_1136999).sum := by decide
  have hdescent : baseEnd_1136999 < baseStart_1136999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1136999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137058 : List Nat := [3, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1137058 : Nat := 118140960795 + 1137058 * 2 ^ 59
def prefixEnd_1137058 : Nat := 4983230072969 + 3 ^ 40 * 1137058 * 2
def baseEnd_1137058 : Nat := 259492127128941106242565

theorem tailTrace_1137058 : CollatzResearch.WordTrace tailWord_1137058 prefixEnd_1137058 259492127128941106242565 := by
  unfold tailWord_1137058
  simp only [CollatzResearch.WordTrace]
  refine ⟨10367978078660133722732957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27647941543093689927287885 10367978078660133722732957)
  ·
    refine ⟨3887991779497550146024859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10367978078660133722732957 3887991779497550146024859)
    ·
      refine ⟨5831987669246325219037289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3887991779497550146024859 5831987669246325219037289)
      ·
        refine ⟨4373990751934743914277967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5831987669246325219037289 4373990751934743914277967)
        ·
          refine ⟨6560986127902115871416951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4373990751934743914277967 6560986127902115871416951)
          ·
            refine ⟨9841479191853173807125427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6560986127902115871416951 9841479191853173807125427)
            ·
              refine ⟨14762218787779760710688141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9841479191853173807125427 14762218787779760710688141)
              ·
                refine ⟨5535832045417410266508053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14762218787779760710688141 5535832045417410266508053)
                ·
                  refine ⟨259492127128941106242565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5535832045417410266508053 259492127128941106242565)
                  ·
                    rfl

theorem cell21_1137058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1137058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137058 prefixEnd_1137058 := by exact prefixLift 1137058
  have htrace : WordTrace (prefixWord ++ tailWord_1137058) baseStart_1137058 baseEnd_1137058 := by
    simpa [prefixWord, tailWord_1137058, baseEnd_1137058] using wordTrace_append hprefix tailTrace_1137058
  have hstable : (prefixWord ++ tailWord_1137058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137058).length < 2 ^ (prefixWord ++ tailWord_1137058).sum := by decide
  have hdescent : baseEnd_1137058 < baseStart_1137058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137061 : List Nat := [1, 3, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1137061 : Nat := 118140960795 + 1137061 * 2 ^ 59
def prefixEnd_1137061 : Nat := 4983230072969 + 3 ^ 40 * 1137061 * 2
def baseEnd_1137061 : Nat := 259492811769813767692559

theorem tailTrace_1137061 : CollatzResearch.WordTrace tailWord_1137061 prefixEnd_1137061 259492811769813767692559 := by
  unfold tailWord_1137061
  simp only [CollatzResearch.WordTrace]
  refine ⟨41472021733629666403291037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27648014489086444268860691 41472021733629666403291037)
  ·
    refine ⟨15552008150111124901234139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41472021733629666403291037 15552008150111124901234139)
    ·
      refine ⟨23328012225166687351851209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15552008150111124901234139 23328012225166687351851209)
      ·
        refine ⟨17496009168875015513888407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23328012225166687351851209 17496009168875015513888407)
        ·
          refine ⟨26244013753312523270832611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17496009168875015513888407 26244013753312523270832611)
          ·
            refine ⟨39366020629968784906248917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26244013753312523270832611 39366020629968784906248917)
            ·
              refine ⟨922641108514893396240209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 39366020629968784906248917 922641108514893396240209)
              ·
                refine ⟨691980831386170047180157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922641108514893396240209 691980831386170047180157)
                ·
                  refine ⟨259492811769813767692559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 691980831386170047180157 259492811769813767692559)
                  ·
                    rfl

theorem cell21_1137061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1137061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137061 prefixEnd_1137061 := by exact prefixLift 1137061
  have htrace : WordTrace (prefixWord ++ tailWord_1137061) baseStart_1137061 baseEnd_1137061 := by
    simpa [prefixWord, tailWord_1137061, baseEnd_1137061] using wordTrace_append hprefix tailTrace_1137061
  have hstable : (prefixWord ++ tailWord_1137061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137061).length < 2 ^ (prefixWord ++ tailWord_1137061).sum := by decide
  have hdescent : baseEnd_1137061 < baseStart_1137061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137106 : List Nat := [3, 2, 2, 4, 2, 8]
def baseStart_1137106 : Nat := 118140960795 + 1137106 * 2 ^ 59
def prefixEnd_1137106 : Nat := 4983230072969 + 3 ^ 40 * 1137106 * 2
def baseEnd_1137106 : Nat := 9611225236403840349721

theorem tailTrace_1137106 : CollatzResearch.WordTrace tailWord_1137106 prefixEnd_1137106 9611225236403840349721 := by
  unfold tailWord_1137106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10368415754616659772169793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27649108678977759392452781 10368415754616659772169793)
  ·
    refine ⟨7776311815962494829127345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10368415754616659772169793 7776311815962494829127345)
    ·
      refine ⟨5832233861971871121845509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7776311815962494829127345 5832233861971871121845509)
      ·
        refine ⟨1093543849119725835346033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5832233861971871121845509 1093543849119725835346033)
        ·
          refine ⟨820157886839794376509525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1093543849119725835346033 820157886839794376509525)
          ·
            refine ⟨9611225236403840349721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 820157886839794376509525 9611225236403840349721)
            ·
              rfl

theorem cell21_1137106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 8].length) (baseStart_1137106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137106 prefixEnd_1137106 := by exact prefixLift 1137106
  have htrace : WordTrace (prefixWord ++ tailWord_1137106) baseStart_1137106 baseEnd_1137106 := by
    simpa [prefixWord, tailWord_1137106, baseEnd_1137106] using wordTrace_append hprefix tailTrace_1137106
  have hstable : (prefixWord ++ tailWord_1137106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137106).length < 2 ^ (prefixWord ++ tailWord_1137106).sum := by decide
  have hdescent : baseEnd_1137106 < baseStart_1137106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137120 : List Nat := [2, 1, 1, 3, 1, 1, 5, 4, 3]
def baseStart_1137120 : Nat := 118140960795 + 1137120 * 2 ^ 59
def prefixEnd_1137120 : Nat := 4983230072969 + 3 ^ 40 * 1137120 * 2
def baseEnd_1137120 : Nat := 259506276373642776209105

theorem tailTrace_1137120 : CollatzResearch.WordTrace tailWord_1137120 prefixEnd_1137120 259506276373642776209105 := by
  unfold tailWord_1137120
  simp only [CollatzResearch.WordTrace]
  refine ⟨20737086820207959739844407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27649449093610612986459209 20737086820207959739844407)
  ·
    refine ⟨31105630230311939609766611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20737086820207959739844407 31105630230311939609766611)
    ·
      refine ⟨46658445345467909414649917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31105630230311939609766611 46658445345467909414649917)
      ·
        refine ⟨17496917004550466030493719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46658445345467909414649917 17496917004550466030493719)
        ·
          refine ⟨26245375506825699045740579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17496917004550466030493719 26245375506825699045740579)
          ·
            refine ⟨39368063260238548568610869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26245375506825699045740579 39368063260238548568610869)
            ·
              refine ⟨3690755930647363928307269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39368063260238548568610869 3690755930647363928307269)
              ·
                refine ⟨692016736996380736557613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3690755930647363928307269 692016736996380736557613)
                ·
                  refine ⟨259506276373642776209105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692016736996380736557613 259506276373642776209105)
                  ·
                    rfl

theorem cell21_1137120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 3].length) (baseStart_1137120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137120 prefixEnd_1137120 := by exact prefixLift 1137120
  have htrace : WordTrace (prefixWord ++ tailWord_1137120) baseStart_1137120 baseEnd_1137120 := by
    simpa [prefixWord, tailWord_1137120, baseEnd_1137120] using wordTrace_append hprefix tailTrace_1137120
  have hstable : (prefixWord ++ tailWord_1137120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137120).length < 2 ^ (prefixWord ++ tailWord_1137120).sum := by decide
  have hdescent : baseEnd_1137120 < baseStart_1137120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137213 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 3]
def baseStart_1137213 : Nat := 118140960795 + 1137213 * 2 ^ 59
def prefixEnd_1137213 : Nat := 4983230072969 + 3 ^ 40 * 1137213 * 2
def baseEnd_1137213 : Nat := 259527500240695281158915

theorem tailTrace_1137213 : CollatzResearch.WordTrace tailWord_1137213 prefixEnd_1137213 259527500240695281158915 := by
  unfold tailWord_1137213
  simp only [CollatzResearch.WordTrace]
  refine ⟨41477565629078996362824293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27651710419385997575216195 41477565629078996362824293)
  ·
    refine ⟨7777043555452311818029555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41477565629078996362824293 7777043555452311818029555)
    ·
      refine ⟨11665565333178467727044333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7777043555452311818029555 11665565333178467727044333)
      ·
        refine ⟨4374586999941925397641625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11665565333178467727044333 4374586999941925397641625)
        ·
          refine ⟨3280940249956444048231219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4374586999941925397641625 3280940249956444048231219)
          ·
            refine ⟨4921410374934666072346829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3280940249956444048231219 4921410374934666072346829)
            ·
              refine ⟨1845528890600499777130061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4921410374934666072346829 1845528890600499777130061)
              ·
                refine ⟨692073333975187416423773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1845528890600499777130061 692073333975187416423773)
                ·
                  refine ⟨259527500240695281158915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692073333975187416423773 259527500240695281158915)
                  ·
                    rfl

theorem cell21_1137213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_1137213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137213 prefixEnd_1137213 := by exact prefixLift 1137213
  have htrace : WordTrace (prefixWord ++ tailWord_1137213) baseStart_1137213 baseEnd_1137213 := by
    simpa [prefixWord, tailWord_1137213, baseEnd_1137213] using wordTrace_append hprefix tailTrace_1137213
  have hstable : (prefixWord ++ tailWord_1137213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137213).length < 2 ^ (prefixWord ++ tailWord_1137213).sum := by decide
  have hdescent : baseEnd_1137213 < baseStart_1137213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137334 : List Nat := [5, 1, 3, 1, 2, 1, 8]
def baseStart_1137334 : Nat := 118140960795 + 1137334 * 2 ^ 59
def prefixEnd_1137334 : Nat := 4983230072969 + 3 ^ 40 * 1137334 * 2
def baseEnd_1137334 : Nat := 28839457121025106626889

theorem tailTrace_1137334 : CollatzResearch.WordTrace tailWord_1137334 prefixEnd_1137334 28839457121025106626889 := by
  unfold tailWord_1137334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2592623678852539626748691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 27654652574427089351986037 2592623678852539626748691)
  ·
    refine ⟨3888935518278809440123037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2592623678852539626748691 3888935518278809440123037)
    ·
      refine ⟨1458350819354553540046139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3888935518278809440123037 1458350819354553540046139)
      ·
        refine ⟨2187526229031830310069209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458350819354553540046139 2187526229031830310069209)
        ·
          refine ⟨1640644671773872732551907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2187526229031830310069209 1640644671773872732551907)
          ·
            refine ⟨2460967007660809098827861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1640644671773872732551907 2460967007660809098827861)
            ·
              refine ⟨28839457121025106626889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2460967007660809098827861 28839457121025106626889)
              ·
                rfl

theorem cell21_1137334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 8].length) (baseStart_1137334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137334 prefixEnd_1137334 := by exact prefixLift 1137334
  have htrace : WordTrace (prefixWord ++ tailWord_1137334) baseStart_1137334 baseEnd_1137334 := by
    simpa [prefixWord, tailWord_1137334, baseEnd_1137334] using wordTrace_append hprefix tailTrace_1137334
  have hstable : (prefixWord ++ tailWord_1137334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137334).length < 2 ^ (prefixWord ++ tailWord_1137334).sum := by decide
  have hdescent : baseEnd_1137334 < baseStart_1137334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137348 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 5]
def baseStart_1137348 : Nat := 118140960795 + 1137348 * 2 ^ 59
def prefixEnd_1137348 : Nat := 4983230072969 + 3 ^ 40 * 1137348 * 2
def baseEnd_1137348 : Nat := 259558309079965046408639

theorem tailTrace_1137348 : CollatzResearch.WordTrace tailWord_1137348 prefixEnd_1137348 259558309079965046408639 := by
  unfold tailWord_1137348
  simp only [CollatzResearch.WordTrace]
  refine ⟨20741244741794957209494349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27654992989059942945992465 20741244741794957209494349)
  ·
    refine ⟨7777966778173108953560381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20741244741794957209494349 7777966778173108953560381)
    ·
      refine ⟨2916737541814915857585143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7777966778173108953560381 2916737541814915857585143)
      ·
        refine ⟨4375106312722373786377715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2916737541814915857585143 4375106312722373786377715)
        ·
          refine ⟨6562659469083560679566573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4375106312722373786377715 6562659469083560679566573)
          ·
            refine ⟨2460997300906335254837465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6562659469083560679566573 2460997300906335254837465)
            ·
              refine ⟨1845747975679751441128099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2460997300906335254837465 1845747975679751441128099)
              ·
                refine ⟨2768621963519627161692149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1845747975679751441128099 2768621963519627161692149)
                ·
                  refine ⟨259558309079965046408639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2768621963519627161692149 259558309079965046408639)
                  ·
                    rfl

theorem cell21_1137348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_1137348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137348 prefixEnd_1137348 := by exact prefixLift 1137348
  have htrace : WordTrace (prefixWord ++ tailWord_1137348) baseStart_1137348 baseEnd_1137348 := by
    simpa [prefixWord, tailWord_1137348, baseEnd_1137348] using wordTrace_append hprefix tailTrace_1137348
  have hstable : (prefixWord ++ tailWord_1137348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137348).length < 2 ^ (prefixWord ++ tailWord_1137348).sum := by decide
  have hdescent : baseEnd_1137348 < baseStart_1137348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137545 : List Nat := [1, 2, 1, 1, 5, 4, 2, 5]
def baseStart_1137545 : Nat := 118140960795 + 1137545 * 2 ^ 59
def prefixEnd_1137545 : Nat := 4983230072969 + 3 ^ 40 * 1137545 * 2
def baseEnd_1137545 : Nat := 86534422387978827208301

theorem tailTrace_1137545 : CollatzResearch.WordTrace tailWord_1137545 prefixEnd_1137545 86534422387978827208301 := by
  unfold tailWord_1137545
  simp only [CollatzResearch.WordTrace]
  refine ⟨41489674663876217063910089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27659783109250811375940059 41489674663876217063910089)
  ·
    refine ⟨31117255997907162797932567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41489674663876217063910089 31117255997907162797932567)
    ·
      refine ⟨46675883996860744196898851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31117255997907162797932567 46675883996860744196898851)
      ·
        refine ⟨70013825995291116295348277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46675883996860744196898851 70013825995291116295348277)
        ·
          refine ⟨6563796187058542152688901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70013825995291116295348277 6563796187058542152688901)
          ·
            refine ⟨1230711785073476653629169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6563796187058542152688901 1230711785073476653629169)
            ·
              refine ⟨923033838805107490221877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230711785073476653629169 923033838805107490221877)
              ·
                refine ⟨86534422387978827208301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 923033838805107490221877 86534422387978827208301)
                ·
                  rfl

theorem cell21_1137545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 5].length) (baseStart_1137545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137545 prefixEnd_1137545 := by exact prefixLift 1137545
  have htrace : WordTrace (prefixWord ++ tailWord_1137545) baseStart_1137545 baseEnd_1137545 := by
    simpa [prefixWord, tailWord_1137545, baseEnd_1137545] using wordTrace_append hprefix tailTrace_1137545
  have hstable : (prefixWord ++ tailWord_1137545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137545).length < 2 ^ (prefixWord ++ tailWord_1137545).sum := by decide
  have hdescent : baseEnd_1137545 < baseStart_1137545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137725 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 6]
def baseStart_1137725 : Nat := 118140960795 + 1137725 * 2 ^ 59
def prefixEnd_1137725 : Nat := 4983230072969 + 3 ^ 40 * 1137725 * 2
def baseEnd_1137725 : Nat := 259644345616296168624535

theorem tailTrace_1137725 : CollatzResearch.WordTrace tailWord_1137725 prefixEnd_1137725 259644345616296168624535 := by
  unfold tailWord_1137725
  simp only [CollatzResearch.WordTrace]
  refine ⟨41496239803224107805462629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27664159868816071870308419 41496239803224107805462629)
  ·
    refine ⟨7780544963104520213524243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41496239803224107805462629 7780544963104520213524243)
    ·
      refine ⟨11670817444656780320286365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7780544963104520213524243 11670817444656780320286365)
      ·
        refine ⟨4376556541746292620107387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11670817444656780320286365 4376556541746292620107387)
        ·
          refine ⟨6564834812619438930161081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376556541746292620107387 6564834812619438930161081)
          ·
            refine ⟨4923626109464579197620811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6564834812619438930161081 4923626109464579197620811)
            ·
              refine ⟨7385439164196868796431217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923626109464579197620811 7385439164196868796431217)
              ·
                refine ⟨5539079373147651597323413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7385439164196868796431217 5539079373147651597323413)
                ·
                  refine ⟨259644345616296168624535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5539079373147651597323413 259644345616296168624535)
                  ·
                    rfl

theorem cell21_1137725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_1137725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137725 prefixEnd_1137725 := by exact prefixLift 1137725
  have htrace : WordTrace (prefixWord ++ tailWord_1137725) baseStart_1137725 baseEnd_1137725 := by
    simpa [prefixWord, tailWord_1137725, baseEnd_1137725] using wordTrace_append hprefix tailTrace_1137725
  have hstable : (prefixWord ++ tailWord_1137725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137725).length < 2 ^ (prefixWord ++ tailWord_1137725).sum := by decide
  have hdescent : baseEnd_1137725 < baseStart_1137725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137756 : List Nat := [2, 2, 4, 1, 1, 1, 4, 6]
def baseStart_1137756 : Nat := 118140960795 + 1137756 * 2 ^ 59
def prefixEnd_1137756 : Nat := 4983230072969 + 3 ^ 40 * 1137756 * 2
def baseEnd_1137756 : Nat := 86550473412882334535935

theorem tailTrace_1137756 : CollatzResearch.WordTrace tailWord_1137756 prefixEnd_1137756 86550473412882334535935 := by
  unfold tailWord_1137756
  simp only [CollatzResearch.WordTrace]
  refine ⟨20748685233055900049920561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27664913644074533399894081 20748685233055900049920561)
  ·
    refine ⟨15561513924791925037440421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20748685233055900049920561 15561513924791925037440421)
    ·
      refine ⟨2917783860898485944520079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15561513924791925037440421 2917783860898485944520079)
      ·
        refine ⟨4376675791347728916780119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2917783860898485944520079 4376675791347728916780119)
        ·
          refine ⟨6565013687021593375170179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4376675791347728916780119 6565013687021593375170179)
          ·
            refine ⟨9847520530532390062755269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6565013687021593375170179 9847520530532390062755269)
            ·
              refine ⟨1846410099474823136766613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9847520530532390062755269 1846410099474823136766613)
              ·
                refine ⟨86550473412882334535935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1846410099474823136766613 86550473412882334535935)
                ·
                  rfl

theorem cell21_1137756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_1137756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137756 prefixEnd_1137756 := by exact prefixLift 1137756
  have htrace : WordTrace (prefixWord ++ tailWord_1137756) baseStart_1137756 baseEnd_1137756 := by
    simpa [prefixWord, tailWord_1137756, baseEnd_1137756] using wordTrace_append hprefix tailTrace_1137756
  have hstable : (prefixWord ++ tailWord_1137756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137756).length < 2 ^ (prefixWord ++ tailWord_1137756).sum := by decide
  have hdescent : baseEnd_1137756 < baseStart_1137756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137784 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_1137784 : Nat := 118140960795 + 1137784 * 2 ^ 59
def prefixEnd_1137784 : Nat := 4983230072969 + 3 ^ 40 * 1137784 * 2
def baseEnd_1137784 : Nat := 259657810220125177141081

theorem tailTrace_1137784 : CollatzResearch.WordTrace tailWord_1137784 prefixEnd_1137784 259657810220125177141081 := by
  unfold tailWord_1137784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20749195855005180440930203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27665594473340240587906937 20749195855005180440930203)
  ·
    refine ⟨31123793782507770661395305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20749195855005180440930203 31123793782507770661395305)
    ·
      refine ⟨23342845336880827996046479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31123793782507770661395305 23342845336880827996046479)
      ·
        refine ⟨35014268005321241994069719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23342845336880827996046479 35014268005321241994069719)
        ·
          refine ⟨52521402007981862991104579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35014268005321241994069719 52521402007981862991104579)
          ·
            refine ⟨78782103011972794486656869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52521402007981862991104579 78782103011972794486656869)
            ·
              refine ⟨14771644314744898966248163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78782103011972794486656869 14771644314744898966248163)
              ·
                refine ⟨22157466472117348449372245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14771644314744898966248163 22157466472117348449372245)
                ·
                  refine ⟨259657810220125177141081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22157466472117348449372245 259657810220125177141081)
                  ·
                    rfl

theorem cell21_1137784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_1137784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137784 prefixEnd_1137784 := by exact prefixLift 1137784
  have htrace : WordTrace (prefixWord ++ tailWord_1137784) baseStart_1137784 baseEnd_1137784 := by
    simpa [prefixWord, tailWord_1137784, baseEnd_1137784] using wordTrace_append hprefix tailTrace_1137784
  have hstable : (prefixWord ++ tailWord_1137784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137784).length < 2 ^ (prefixWord ++ tailWord_1137784).sum := by decide
  have hdescent : baseEnd_1137784 < baseStart_1137784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137790 : List Nat := [4, 2, 4, 1, 1, 9]
def baseStart_1137790 : Nat := 118140960795 + 1137790 * 2 ^ 59
def prefixEnd_1137790 : Nat := 4983230072969 + 3 ^ 40 * 1137790 * 2
def baseEnd_1137790 : Nat := 9617006648217425927447

theorem tailTrace_1137790 : CollatzResearch.WordTrace tailWord_1137790 prefixEnd_1137790 9617006648217425927447 := by
  unfold tailWord_1137790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5187326318498577988322353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27665740365325749271052549 5187326318498577988322353)
  ·
    refine ⟨3890494738873933491241765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5187326318498577988322353 3890494738873933491241765)
    ·
      refine ⟨729467763538862529607831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3890494738873933491241765 729467763538862529607831)
      ·
        refine ⟨1094201645308293794411747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 729467763538862529607831 1094201645308293794411747)
        ·
          refine ⟨1641302467962440691617621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094201645308293794411747 1641302467962440691617621)
          ·
            refine ⟨9617006648217425927447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1641302467962440691617621 9617006648217425927447)
            ·
              rfl

theorem cell21_1137790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 9].length) (baseStart_1137790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137790 prefixEnd_1137790 := by exact prefixLift 1137790
  have htrace : WordTrace (prefixWord ++ tailWord_1137790) baseStart_1137790 baseEnd_1137790 := by
    simpa [prefixWord, tailWord_1137790, baseEnd_1137790] using wordTrace_append hprefix tailTrace_1137790
  have hstable : (prefixWord ++ tailWord_1137790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137790).length < 2 ^ (prefixWord ++ tailWord_1137790).sum := by decide
  have hdescent : baseEnd_1137790 < baseStart_1137790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137801 : List Nat := [1, 2, 1, 1, 4, 3, 1, 4, 4]
def baseStart_1137801 : Nat := 118140960795 + 1137801 * 2 ^ 59
def prefixEnd_1137801 : Nat := 4983230072969 + 3 ^ 40 * 1137801 * 2
def baseEnd_1137801 : Nat := 259661689851736925357713

theorem tailTrace_1137801 : CollatzResearch.WordTrace tailWord_1137801 prefixEnd_1137801 259661689851736925357713 := by
  unfold tailWord_1137801
  simp only [CollatzResearch.WordTrace]
  refine ⟨41499011750948772785229257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27666007833965848523486171 41499011750948772785229257)
  ·
    refine ⟨31124258813211579588921943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41499011750948772785229257 31124258813211579588921943)
    ·
      refine ⟨46686388219817369383382915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31124258813211579588921943 46686388219817369383382915)
      ·
        refine ⟨70029582329726054075074373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46686388219817369383382915 70029582329726054075074373)
        ·
          refine ⟨13130546686823635139076445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70029582329726054075074373 13130546686823635139076445)
          ·
            refine ⟨4923955007558863177153667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13130546686823635139076445 4923955007558863177153667)
            ·
              refine ⟨7385932511338294765730501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4923955007558863177153667 7385932511338294765730501)
              ·
                refine ⟨1384862345875930268574469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7385932511338294765730501 1384862345875930268574469)
                ·
                  refine ⟨259661689851736925357713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384862345875930268574469 259661689851736925357713)
                  ·
                    rfl

theorem cell21_1137801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 4].length) (baseStart_1137801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137801 prefixEnd_1137801 := by exact prefixLift 1137801
  have htrace : WordTrace (prefixWord ++ tailWord_1137801) baseStart_1137801 baseEnd_1137801 := by
    simpa [prefixWord, tailWord_1137801, baseEnd_1137801] using wordTrace_append hprefix tailTrace_1137801
  have hstable : (prefixWord ++ tailWord_1137801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137801).length < 2 ^ (prefixWord ++ tailWord_1137801).sum := by decide
  have hdescent : baseEnd_1137801 < baseStart_1137801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137818 : List Nat := [3, 1, 1, 5, 1, 1, 2, 3, 4]
def baseStart_1137818 : Nat := 118140960795 + 1137818 * 2 ^ 59
def prefixEnd_1137818 : Nat := 4983230072969 + 3 ^ 40 * 1137818 * 2
def baseEnd_1137818 : Nat := 259665569483348673574345

theorem tailTrace_1137818 : CollatzResearch.WordTrace tailWord_1137818 prefixEnd_1137818 259665569483348673574345 := by
  unfold tailWord_1137818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10374907947971796172149527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27666421194591456459065405 10374907947971796172149527)
  ·
    refine ⟨15562361921957694258224291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10374907947971796172149527 15562361921957694258224291)
    ·
      refine ⟨23343542882936541387336437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15562361921957694258224291 23343542882936541387336437)
      ·
        refine ⟨2188457145275300755062791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23343542882936541387336437 2188457145275300755062791)
        ·
          refine ⟨3282685717912951132594187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2188457145275300755062791 3282685717912951132594187)
          ·
            refine ⟨4924028576869426698891281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3282685717912951132594187 4924028576869426698891281)
            ·
              refine ⟨3693021432652070024168461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4924028576869426698891281 3693021432652070024168461)
              ·
                refine ⟨1384883037244526259063173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3693021432652070024168461 1384883037244526259063173)
                ·
                  refine ⟨259665569483348673574345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384883037244526259063173 259665569483348673574345)
                  ·
                    rfl

theorem cell21_1137818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_1137818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137818 prefixEnd_1137818 := by exact prefixLift 1137818
  have htrace : WordTrace (prefixWord ++ tailWord_1137818) baseStart_1137818 baseEnd_1137818 := by
    simpa [prefixWord, tailWord_1137818, baseEnd_1137818] using wordTrace_append hprefix tailTrace_1137818
  have hstable : (prefixWord ++ tailWord_1137818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137818).length < 2 ^ (prefixWord ++ tailWord_1137818).sum := by decide
  have hdescent : baseEnd_1137818 < baseStart_1137818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137869 : List Nat := [1, 6, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1137869 : Nat := 118140960795 + 1137869 * 2 ^ 59
def prefixEnd_1137869 : Nat := 4983230072969 + 3 ^ 40 * 1137869 * 2
def baseEnd_1137869 : Nat := 259677208378183918224241

theorem tailTrace_1137869 : CollatzResearch.WordTrace tailWord_1137869 prefixEnd_1137869 259677208378183918224241 := by
  unfold tailWord_1137869
  simp only [CollatzResearch.WordTrace]
  refine ⟨41501491914702420398704661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27667661276468280265803107 41501491914702420398704661)
  ·
    refine ⟨1945382433501675956189281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41501491914702420398704661 1945382433501675956189281)
    ·
      refine ⟨1459036825126256967141961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1945382433501675956189281 1459036825126256967141961)
      ·
        refine ⟨1094277618844692725356471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1459036825126256967141961 1094277618844692725356471)
        ·
          refine ⟨1641416428267039088034707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094277618844692725356471 1641416428267039088034707)
          ·
            refine ⟨2462124642400558632052061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641416428267039088034707 2462124642400558632052061)
            ·
              refine ⟨923296740900209487019523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2462124642400558632052061 923296740900209487019523)
              ·
                refine ⟨1384945111350314230529285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923296740900209487019523 1384945111350314230529285)
                ·
                  refine ⟨259677208378183918224241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1384945111350314230529285 259677208378183918224241)
                  ·
                    rfl

theorem cell21_1137869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1137869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137869 prefixEnd_1137869 := by exact prefixLift 1137869
  have htrace : WordTrace (prefixWord ++ tailWord_1137869) baseStart_1137869 baseEnd_1137869 := by
    simpa [prefixWord, tailWord_1137869, baseEnd_1137869] using wordTrace_append hprefix tailTrace_1137869
  have hstable : (prefixWord ++ tailWord_1137869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137869).length < 2 ^ (prefixWord ++ tailWord_1137869).sum := by decide
  have hdescent : baseEnd_1137869 < baseStart_1137869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137928 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_1137928 : Nat := 118140960795 + 1137928 * 2 ^ 59
def prefixEnd_1137928 : Nat := 4983230072969 + 3 ^ 40 * 1137928 * 2
def baseEnd_1137928 : Nat := 259690672982012926740787

theorem tailTrace_1137928 : CollatzResearch.WordTrace tailWord_1137928 prefixEnd_1137928 259690672982012926740787 := by
  unfold tailWord_1137928
  simp only [CollatzResearch.WordTrace]
  refine ⟨20751821910744336737551219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27669095880992448983401625 20751821910744336737551219)
  ·
    refine ⟨31127732866116505106326829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20751821910744336737551219 31127732866116505106326829)
    ·
      refine ⟨11672899824793689414872561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31127732866116505106326829 11672899824793689414872561)
      ·
        refine ⟨8754674868595267061154421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11672899824793689414872561 8754674868595267061154421)
        ·
          refine ⟨820750768930806286983227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8754674868595267061154421 820750768930806286983227)
          ·
            refine ⟨1231126153396209430474841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820750768930806286983227 1231126153396209430474841)
            ·
              refine ⟨923344615047157072856131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231126153396209430474841 923344615047157072856131)
              ·
                refine ⟨1385016922570735609284197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923344615047157072856131 1385016922570735609284197)
                ·
                  refine ⟨259690672982012926740787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1385016922570735609284197 259690672982012926740787)
                  ·
                    rfl

theorem cell21_1137928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_1137928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137928 prefixEnd_1137928 := by exact prefixLift 1137928
  have htrace : WordTrace (prefixWord ++ tailWord_1137928) baseStart_1137928 baseEnd_1137928 := by
    simpa [prefixWord, tailWord_1137928, baseEnd_1137928] using wordTrace_append hprefix tailTrace_1137928
  have hstable : (prefixWord ++ tailWord_1137928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137928).length < 2 ^ (prefixWord ++ tailWord_1137928).sum := by decide
  have hdescent : baseEnd_1137928 < baseStart_1137928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137970 : List Nat := [3, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1137970 : Nat := 118140960795 + 1137970 * 2 ^ 59
def prefixEnd_1137970 : Nat := 4983230072969 + 3 ^ 40 * 1137970 * 2
def baseEnd_1137970 : Nat := 259700257954230187040701

theorem tailTrace_1137970 : CollatzResearch.WordTrace tailWord_1137970 prefixEnd_1137970 259700257954230187040701 := by
  unfold tailWord_1137970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10376293921834128662032841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27670117124891009765420909 10376293921834128662032841)
  ·
    refine ⟨7782220441375596496524631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10376293921834128662032841 7782220441375596496524631)
    ·
      refine ⟨11673330662063394744786947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7782220441375596496524631 11673330662063394744786947)
      ·
        refine ⟨17509995993095092117180421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11673330662063394744786947 17509995993095092117180421)
        ·
          refine ⟨3283124248705329771971329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17509995993095092117180421 3283124248705329771971329)
          ·
            refine ⟨2462343186528997328978497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3283124248705329771971329 2462343186528997328978497)
            ·
              refine ⟨1846757389896747996733873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2462343186528997328978497 1846757389896747996733873)
              ·
                refine ⟨1385068042422560997550405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1846757389896747996733873 1385068042422560997550405)
                ·
                  refine ⟨259700257954230187040701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1385068042422560997550405 259700257954230187040701)
                  ·
                    rfl

theorem cell21_1137970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1137970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137970 prefixEnd_1137970 := by exact prefixLift 1137970
  have htrace : WordTrace (prefixWord ++ tailWord_1137970) baseStart_1137970 baseEnd_1137970 := by
    simpa [prefixWord, tailWord_1137970, baseEnd_1137970] using wordTrace_append hprefix tailTrace_1137970
  have hstable : (prefixWord ++ tailWord_1137970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137970).length < 2 ^ (prefixWord ++ tailWord_1137970).sum := by decide
  have hdescent : baseEnd_1137970 < baseStart_1137970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137973 : List Nat := [1, 3, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1137973 : Nat := 118140960795 + 1137973 * 2 ^ 59
def prefixEnd_1137973 : Nat := 4983230072969 + 3 ^ 40 * 1137973 * 2
def baseEnd_1137973 : Nat := 259700942595102848490695

theorem tailTrace_1137973 : CollatzResearch.WordTrace tailWord_1137973 prefixEnd_1137973 259700942595102848490695 := by
  unfold tailWord_1137973
  simp only [CollatzResearch.WordTrace]
  refine ⟨41505285106325646160490573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27670190070883764106993715 41505285106325646160490573)
  ·
    refine ⟨15564481914872117310183965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41505285106325646160490573 15564481914872117310183965)
    ·
      refine ⟨5836680718077043991318987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15564481914872117310183965 5836680718077043991318987)
      ·
        refine ⟨8755021077115565986978481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836680718077043991318987 8755021077115565986978481)
        ·
          refine ⟨6566265807836674490233861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8755021077115565986978481 6566265807836674490233861)
          ·
            refine ⟨1231174838969376466918849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6566265807836674490233861 1231174838969376466918849)
            ·
              refine ⟨923381129227032350189137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231174838969376466918849 923381129227032350189137)
              ·
                refine ⟨692535846920274262641853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923381129227032350189137 692535846920274262641853)
                ·
                  refine ⟨259700942595102848490695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692535846920274262641853 259700942595102848490695)
                  ·
                    rfl

theorem cell21_1137973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1137973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137973 prefixEnd_1137973 := by exact prefixLift 1137973
  have htrace : WordTrace (prefixWord ++ tailWord_1137973) baseStart_1137973 baseEnd_1137973 := by
    simpa [prefixWord, tailWord_1137973, baseEnd_1137973] using wordTrace_append hprefix tailTrace_1137973
  have hstable : (prefixWord ++ tailWord_1137973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137973).length < 2 ^ (prefixWord ++ tailWord_1137973).sum := by decide
  have hdescent : baseEnd_1137973 < baseStart_1137973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1137998 : List Nat := [4, 1, 1, 1, 1, 1, 5, 2, 5]
def baseStart_1137998 : Nat := 118140960795 + 1137998 * 2 ^ 59
def prefixEnd_1137998 : Nat := 4983230072969 + 3 ^ 40 * 1137998 * 2
def baseEnd_1137998 : Nat := 259706647935708360573977

theorem tailTrace_1137998 : CollatzResearch.WordTrace tailWord_1137998 prefixEnd_1137998 259706647935708360573977 := by
  unfold tailWord_1137998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188274616404384428768831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27670797954156716953433765 5188274616404384428768831)
  ·
    refine ⟨7782411924606576643153247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5188274616404384428768831 7782411924606576643153247)
    ·
      refine ⟨11673617886909864964729871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7782411924606576643153247 11673617886909864964729871)
      ·
        refine ⟨17510426830364797447094807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11673617886909864964729871 17510426830364797447094807)
        ·
          refine ⟨26265640245547196170642211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17510426830364797447094807 26265640245547196170642211)
          ·
            refine ⟨39398460368320794255963317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26265640245547196170642211 39398460368320794255963317)
            ·
              refine ⟨3693605659530074461496561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39398460368320794255963317 3693605659530074461496561)
              ·
                refine ⟨2770204244647555846122421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3693605659530074461496561 2770204244647555846122421)
                ·
                  refine ⟨259706647935708360573977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2770204244647555846122421 259706647935708360573977)
                  ·
                    rfl

theorem cell21_1137998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_1137998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1137998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1137998 prefixEnd_1137998 := by exact prefixLift 1137998
  have htrace : WordTrace (prefixWord ++ tailWord_1137998) baseStart_1137998 baseEnd_1137998 := by
    simpa [prefixWord, tailWord_1137998, baseEnd_1137998] using wordTrace_append hprefix tailTrace_1137998
  have hstable : (prefixWord ++ tailWord_1137998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1137998).length < 2 ^ (prefixWord ++ tailWord_1137998).sum := by decide
  have hdescent : baseEnd_1137998 < baseStart_1137998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1137998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138029 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 6]
def baseStart_1138029 : Nat := 118140960795 + 1138029 * 2 ^ 59
def prefixEnd_1138029 : Nat := 4983230072969 + 3 ^ 40 * 1138029 * 2
def baseEnd_1138029 : Nat := 259713722558059195557247

theorem tailTrace_1138029 : CollatzResearch.WordTrace tailWord_1138029 prefixEnd_1138029 259713722558059195557247 := by
  unfold tailWord_1138029
  simp only [CollatzResearch.WordTrace]
  refine ⟨41507327594122767724529141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27671551729415178483019427 41507327594122767724529141)
  ·
    refine ⟨3891311961949009474174607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41507327594122767724529141 3891311961949009474174607)
    ·
      refine ⟨5836967942923514211261911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3891311961949009474174607 5836967942923514211261911)
      ·
        refine ⟨8755451914385271316892867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5836967942923514211261911 8755451914385271316892867)
        ·
          refine ⟨13133177871577906975339301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8755451914385271316892867 13133177871577906975339301)
          ·
            refine ⟨2462470850920857557876119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13133177871577906975339301 2462470850920857557876119)
            ·
              refine ⟨3693706276381286336814179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2462470850920857557876119 3693706276381286336814179)
              ·
                refine ⟨5540559414571929505221269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3693706276381286336814179 5540559414571929505221269)
                ·
                  refine ⟨259713722558059195557247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5540559414571929505221269 259713722558059195557247)
                  ·
                    rfl

theorem cell21_1138029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_1138029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138029 prefixEnd_1138029 := by exact prefixLift 1138029
  have htrace : WordTrace (prefixWord ++ tailWord_1138029) baseStart_1138029 baseEnd_1138029 := by
    simpa [prefixWord, tailWord_1138029, baseEnd_1138029] using wordTrace_append hprefix tailTrace_1138029
  have hstable : (prefixWord ++ tailWord_1138029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138029).length < 2 ^ (prefixWord ++ tailWord_1138029).sum := by decide
  have hdescent : baseEnd_1138029 < baseStart_1138029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138066 : List Nat := [3, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_1138066 : Nat := 118140960795 + 1138066 * 2 ^ 59
def prefixEnd_1138066 : Nat := 4983230072969 + 3 ^ 40 * 1138066 * 2
def baseEnd_1138066 : Nat := 259722166462155353440505

theorem tailTrace_1138066 : CollatzResearch.WordTrace tailWord_1138066 prefixEnd_1138066 259722166462155353440505 := by
  unfold tailWord_1138066
  simp only [CollatzResearch.WordTrace]
  refine ⟨10377169273747180760906513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27672451396659148695750701 10377169273747180760906513)
  ·
    refine ⟨7782876955310385570679885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10377169273747180760906513 7782876955310385570679885)
    ·
      refine ⟨2918578858241394589004957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7782876955310385570679885 2918578858241394589004957)
      ·
        refine ⟨1094467071840522970876859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2918578858241394589004957 1094467071840522970876859)
        ·
          refine ⟨1641700607760784456315289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1094467071840522970876859 1641700607760784456315289)
          ·
            refine ⟨1231275455820588342236467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1641700607760784456315289 1231275455820588342236467)
            ·
              refine ⟨1846913183730882513354701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231275455820588342236467 1846913183730882513354701)
              ·
                refine ⟨692592443899080942508013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1846913183730882513354701 692592443899080942508013)
                ·
                  refine ⟨259722166462155353440505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692592443899080942508013 259722166462155353440505)
                  ·
                    rfl

theorem cell21_1138066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_1138066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138066 prefixEnd_1138066 := by exact prefixLift 1138066
  have htrace : WordTrace (prefixWord ++ tailWord_1138066) baseStart_1138066 baseEnd_1138066 := by
    simpa [prefixWord, tailWord_1138066, baseEnd_1138066] using wordTrace_append hprefix tailTrace_1138066
  have hstable : (prefixWord ++ tailWord_1138066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138066).length < 2 ^ (prefixWord ++ tailWord_1138066).sum := by decide
  have hdescent : baseEnd_1138066 < baseStart_1138066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138246 : List Nat := [6, 1, 1, 1, 4, 1, 7]
def baseStart_1138246 : Nat := 118140960795 + 1138246 * 2 ^ 59
def prefixEnd_1138246 : Nat := 4983230072969 + 3 ^ 40 * 1138246 * 2
def baseEnd_1138246 : Nat := 28862582768279448937793

theorem tailTrace_1138246 : CollatzResearch.WordTrace tailWord_1138246 prefixEnd_1138246 28862582768279448937793 := by
  unfold tailWord_1138246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1297351319823019180786831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 27676828156224409190119061 1297351319823019180786831)
  ·
    refine ⟨1946026979734528771180247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1297351319823019180786831 1946026979734528771180247)
    ·
      refine ⟨2919040469601793156770371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1946026979734528771180247 2919040469601793156770371)
      ·
        refine ⟨4378560704402689735155557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2919040469601793156770371 4378560704402689735155557)
        ·
          refine ⟨820980132075504325341667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4378560704402689735155557 820980132075504325341667)
          ·
            refine ⟨1231470198113256488012501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820980132075504325341667 1231470198113256488012501)
            ·
              refine ⟨28862582768279448937793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1231470198113256488012501 28862582768279448937793)
              ·
                rfl

theorem cell21_1138246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 7].length) (baseStart_1138246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138246 prefixEnd_1138246 := by exact prefixLift 1138246
  have htrace : WordTrace (prefixWord ++ tailWord_1138246) baseStart_1138246 baseEnd_1138246 := by
    simpa [prefixWord, tailWord_1138246, baseEnd_1138246] using wordTrace_append hprefix tailTrace_1138246
  have hstable : (prefixWord ++ tailWord_1138246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138246).length < 2 ^ (prefixWord ++ tailWord_1138246).sum := by decide
  have hdescent : baseEnd_1138246 < baseStart_1138246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138260 : List Nat := [2, 4, 1, 1, 1, 2, 5, 2, 3]
def baseStart_1138260 : Nat := 118140960795 + 1138260 * 2 ^ 59
def prefixEnd_1138260 : Nat := 4983230072969 + 3 ^ 40 * 1138260 * 2
def baseEnd_1138260 : Nat := 259766439905254127206775

theorem tailTrace_1138260 : CollatzResearch.WordTrace tailWord_1138260 prefixEnd_1138260 259766439905254127206775 := by
  unfold tailWord_1138260
  simp only [CollatzResearch.WordTrace]
  refine ⟨20757876428142947088094117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27677168570857262784125489 20757876428142947088094117)
  ·
    refine ⟨3892101830276802579017647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20757876428142947088094117 3892101830276802579017647)
    ·
      refine ⟨5838152745415203868526471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3892101830276802579017647 5838152745415203868526471)
      ·
        refine ⟨8757229118122805802789707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5838152745415203868526471 8757229118122805802789707)
        ·
          refine ⟨13135843677184208704184561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8757229118122805802789707 13135843677184208704184561)
          ·
            refine ⟨9851882757888156528138421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13135843677184208704184561 9851882757888156528138421)
            ·
              refine ⟨923614008552014674512977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9851882757888156528138421 923614008552014674512977)
              ·
                refine ⟨692710506414011005884733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923614008552014674512977 692710506414011005884733)
                ·
                  refine ⟨259766439905254127206775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692710506414011005884733 259766439905254127206775)
                  ·
                    rfl

theorem cell21_1138260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_1138260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138260 prefixEnd_1138260 := by exact prefixLift 1138260
  have htrace : WordTrace (prefixWord ++ tailWord_1138260) baseStart_1138260 baseEnd_1138260 := by
    simpa [prefixWord, tailWord_1138260, baseEnd_1138260] using wordTrace_append hprefix tailTrace_1138260
  have hstable : (prefixWord ++ tailWord_1138260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138260).length < 2 ^ (prefixWord ++ tailWord_1138260).sum := by decide
  have hdescent : baseEnd_1138260 < baseStart_1138260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138451 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 8]
def baseStart_1138451 : Nat := 118140960795 + 1138451 * 2 ^ 59
def prefixEnd_1138451 : Nat := 4983230072969 + 3 ^ 40 * 1138451 * 2
def baseEnd_1138451 : Nat := 259810028707480239523051

theorem tailTrace_1138451 : CollatzResearch.WordTrace tailWord_1138451 prefixEnd_1138451 259810028707480239523051 := by
  unfold tailWord_1138451
  simp only [CollatzResearch.WordTrace]
  refine ⟨41522719198593933796391207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27681812799062622530927471 41522719198593933796391207)
  ·
    refine ⟨62284078797890900694586811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41522719198593933796391207 62284078797890900694586811)
    ·
      refine ⟨93426118196836351041880217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62284078797890900694586811 93426118196836351041880217)
      ·
        refine ⟨70069588647627263281410163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93426118196836351041880217 70069588647627263281410163)
        ·
          refine ⟨105104382971440894922115245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70069588647627263281410163 105104382971440894922115245)
          ·
            refine ⟨39414143614290335595793217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105104382971440894922115245 39414143614290335595793217)
            ·
              refine ⟨29560607710717751696844913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39414143614290335595793217 29560607710717751696844913)
              ·
                refine ⟨22170455783038313772633685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29560607710717751696844913 22170455783038313772633685)
                ·
                  refine ⟨259810028707480239523051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22170455783038313772633685 259810028707480239523051)
                  ·
                    rfl

theorem cell21_1138451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 8].length) (baseStart_1138451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138451 prefixEnd_1138451 := by exact prefixLift 1138451
  have htrace : WordTrace (prefixWord ++ tailWord_1138451) baseStart_1138451 baseEnd_1138451 := by
    simpa [prefixWord, tailWord_1138451, baseEnd_1138451] using wordTrace_append hprefix tailTrace_1138451
  have hstable : (prefixWord ++ tailWord_1138451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138451).length < 2 ^ (prefixWord ++ tailWord_1138451).sum := by decide
  have hdescent : baseEnd_1138451 < baseStart_1138451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138482 : List Nat := [3, 2, 1, 1, 3, 11]
def baseStart_1138482 : Nat := 118140960795 + 1138482 * 2 ^ 59
def prefixEnd_1138482 : Nat := 4983230072969 + 3 ^ 40 * 1138482 * 2
def baseEnd_1138482 : Nat := 9622855678882632389123

theorem tailTrace_1138482 : CollatzResearch.WordTrace tailWord_1138482 prefixEnd_1138482 9622855678882632389123 := by
  unfold tailWord_1138482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10380962465370406522692425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27682566574321084060513133 10380962465370406522692425)
  ·
    refine ⟨7785721849027804892019319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10380962465370406522692425 7785721849027804892019319)
    ·
      refine ⟨11678582773541707338028979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7785721849027804892019319 11678582773541707338028979)
      ·
        refine ⟨17517874160312561007043469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11678582773541707338028979 17517874160312561007043469)
        ·
          refine ⟨6569202810117210377641301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17517874160312561007043469 6569202810117210377641301)
          ·
            refine ⟨9622855678882632389123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6569202810117210377641301 9622855678882632389123)
            ·
              rfl

theorem cell21_1138482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 11].length) (baseStart_1138482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138482 prefixEnd_1138482 := by exact prefixLift 1138482
  have htrace : WordTrace (prefixWord ++ tailWord_1138482) baseStart_1138482 baseEnd_1138482 := by
    simpa [prefixWord, tailWord_1138482, baseEnd_1138482] using wordTrace_append hprefix tailTrace_1138482
  have hstable : (prefixWord ++ tailWord_1138482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138482).length < 2 ^ (prefixWord ++ tailWord_1138482).sum := by decide
  have hdescent : baseEnd_1138482 < baseStart_1138482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138488 : List Nat := [2, 1, 2, 1, 3, 5, 2, 2, 3]
def baseStart_1138488 : Nat := 118140960795 + 1138488 * 2 ^ 59
def prefixEnd_1138488 : Nat := 4983230072969 + 3 ^ 40 * 1138488 * 2
def baseEnd_1138488 : Nat := 259818472611576397406309

theorem tailTrace_1138488 : CollatzResearch.WordTrace tailWord_1138488 prefixEnd_1138488 259818472611576397406309 := by
  unfold tailWord_1138488
  simp only [CollatzResearch.WordTrace]
  refine ⟨20762034349729944557744059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27682712466306592743658745 20762034349729944557744059)
  ·
    refine ⟨31143051524594916836616089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20762034349729944557744059 31143051524594916836616089)
    ·
      refine ⟨23357288643446187627462067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31143051524594916836616089 23357288643446187627462067)
      ·
        refine ⟨35035932965169281441193101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23357288643446187627462067 35035932965169281441193101)
        ·
          refine ⟨13138474861938480540447413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35035932965169281441193101 13138474861938480540447413)
          ·
            refine ⟨1231732018306732550666945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13138474861938480540447413 1231732018306732550666945)
            ·
              refine ⟨923799013730049413000209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231732018306732550666945 923799013730049413000209)
              ·
                refine ⟨692849260297537059750157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 923799013730049413000209 692849260297537059750157)
                ·
                  refine ⟨259818472611576397406309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 692849260297537059750157 259818472611576397406309)
                  ·
                    rfl

theorem cell21_1138488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 3].length) (baseStart_1138488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138488 prefixEnd_1138488 := by exact prefixLift 1138488
  have htrace : WordTrace (prefixWord ++ tailWord_1138488) baseStart_1138488 baseEnd_1138488 := by
    simpa [prefixWord, tailWord_1138488, baseEnd_1138488] using wordTrace_append hprefix tailTrace_1138488
  have hstable : (prefixWord ++ tailWord_1138488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138488).length < 2 ^ (prefixWord ++ tailWord_1138488).sum := by decide
  have hdescent : baseEnd_1138488 < baseStart_1138488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138499 : List Nat := [1, 1, 1, 3, 1, 7, 1, 6]
def baseStart_1138499 : Nat := 118140960795 + 1138499 * 2 ^ 59
def prefixEnd_1138499 : Nat := 4983230072969 + 3 ^ 40 * 1138499 * 2
def baseEnd_1138499 : Nat := 86606994320480940907651

theorem tailTrace_1138499 : CollatzResearch.WordTrace tailWord_1138499 prefixEnd_1138499 86606994320480940907651 := by
  unfold tailWord_1138499
  simp only [CollatzResearch.WordTrace]
  refine ⟨41524469902420037994138551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27682979934946691996092367 41524469902420037994138551)
  ·
    refine ⟨62286704853630056991207827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41524469902420037994138551 62286704853630056991207827)
    ·
      refine ⟨93430057280445085486811741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62286704853630056991207827 93430057280445085486811741)
      ·
        refine ⟨35036271480166907057554403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93430057280445085486811741 35036271480166907057554403)
        ·
          refine ⟨52554407220250360586331605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35036271480166907057554403 52554407220250360586331605)
          ·
            refine ⟨1231743919224617826242147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52554407220250360586331605 1231743919224617826242147)
            ·
              refine ⟨1847615878836926739363221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1231743919224617826242147 1847615878836926739363221)
              ·
                refine ⟨86606994320480940907651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1847615878836926739363221 86606994320480940907651)
                ·
                  rfl

theorem cell21_1138499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 6].length) (baseStart_1138499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138499 prefixEnd_1138499 := by exact prefixLift 1138499
  have htrace : WordTrace (prefixWord ++ tailWord_1138499) baseStart_1138499 baseEnd_1138499 := by
    simpa [prefixWord, tailWord_1138499, baseEnd_1138499] using wordTrace_append hprefix tailTrace_1138499
  have hstable : (prefixWord ++ tailWord_1138499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138499).length < 2 ^ (prefixWord ++ tailWord_1138499).sum := by decide
  have hdescent : baseEnd_1138499 < baseStart_1138499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138513 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_1138513 : Nat := 118140960795 + 1138513 * 2 ^ 59
def prefixEnd_1138513 : Nat := 4983230072969 + 3 ^ 40 * 1138513 * 2
def baseEnd_1138513 : Nat := 259824177952181909489591

theorem tailTrace_1138513 : CollatzResearch.WordTrace tailWord_1138513 prefixEnd_1138513 259824177952181909489591 := by
  unfold tailWord_1138513
  simp only [CollatzResearch.WordTrace]
  refine ⟨41524980524369318385148193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27683320349579545590098795 41524980524369318385148193)
  ·
    refine ⟨31143735393276988788861145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41524980524369318385148193 31143735393276988788861145)
    ·
      refine ⟨23357801544957741591645859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31143735393276988788861145 23357801544957741591645859)
      ·
        refine ⟨35036702317436612387468789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23357801544957741591645859 35036702317436612387468789)
        ·
          refine ⟨3284690842259682411325199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35036702317436612387468789 3284690842259682411325199)
          ·
            refine ⟨4927036263389523616987799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3284690842259682411325199 4927036263389523616987799)
            ·
              refine ⟨7390554395084285425481699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4927036263389523616987799 7390554395084285425481699)
              ·
                refine ⟨11085831592626428138222549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7390554395084285425481699 11085831592626428138222549)
                ·
                  refine ⟨259824177952181909489591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11085831592626428138222549 259824177952181909489591)
                  ·
                    rfl

theorem cell21_1138513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_1138513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138513 prefixEnd_1138513 := by exact prefixLift 1138513
  have htrace : WordTrace (prefixWord ++ tailWord_1138513) baseStart_1138513 baseEnd_1138513 := by
    simpa [prefixWord, tailWord_1138513, baseEnd_1138513] using wordTrace_append hprefix tailTrace_1138513
  have hstable : (prefixWord ++ tailWord_1138513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138513).length < 2 ^ (prefixWord ++ tailWord_1138513).sum := by decide
  have hdescent : baseEnd_1138513 < baseStart_1138513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138516 : List Nat := [2, 4, 1, 1, 3, 2, 3, 5]
def baseStart_1138516 : Nat := 118140960795 + 1138516 * 2 ^ 59
def prefixEnd_1138516 : Nat := 4983230072969 + 3 ^ 40 * 1138516 * 2
def baseEnd_1138516 : Nat := 86608287531018190313195

theorem tailTrace_1138516 : CollatzResearch.WordTrace tailWord_1138516 prefixEnd_1138516 86608287531018190313195 := by
  unfold tailWord_1138516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20762544971679224948753701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27683393295572299931671601 20762544971679224948753701)
  ·
    refine ⟨3892977182189854677891319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20762544971679224948753701 3892977182189854677891319)
    ·
      refine ⟨5839465773284782016836979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3892977182189854677891319 5839465773284782016836979)
      ·
        refine ⟨8759198659927173025255469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5839465773284782016836979 8759198659927173025255469)
        ·
          refine ⟨3284699497472689884470801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8759198659927173025255469 3284699497472689884470801)
          ·
            refine ⟨2463524623104517413353101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3284699497472689884470801 2463524623104517413353101)
            ·
              refine ⟨923821733664194030007413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2463524623104517413353101 923821733664194030007413)
              ·
                refine ⟨86608287531018190313195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 923821733664194030007413 86608287531018190313195)
                ·
                  rfl

theorem cell21_1138516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_1138516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138516 prefixEnd_1138516 := by exact prefixLift 1138516
  have htrace : WordTrace (prefixWord ++ tailWord_1138516) baseStart_1138516 baseEnd_1138516 := by
    simpa [prefixWord, tailWord_1138516, baseEnd_1138516] using wordTrace_append hprefix tailTrace_1138516
  have hstable : (prefixWord ++ tailWord_1138516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138516).length < 2 ^ (prefixWord ++ tailWord_1138516).sum := by decide
  have hdescent : baseEnd_1138516 < baseStart_1138516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138612 : List Nat := [2, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1138612 : Nat := 118140960795 + 1138612 * 2 ^ 59
def prefixEnd_1138612 : Nat := 4983230072969 + 3 ^ 40 * 1138612 * 2
def baseEnd_1138612 : Nat := 259846771100979737339389

theorem tailTrace_1138612 : CollatzResearch.WordTrace tailWord_1138612 prefixEnd_1138612 259846771100979737339389 := by
  unfold tailWord_1138612
  simp only [CollatzResearch.WordTrace]
  refine ⟨20764295675505329146501045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27685727567340438862001393 20764295675505329146501045)
  ·
    refine ⟨1946652719578624607484473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20764295675505329146501045 1946652719578624607484473)
    ·
      refine ⟨1459989539683968455613355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1946652719578624607484473 1459989539683968455613355)
      ·
        refine ⟨2189984309525952683420033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1459989539683968455613355 2189984309525952683420033)
        ·
          refine ⟨1642488232144464512565025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2189984309525952683420033 1642488232144464512565025)
          ·
            refine ⟨1231866174108348384423769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1642488232144464512565025 1231866174108348384423769)
            ·
              refine ⟨923899630581261288317827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1231866174108348384423769 923899630581261288317827)
              ·
                refine ⟨1385849445871891932476741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923899630581261288317827 1385849445871891932476741)
                ·
                  refine ⟨259846771100979737339389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1385849445871891932476741 259846771100979737339389)
                  ·
                    rfl

theorem cell21_1138612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1138612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138612 prefixEnd_1138612 := by exact prefixLift 1138612
  have htrace : WordTrace (prefixWord ++ tailWord_1138612) baseStart_1138612 baseEnd_1138612 := by
    simpa [prefixWord, tailWord_1138612, baseEnd_1138612] using wordTrace_append hprefix tailTrace_1138612
  have hstable : (prefixWord ++ tailWord_1138612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138612).length < 2 ^ (prefixWord ++ tailWord_1138612).sum := by decide
  have hdescent : baseEnd_1138612 < baseStart_1138612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138634 : List Nat := [3, 1, 2, 1, 2, 1, 4, 7]
def baseStart_1138634 : Nat := 118140960795 + 1138634 * 2 ^ 59
def prefixEnd_1138634 : Nat := 4983230072969 + 3 ^ 40 * 1138634 * 2
def baseEnd_1138634 : Nat := 86617263933570862657559

theorem tailTrace_1138634 : CollatzResearch.WordTrace tailWord_1138634 prefixEnd_1138634 86617263933570862657559 := by
  unfold tailWord_1138634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10382348439232739012575739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27686262504620637366868637 10382348439232739012575739)
  ·
    refine ⟨15573522658849108518863609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10382348439232739012575739 15573522658849108518863609)
    ·
      refine ⟨11680141994136831389147707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15573522658849108518863609 11680141994136831389147707)
      ·
        refine ⟨17520212991205247083721561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11680141994136831389147707 17520212991205247083721561)
        ·
          refine ⟨13140159743403935312791171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17520212991205247083721561 13140159743403935312791171)
          ·
            refine ⟨19710239615105902969186757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13140159743403935312791171 19710239615105902969186757)
            ·
              refine ⟨3695669927832356806722517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19710239615105902969186757 3695669927832356806722517)
              ·
                refine ⟨86617263933570862657559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3695669927832356806722517 86617263933570862657559)
                ·
                  rfl

theorem cell21_1138634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_1138634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138634 prefixEnd_1138634 := by exact prefixLift 1138634
  have htrace : WordTrace (prefixWord ++ tailWord_1138634) baseStart_1138634 baseEnd_1138634 := by
    simpa [prefixWord, tailWord_1138634, baseEnd_1138634] using wordTrace_append hprefix tailTrace_1138634
  have hstable : (prefixWord ++ tailWord_1138634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138634).length < 2 ^ (prefixWord ++ tailWord_1138634).sum := by decide
  have hdescent : baseEnd_1138634 < baseStart_1138634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138730 : List Nat := [3, 1, 4, 1, 2, 2, 3, 1, 4]
def baseStart_1138730 : Nat := 118140960795 + 1138730 * 2 ^ 59
def prefixEnd_1138730 : Nat := 4983230072969 + 3 ^ 40 * 1138730 * 2
def baseEnd_1138730 : Nat := 259873700308637754372481

theorem tailTrace_1138730 : CollatzResearch.WordTrace tailWord_1138730 prefixEnd_1138730 259873700308637754372481 := by
  unfold tailWord_1138730
  simp only [CollatzResearch.WordTrace]
  refine ⟨10383223791145791111449411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27688596776388776297198429 10383223791145791111449411)
  ·
    refine ⟨15574835686718686667174117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10383223791145791111449411 15574835686718686667174117)
    ·
      refine ⟨2920281691259753750095147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15574835686718686667174117 2920281691259753750095147)
      ·
        refine ⟨4380422536889630625142721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2920281691259753750095147 4380422536889630625142721)
        ·
          refine ⟨3285316902667222968857041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4380422536889630625142721 3285316902667222968857041)
          ·
            refine ⟨2463987677000417226642781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285316902667222968857041 2463987677000417226642781)
            ·
              refine ⟨923995378875156459991043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2463987677000417226642781 923995378875156459991043)
              ·
                refine ⟨1385993068312734689986565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 923995378875156459991043 1385993068312734689986565)
                ·
                  refine ⟨259873700308637754372481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1385993068312734689986565 259873700308637754372481)
                  ·
                    rfl

theorem cell21_1138730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 1, 4].length) (baseStart_1138730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138730 prefixEnd_1138730 := by exact prefixLift 1138730
  have htrace : WordTrace (prefixWord ++ tailWord_1138730) baseStart_1138730 baseEnd_1138730 := by
    simpa [prefixWord, tailWord_1138730, baseEnd_1138730] using wordTrace_append hprefix tailTrace_1138730
  have hstable : (prefixWord ++ tailWord_1138730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138730).length < 2 ^ (prefixWord ++ tailWord_1138730).sum := by decide
  have hdescent : baseEnd_1138730 < baseStart_1138730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138741 : List Nat := [1, 3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1138741 : Nat := 118140960795 + 1138741 * 2 ^ 59
def prefixEnd_1138741 : Nat := 4983230072969 + 3 ^ 40 * 1138741 * 2
def baseEnd_1138741 : Nat := 259876210658504179689125

theorem tailTrace_1138741 : CollatzResearch.WordTrace tailWord_1138741 prefixEnd_1138741 259876210658504179689125 := by
  unfold tailWord_1138741
  simp only [CollatzResearch.WordTrace]
  refine ⟨41533296367543313324448077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27688864245028875549632051 41533296367543313324448077)
  ·
    refine ⟨15574986137828742496668029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41533296367543313324448077 15574986137828742496668029)
    ·
      refine ⟨5840619801685778436250511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15574986137828742496668029 5840619801685778436250511)
      ·
        refine ⟨8760929702528667654375767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840619801685778436250511 8760929702528667654375767)
        ·
          refine ⟨13141394553793001481563651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8760929702528667654375767 13141394553793001481563651)
          ·
            refine ⟨19712091830689502222345477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13141394553793001481563651 19712091830689502222345477)
            ·
              refine ⟨3696017218254281666689777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19712091830689502222345477 3696017218254281666689777)
              ·
                refine ⟨2772012913690711250017333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3696017218254281666689777 2772012913690711250017333)
                ·
                  refine ⟨259876210658504179689125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2772012913690711250017333 259876210658504179689125)
                  ·
                    rfl

theorem cell21_1138741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1138741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138741 prefixEnd_1138741 := by exact prefixLift 1138741
  have htrace : WordTrace (prefixWord ++ tailWord_1138741) baseStart_1138741 baseEnd_1138741 := by
    simpa [prefixWord, tailWord_1138741, baseEnd_1138741] using wordTrace_append hprefix tailTrace_1138741
  have hstable : (prefixWord ++ tailWord_1138741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138741).length < 2 ^ (prefixWord ++ tailWord_1138741).sum := by decide
  have hdescent : baseEnd_1138741 < baseStart_1138741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138744 : List Nat := [2, 1, 2, 1, 6, 2, 2, 5]
def baseStart_1138744 : Nat := 118140960795 + 1138744 * 2 ^ 59
def prefixEnd_1138744 : Nat := 4983230072969 + 3 ^ 40 * 1138744 * 2
def baseEnd_1138744 : Nat := 86625631766458947046373

theorem tailTrace_1138744 : CollatzResearch.WordTrace tailWord_1138744 prefixEnd_1138744 86625631766458947046373 := by
  unfold tailWord_1138744
  simp only [CollatzResearch.WordTrace]
  refine ⟨20766702893266222418403643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27688937191021629891204857 20766702893266222418403643)
  ·
    refine ⟨31150054339899333627605465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20766702893266222418403643 31150054339899333627605465)
    ·
      refine ⟨23362540754924500220704099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31150054339899333627605465 23362540754924500220704099)
      ·
        refine ⟨35043811132386750331056149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23362540754924500220704099 35043811132386750331056149)
        ·
          refine ⟨1642678646830628921768257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 35043811132386750331056149 1642678646830628921768257)
          ·
            refine ⟨1232008985122971691326193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1642678646830628921768257 1232008985122971691326193)
            ·
              refine ⟨924006738842228768494645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1232008985122971691326193 924006738842228768494645)
              ·
                refine ⟨86625631766458947046373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924006738842228768494645 86625631766458947046373)
                ·
                  rfl

theorem cell21_1138744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_1138744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138744 prefixEnd_1138744 := by exact prefixLift 1138744
  have htrace : WordTrace (prefixWord ++ tailWord_1138744) baseStart_1138744 baseEnd_1138744 := by
    simpa [prefixWord, tailWord_1138744, baseEnd_1138744] using wordTrace_append hprefix tailTrace_1138744
  have hstable : (prefixWord ++ tailWord_1138744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138744).length < 2 ^ (prefixWord ++ tailWord_1138744).sum := by decide
  have hdescent : baseEnd_1138744 < baseStart_1138744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138772 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1138772 : Nat := 118140960795 + 1138772 * 2 ^ 59
def prefixEnd_1138772 : Nat := 4983230072969 + 3 ^ 40 * 1138772 * 2
def baseEnd_1138772 : Nat := 259883285280855014672395

theorem tailTrace_1138772 : CollatzResearch.WordTrace tailWord_1138772 prefixEnd_1138772 259883285280855014672395 := by
  unfold tailWord_1138772
  simp only [CollatzResearch.WordTrace]
  refine ⟨20767213515215502809413285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27689618020287337079217713 20767213515215502809413285)
  ·
    refine ⟨3893852534102906776764991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20767213515215502809413285 3893852534102906776764991)
    ·
      refine ⟨5840778801154360165147487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3893852534102906776764991 5840778801154360165147487)
      ·
        refine ⟨8761168201731540247721231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5840778801154360165147487 8761168201731540247721231)
        ·
          refine ⟨13141752302597310371581847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8761168201731540247721231 13141752302597310371581847)
          ·
            refine ⟨19712628453895965557372771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13141752302597310371581847 19712628453895965557372771)
            ·
              refine ⟨29568942680843948336059157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19712628453895965557372771 29568942680843948336059157)
              ·
                refine ⟨1386044188164560078252773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29568942680843948336059157 1386044188164560078252773)
                ·
                  refine ⟨259883285280855014672395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386044188164560078252773 259883285280855014672395)
                  ·
                    rfl

theorem cell21_1138772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1138772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138772 prefixEnd_1138772 := by exact prefixLift 1138772
  have htrace : WordTrace (prefixWord ++ tailWord_1138772) baseStart_1138772 baseEnd_1138772 := by
    simpa [prefixWord, tailWord_1138772, baseEnd_1138772] using wordTrace_append hprefix tailTrace_1138772
  have hstable : (prefixWord ++ tailWord_1138772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138772).length < 2 ^ (prefixWord ++ tailWord_1138772).sum := by decide
  have hdescent : baseEnd_1138772 < baseStart_1138772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138789 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1138789 : Nat := 118140960795 + 1138789 * 2 ^ 59
def prefixEnd_1138789 : Nat := 4983230072969 + 3 ^ 40 * 1138789 * 2
def baseEnd_1138789 : Nat := 259887164912466762889027

theorem tailTrace_1138789 : CollatzResearch.WordTrace tailWord_1138789 prefixEnd_1138789 259887164912466762889027 := by
  unfold tailWord_1138789
  simp only [CollatzResearch.WordTrace]
  refine ⟨41535047071369417522195421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27690031380912945014796947 41535047071369417522195421)
  ·
    refine ⟨15575642651763531570823283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41535047071369417522195421 15575642651763531570823283)
    ·
      refine ⟨23363463977645297356234925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15575642651763531570823283 23363463977645297356234925)
      ·
        refine ⟨8761298991616986508588097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23363463977645297356234925 8761298991616986508588097)
        ·
          refine ⟨6570974243712739881441073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8761298991616986508588097 6570974243712739881441073)
          ·
            refine ⟨4928230682784554911080805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6570974243712739881441073 4928230682784554911080805)
            ·
              refine ⟨924043253022104045827651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4928230682784554911080805 924043253022104045827651)
              ·
                refine ⟨1386064879533156068741477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 924043253022104045827651 1386064879533156068741477)
                ·
                  refine ⟨259887164912466762889027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386064879533156068741477 259887164912466762889027)
                  ·
                    rfl

theorem cell21_1138789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1138789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138789 prefixEnd_1138789 := by exact prefixLift 1138789
  have htrace : WordTrace (prefixWord ++ tailWord_1138789) baseStart_1138789 baseEnd_1138789 := by
    simpa [prefixWord, tailWord_1138789, baseEnd_1138789] using wordTrace_append hprefix tailTrace_1138789
  have hstable : (prefixWord ++ tailWord_1138789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138789).length < 2 ^ (prefixWord ++ tailWord_1138789).sum := by decide
  have hdescent : baseEnd_1138789 < baseStart_1138789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138848 : List Nat := [2, 1, 1, 4, 2, 2, 2, 3, 4]
def baseStart_1138848 : Nat := 118140960795 + 1138848 * 2 ^ 59
def prefixEnd_1138848 : Nat := 4983230072969 + 3 ^ 40 * 1138848 * 2
def baseEnd_1138848 : Nat := 259900629516295771405573

theorem tailTrace_1138848 : CollatzResearch.WordTrace tailWord_1138848 prefixEnd_1138848 259900629516295771405573 := by
  unfold tailWord_1138848
  simp only [CollatzResearch.WordTrace]
  refine ⟨20768599489077835299296599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27691465985437113732395465 20768599489077835299296599)
  ·
    refine ⟨31152899233616752948944899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20768599489077835299296599 31152899233616752948944899)
    ·
      refine ⟨46729348850425129423417349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31152899233616752948944899 46729348850425129423417349)
      ·
        refine ⟨8761752909454711766890753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46729348850425129423417349 8761752909454711766890753)
        ·
          refine ⟨6571314682091033825168065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8761752909454711766890753 6571314682091033825168065)
          ·
            refine ⟨4928486011568275368876049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6571314682091033825168065 4928486011568275368876049)
            ·
              refine ⟨3696364508676206526657037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4928486011568275368876049 3696364508676206526657037)
              ·
                refine ⟨1386136690753577447496389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3696364508676206526657037 1386136690753577447496389)
                ·
                  refine ⟨259900629516295771405573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386136690753577447496389 259900629516295771405573)
                  ·
                    rfl

theorem cell21_1138848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 4].length) (baseStart_1138848 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138848 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138848 prefixEnd_1138848 := by exact prefixLift 1138848
  have htrace : WordTrace (prefixWord ++ tailWord_1138848) baseStart_1138848 baseEnd_1138848 := by
    simpa [prefixWord, tailWord_1138848, baseEnd_1138848] using wordTrace_append hprefix tailTrace_1138848
  have hstable : (prefixWord ++ tailWord_1138848).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138848).length < 2 ^ (prefixWord ++ tailWord_1138848).sum := by decide
  have hdescent : baseEnd_1138848 < baseStart_1138848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138882 : List Nat := [3, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1138882 : Nat := 118140960795 + 1138882 * 2 ^ 59
def prefixEnd_1138882 : Nat := 4983230072969 + 3 ^ 40 * 1138882 * 2
def baseEnd_1138882 : Nat := 259908388779519267838837

theorem tailTrace_1138882 : CollatzResearch.WordTrace tailWord_1138882 prefixEnd_1138882 259908388779519267838837 := by
  unfold tailWord_1138882
  simp only [CollatzResearch.WordTrace]
  refine ⟨10384609765008123601332725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27692292706688329603553933 10384609765008123601332725)
  ·
    refine ⟨973557165469511587624943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 10384609765008123601332725 973557165469511587624943)
    ·
      refine ⟨1460335748204267381437415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 973557165469511587624943 1460335748204267381437415)
      ·
        refine ⟨2190503622306401072156123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1460335748204267381437415 2190503622306401072156123)
        ·
          refine ⟨3285755433459601608234185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2190503622306401072156123 3285755433459601608234185)
          ·
            refine ⟨2464316575094701206175639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3285755433459601608234185 2464316575094701206175639)
            ·
              refine ⟨3696474862642051809263459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2464316575094701206175639 3696474862642051809263459)
              ·
                refine ⟨5544712293963077713895189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3696474862642051809263459 5544712293963077713895189)
                ·
                  refine ⟨259908388779519267838837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5544712293963077713895189 259908388779519267838837)
                  ·
                    rfl

theorem cell21_1138882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1138882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138882 prefixEnd_1138882 := by exact prefixLift 1138882
  have htrace : WordTrace (prefixWord ++ tailWord_1138882) baseStart_1138882 baseEnd_1138882 := by
    simpa [prefixWord, tailWord_1138882, baseEnd_1138882] using wordTrace_append hprefix tailTrace_1138882
  have hstable : (prefixWord ++ tailWord_1138882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138882).length < 2 ^ (prefixWord ++ tailWord_1138882).sum := by decide
  have hdescent : baseEnd_1138882 < baseStart_1138882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138921 : List Nat := [1, 2, 1, 1, 1, 2, 2, 11]
def baseStart_1138921 : Nat := 118140960795 + 1138921 * 2 ^ 59
def prefixEnd_1138921 : Nat := 4983230072969 + 3 ^ 40 * 1138921 * 2
def baseEnd_1138921 : Nat := 86639096370287955562919

theorem tailTrace_1138921 : CollatzResearch.WordTrace tailWord_1138921 prefixEnd_1138921 86639096370287955562919 := by
  unfold tailWord_1138921
  simp only [CollatzResearch.WordTrace]
  refine ⟨41539861506891204066000617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27693241004594136044000411 41539861506891204066000617)
  ·
    refine ⟨31154896130168403049500463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41539861506891204066000617 31154896130168403049500463)
    ·
      refine ⟨46732344195252604574250695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31154896130168403049500463 46732344195252604574250695)
      ·
        refine ⟨70098516292878906861376043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46732344195252604574250695 70098516292878906861376043)
        ·
          refine ⟨105147774439318360292064065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70098516292878906861376043 105147774439318360292064065)
          ·
            refine ⟨78860830829488770219048049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105147774439318360292064065 78860830829488770219048049)
            ·
              refine ⟨59145623122116577664286037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78860830829488770219048049 59145623122116577664286037)
              ·
                refine ⟨86639096370287955562919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59145623122116577664286037 86639096370287955562919)
                ·
                  rfl

theorem cell21_1138921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_1138921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138921 prefixEnd_1138921 := by exact prefixLift 1138921
  have htrace : WordTrace (prefixWord ++ tailWord_1138921) baseStart_1138921 baseEnd_1138921 := by
    simpa [prefixWord, tailWord_1138921, baseEnd_1138921] using wordTrace_append hprefix tailTrace_1138921
  have hstable : (prefixWord ++ tailWord_1138921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138921).length < 2 ^ (prefixWord ++ tailWord_1138921).sum := by decide
  have hdescent : baseEnd_1138921 < baseStart_1138921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138927 : List Nat := [1, 1, 2, 1, 6, 3, 1, 3, 3]
def baseStart_1138927 : Nat := 118140960795 + 1138927 * 2 ^ 59
def prefixEnd_1138927 : Nat := 4983230072969 + 3 ^ 40 * 1138927 * 2
def baseEnd_1138927 : Nat := 259918658392609189588745

theorem tailTrace_1138927 : CollatzResearch.WordTrace tailWord_1138927 prefixEnd_1138927 259918658392609189588745 := by
  unfold tailWord_1138927
  simp only [CollatzResearch.WordTrace]
  refine ⟨41540080344869467090719035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27693386896579644727146023 41540080344869467090719035)
  ·
    refine ⟨62310120517304200636078553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41540080344869467090719035 62310120517304200636078553)
    ·
      refine ⟨46732590387978150477058915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62310120517304200636078553 46732590387978150477058915)
      ·
        refine ⟨70098885581967225715588373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46732590387978150477058915 70098885581967225715588373)
        ·
          refine ⟨3285885261654713705418205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70098885581967225715588373 3285885261654713705418205)
          ·
            refine ⟨1232206973120517639531827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3285885261654713705418205 1232206973120517639531827)
            ·
              refine ⟨1848310459680776459297741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232206973120517639531827 1848310459680776459297741)
              ·
                refine ⟨693116422380291172236653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1848310459680776459297741 693116422380291172236653)
                ·
                  refine ⟨259918658392609189588745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693116422380291172236653 259918658392609189588745)
                  ·
                    rfl

theorem cell21_1138927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 3].length) (baseStart_1138927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138927 prefixEnd_1138927 := by exact prefixLift 1138927
  have htrace : WordTrace (prefixWord ++ tailWord_1138927) baseStart_1138927 baseEnd_1138927 := by
    simpa [prefixWord, tailWord_1138927, baseEnd_1138927] using wordTrace_append hprefix tailTrace_1138927
  have hstable : (prefixWord ++ tailWord_1138927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138927).length < 2 ^ (prefixWord ++ tailWord_1138927).sum := by decide
  have hdescent : baseEnd_1138927 < baseStart_1138927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1138938 : List Nat := [3, 1, 1, 1, 1, 7, 7]
def baseStart_1138938 : Nat := 118140960795 + 1138938 * 2 ^ 59
def prefixEnd_1138938 : Nat := 4983230072969 + 3 ^ 40 * 1138938 * 2
def baseEnd_1138938 : Nat := 28880129860275068322821

theorem tailTrace_1138938 : CollatzResearch.WordTrace tailWord_1138938 prefixEnd_1138938 28880129860275068322821 := by
  unfold tailWord_1138938
  simp only [CollatzResearch.WordTrace]
  refine ⟨10385120386957403992342367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27693654365219743979579645 10385120386957403992342367)
  ·
    refine ⟨15577680580436105988513551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10385120386957403992342367 15577680580436105988513551)
    ·
      refine ⟨23366520870654158982770327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15577680580436105988513551 23366520870654158982770327)
      ·
        refine ⟨35049781305981238474155491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23366520870654158982770327 35049781305981238474155491)
        ·
          refine ⟨52574671958971857711233237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35049781305981238474155491 52574671958971857711233237)
          ·
            refine ⟨1232218874038402915107029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 52574671958971857711233237 1232218874038402915107029)
            ·
              refine ⟨28880129860275068322821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1232218874038402915107029 28880129860275068322821)
              ·
                rfl

theorem cell21_1138938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 7].length) (baseStart_1138938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1138938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1138938 prefixEnd_1138938 := by exact prefixLift 1138938
  have htrace : WordTrace (prefixWord ++ tailWord_1138938) baseStart_1138938 baseEnd_1138938 := by
    simpa [prefixWord, tailWord_1138938, baseEnd_1138938] using wordTrace_append hprefix tailTrace_1138938
  have hstable : (prefixWord ++ tailWord_1138938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1138938).length < 2 ^ (prefixWord ++ tailWord_1138938).sum := by decide
  have hdescent : baseEnd_1138938 < baseStart_1138938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1138938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139121 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 5]
def baseStart_1139121 : Nat := 118140960795 + 1139121 * 2 ^ 59
def prefixEnd_1139121 : Nat := 4983230072969 + 3 ^ 40 * 1139121 * 2
def baseEnd_1139121 : Nat := 259962931835707963355015

theorem tailTrace_1139121 : CollatzResearch.WordTrace tailWord_1139121 prefixEnd_1139121 259962931835707963355015 := by
  unfold tailWord_1139121
  simp only [CollatzResearch.WordTrace]
  refine ⟨41547156106166638223281217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27698104070777758815520811 41547156106166638223281217)
  ·
    refine ⟨31160367079624978667460913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41547156106166638223281217 31160367079624978667460913)
    ·
      refine ⟨23370275309718734000595685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31160367079624978667460913 23370275309718734000595685)
      ·
        refine ⟨4381926620572262625111691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23370275309718734000595685 4381926620572262625111691)
        ·
          refine ⟨6572889930858393937667537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4381926620572262625111691 6572889930858393937667537)
          ·
            refine ⟨4929667448143795453250653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6572889930858393937667537 4929667448143795453250653)
            ·
              refine ⟨1848625293053923294968995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4929667448143795453250653 1848625293053923294968995)
              ·
                refine ⟨2772937939580884942453493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1848625293053923294968995 2772937939580884942453493)
                ·
                  refine ⟨259962931835707963355015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2772937939580884942453493 259962931835707963355015)
                  ·
                    rfl

theorem cell21_1139121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 5].length) (baseStart_1139121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139121 prefixEnd_1139121 := by exact prefixLift 1139121
  have htrace : WordTrace (prefixWord ++ tailWord_1139121) baseStart_1139121 baseEnd_1139121 := by
    simpa [prefixWord, tailWord_1139121, baseEnd_1139121] using wordTrace_append hprefix tailTrace_1139121
  have hstable : (prefixWord ++ tailWord_1139121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139121).length < 2 ^ (prefixWord ++ tailWord_1139121).sum := by decide
  have hdescent : baseEnd_1139121 < baseStart_1139121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139180 : List Nat := [2, 2, 1, 1, 2, 1, 4, 3, 5]
def baseStart_1139180 : Nat := 118140960795 + 1139180 * 2 ^ 59
def prefixEnd_1139180 : Nat := 4983230072969 + 3 ^ 40 * 1139180 * 2
def baseEnd_1139180 : Nat := 259976396439536971871561

theorem tailTrace_1139180 : CollatzResearch.WordTrace tailWord_1139180 prefixEnd_1139180 259976396439536971871561 := by
  unfold tailWord_1139180
  simp only [CollatzResearch.WordTrace]
  refine ⟨20774654006476445649839497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27699538675301927533119329 20774654006476445649839497)
  ·
    refine ⟨15580990504857334237379623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20774654006476445649839497 15580990504857334237379623)
    ·
      refine ⟨23371485757286001356069435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15580990504857334237379623 23371485757286001356069435)
      ·
        refine ⟨35057228635929002034104153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23371485757286001356069435 35057228635929002034104153)
        ·
          refine ⟨26292921476946751525578115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35057228635929002034104153 26292921476946751525578115)
          ·
            refine ⟨39439382215420127288367173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26292921476946751525578115 39439382215420127288367173)
            ·
              refine ⟨7394884165391273866568845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39439382215420127288367173 7394884165391273866568845)
              ·
                refine ⟨2773081562021727699963317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7394884165391273866568845 2773081562021727699963317)
                ·
                  refine ⟨259976396439536971871561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2773081562021727699963317 259976396439536971871561)
                  ·
                    rfl

theorem cell21_1139180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_1139180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139180 prefixEnd_1139180 := by exact prefixLift 1139180
  have htrace : WordTrace (prefixWord ++ tailWord_1139180) baseStart_1139180 baseEnd_1139180 := by
    simpa [prefixWord, tailWord_1139180, baseEnd_1139180] using wordTrace_append hprefix tailTrace_1139180
  have hstable : (prefixWord ++ tailWord_1139180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139180).length < 2 ^ (prefixWord ++ tailWord_1139180).sum := by decide
  have hdescent : baseEnd_1139180 < baseStart_1139180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139214 : List Nat := [4, 1, 1, 2, 3, 1, 1, 5, 3]
def baseStart_1139214 : Nat := 118140960795 + 1139214 * 2 ^ 59
def prefixEnd_1139214 : Nat := 4983230072969 + 3 ^ 40 * 1139214 * 2
def baseEnd_1139214 : Nat := 259984155702760468304825

theorem tailTrace_1139214 : CollatzResearch.WordTrace tailWord_1139214 prefixEnd_1139214 259984155702760468304825 := by
  unfold tailWord_1139214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5193818511853714388302087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27700365396553143404277797 5193818511853714388302087)
  ·
    refine ⟨7790727767780571582453131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5193818511853714388302087 7790727767780571582453131)
    ·
      refine ⟨11686091651670857373679697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7790727767780571582453131 11686091651670857373679697)
      ·
        refine ⟨8764568738753143030259773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11686091651670857373679697 8764568738753143030259773)
        ·
          refine ⟨3286713277032428636347415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8764568738753143030259773 3286713277032428636347415)
          ·
            refine ⟨4930069915548642954521123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3286713277032428636347415 4930069915548642954521123)
            ·
              refine ⟨7395104873322964431781685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4930069915548642954521123 7395104873322964431781685)
              ·
                refine ⟨693291081874027915479533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7395104873322964431781685 693291081874027915479533)
                ·
                  refine ⟨259984155702760468304825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693291081874027915479533 259984155702760468304825)
                  ·
                    rfl

theorem cell21_1139214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_1139214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139214 prefixEnd_1139214 := by exact prefixLift 1139214
  have htrace : WordTrace (prefixWord ++ tailWord_1139214) baseStart_1139214 baseEnd_1139214 := by
    simpa [prefixWord, tailWord_1139214, baseEnd_1139214] using wordTrace_append hprefix tailTrace_1139214
  have hstable : (prefixWord ++ tailWord_1139214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139214).length < 2 ^ (prefixWord ++ tailWord_1139214).sum := by decide
  have hdescent : baseEnd_1139214 < baseStart_1139214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139228 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 4]
def baseStart_1139228 : Nat := 118140960795 + 1139228 * 2 ^ 59
def prefixEnd_1139228 : Nat := 4983230072969 + 3 ^ 40 * 1139228 * 2
def baseEnd_1139228 : Nat := 259987350693499555071463

theorem tailTrace_1139228 : CollatzResearch.WordTrace tailWord_1139228 prefixEnd_1139228 259987350693499555071463 := by
  unfold tailWord_1139228
  simp only [CollatzResearch.WordTrace]
  refine ⟨20775529358389497748713169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27700705811185996998284225 20775529358389497748713169)
  ·
    refine ⟨15581647018792123311534877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20775529358389497748713169 15581647018792123311534877)
    ·
      refine ⟨5843117632047046241825579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15581647018792123311534877 5843117632047046241825579)
      ·
        refine ⟨8764676448070569362738369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5843117632047046241825579 8764676448070569362738369)
        ·
          refine ⟨6573507336052927022053777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8764676448070569362738369 6573507336052927022053777)
          ·
            refine ⟨4930130502039695266540333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6573507336052927022053777 4930130502039695266540333)
            ·
              refine ⟨1848798938264885724952625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4930130502039695266540333 1848798938264885724952625)
              ·
                refine ⟨1386599203698664293714469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1848798938264885724952625 1386599203698664293714469)
                ·
                  refine ⟨259987350693499555071463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386599203698664293714469 259987350693499555071463)
                  ·
                    rfl

theorem cell21_1139228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_1139228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139228 prefixEnd_1139228 := by exact prefixLift 1139228
  have htrace : WordTrace (prefixWord ++ tailWord_1139228) baseStart_1139228 baseEnd_1139228 := by
    simpa [prefixWord, tailWord_1139228, baseEnd_1139228] using wordTrace_append hprefix tailTrace_1139228
  have hstable : (prefixWord ++ tailWord_1139228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139228).length < 2 ^ (prefixWord ++ tailWord_1139228).sum := by decide
  have hdescent : baseEnd_1139228 < baseStart_1139228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139256 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 5]
def baseStart_1139256 : Nat := 118140960795 + 1139256 * 2 ^ 59
def prefixEnd_1139256 : Nat := 4983230072969 + 3 ^ 40 * 1139256 * 2
def baseEnd_1139256 : Nat := 259993740674977728604739

theorem tailTrace_1139256 : CollatzResearch.WordTrace tailWord_1139256 prefixEnd_1139256 259993740674977728604739 := by
  unfold tailWord_1139256
  simp only [CollatzResearch.WordTrace]
  refine ⟨20776039980338778139722811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27701386640451704186297081 20776039980338778139722811)
  ·
    refine ⟨31164059970508167209584217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20776039980338778139722811 31164059970508167209584217)
    ·
      refine ⟨23373044977881125407188163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31164059970508167209584217 23373044977881125407188163)
      ·
        refine ⟨35059567466821688110782245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23373044977881125407188163 35059567466821688110782245)
        ·
          refine ⟨6573668900029066520771671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35059567466821688110782245 6573668900029066520771671)
          ·
            refine ⟨9860503350043599781157507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6573668900029066520771671 9860503350043599781157507)
            ·
              refine ⟨14790755025065399671736261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9860503350043599781157507 14790755025065399671736261)
              ·
                refine ⟨2773266567199762438450549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14790755025065399671736261 2773266567199762438450549)
                ·
                  refine ⟨259993740674977728604739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2773266567199762438450549 259993740674977728604739)
                  ·
                    rfl

theorem cell21_1139256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 5].length) (baseStart_1139256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139256 prefixEnd_1139256 := by exact prefixLift 1139256
  have htrace : WordTrace (prefixWord ++ tailWord_1139256) baseStart_1139256 baseEnd_1139256 := by
    simpa [prefixWord, tailWord_1139256, baseEnd_1139256] using wordTrace_append hprefix tailTrace_1139256
  have hstable : (prefixWord ++ tailWord_1139256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139256).length < 2 ^ (prefixWord ++ tailWord_1139256).sum := by decide
  have hdescent : baseEnd_1139256 < baseStart_1139256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139287 : List Nat := [1, 1, 3, 2, 2, 2, 2, 4, 4]
def baseStart_1139287 : Nat := 118140960795 + 1139287 * 2 ^ 59
def prefixEnd_1139287 : Nat := 4983230072969 + 3 ^ 40 * 1139287 * 2
def baseEnd_1139287 : Nat := 260000815297328563588009

theorem tailTrace_1139287 : CollatzResearch.WordTrace tailWord_1139287 prefixEnd_1139287 260000815297328563588009 := by
  unfold tailWord_1139287
  simp only [CollatzResearch.WordTrace]
  refine ⟨41553210623565248573824115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27702140415710165715882743 41553210623565248573824115)
  ·
    refine ⟨62329815935347872860736173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41553210623565248573824115 62329815935347872860736173)
    ·
      refine ⟨23373680975755452322776065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62329815935347872860736173 23373680975755452322776065)
      ·
        refine ⟨17530260731816589242082049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23373680975755452322776065 17530260731816589242082049)
        ·
          refine ⟨13147695548862441931561537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17530260731816589242082049 13147695548862441931561537)
          ·
            refine ⟨9860771661646831448671153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13147695548862441931561537 9860771661646831448671153)
            ·
              refine ⟨7395578746235123586503365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9860771661646831448671153 7395578746235123586503365)
              ·
                refine ⟨1386671014919085672469381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7395578746235123586503365 1386671014919085672469381)
                ·
                  refine ⟨260000815297328563588009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1386671014919085672469381 260000815297328563588009)
                  ·
                    rfl

theorem cell21_1139287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_1139287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139287 prefixEnd_1139287 := by exact prefixLift 1139287
  have htrace : WordTrace (prefixWord ++ tailWord_1139287) baseStart_1139287 baseEnd_1139287 := by
    simpa [prefixWord, tailWord_1139287, baseEnd_1139287] using wordTrace_append hprefix tailTrace_1139287
  have hstable : (prefixWord ++ tailWord_1139287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139287).length < 2 ^ (prefixWord ++ tailWord_1139287).sum := by decide
  have hdescent : baseEnd_1139287 < baseStart_1139287 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139442 : List Nat := [3, 2, 1, 3, 1, 2, 3, 3, 3]
def baseStart_1139442 : Nat := 118140960795 + 1139442 * 2 ^ 59
def prefixEnd_1139442 : Nat := 4983230072969 + 3 ^ 40 * 1139442 * 2
def baseEnd_1139442 : Nat := 260036188409082738504359

theorem tailTrace_1139442 : CollatzResearch.WordTrace tailWord_1139442 prefixEnd_1139442 260036188409082738504359 := by
  unfold tailWord_1139442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10389715984500927511429145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27705909292002473363811053 10389715984500927511429145)
  ·
    refine ⟨7792286988375695633571859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10389715984500927511429145 7792286988375695633571859)
    ·
      refine ⟨11688430482563543450357789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7792286988375695633571859 11688430482563543450357789)
      ·
        refine ⟨4383161430961328793884171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11688430482563543450357789 4383161430961328793884171)
        ·
          refine ⟨6574742146441993190826257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4383161430961328793884171 6574742146441993190826257)
          ·
            refine ⟨4931056609831494893119693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6574742146441993190826257 4931056609831494893119693)
            ·
              refine ⟨1849146228686810584919885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931056609831494893119693 1849146228686810584919885)
              ·
                refine ⟨693429835757553969344957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1849146228686810584919885 693429835757553969344957)
                ·
                  refine ⟨260036188409082738504359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693429835757553969344957 260036188409082738504359)
                  ·
                    rfl

theorem cell21_1139442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 3, 3].length) (baseStart_1139442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139442 prefixEnd_1139442 := by exact prefixLift 1139442
  have htrace : WordTrace (prefixWord ++ tailWord_1139442) baseStart_1139442 baseEnd_1139442 := by
    simpa [prefixWord, tailWord_1139442, baseEnd_1139442] using wordTrace_append hprefix tailTrace_1139442
  have hstable : (prefixWord ++ tailWord_1139442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139442).length < 2 ^ (prefixWord ++ tailWord_1139442).sum := by decide
  have hdescent : baseEnd_1139442 < baseStart_1139442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139445 : List Nat := [1, 3, 6, 1, 2, 1, 7]
def baseStart_1139445 : Nat := 118140960795 + 1139445 * 2 ^ 59
def prefixEnd_1139445 : Nat := 4983230072969 + 3 ^ 40 * 1139445 * 2
def baseEnd_1139445 : Nat := 28892985894439488883817

theorem tailTrace_1139445 : CollatzResearch.WordTrace tailWord_1139445 prefixEnd_1139445 28892985894439488883817 := by
  unfold tailWord_1139445
  simp only [CollatzResearch.WordTrace]
  refine ⟨41558973356992841558075789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27705982237995227705383859 41558973356992841558075789)
  ·
    refine ⟨15584615008872315584278421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41558973356992841558075789 15584615008872315584278421)
    ·
      refine ⟨730528828540889793013051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 15584615008872315584278421 730528828540889793013051)
      ·
        refine ⟨1095793242811334689519577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 730528828540889793013051 1095793242811334689519577)
        ·
          refine ⟨821844932108501017139683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1095793242811334689519577 821844932108501017139683)
          ·
            refine ⟨1232767398162751525709525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821844932108501017139683 1232767398162751525709525)
            ·
              refine ⟨28892985894439488883817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1232767398162751525709525 28892985894439488883817)
              ·
                rfl

theorem cell21_1139445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 7].length) (baseStart_1139445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139445 prefixEnd_1139445 := by exact prefixLift 1139445
  have htrace : WordTrace (prefixWord ++ tailWord_1139445) baseStart_1139445 baseEnd_1139445 := by
    simpa [prefixWord, tailWord_1139445, baseEnd_1139445] using wordTrace_append hprefix tailTrace_1139445
  have hstable : (prefixWord ++ tailWord_1139445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139445).length < 2 ^ (prefixWord ++ tailWord_1139445).sum := by decide
  have hdescent : baseEnd_1139445 < baseStart_1139445 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139529 : List Nat := [1, 2, 1, 1, 2, 5, 3, 6]
def baseStart_1139529 : Nat := 118140960795 + 1139529 * 2 ^ 59
def prefixEnd_1139529 : Nat := 4983230072969 + 3 ^ 40 * 1139529 * 2
def baseEnd_1139529 : Nat := 86685347664796640184727

theorem tailTrace_1139529 : CollatzResearch.WordTrace tailWord_1139529 prefixEnd_1139529 86685347664796640184727 := by
  unfold tailWord_1139529
  simp only [CollatzResearch.WordTrace]
  refine ⟨41562037088688523904133641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27708024725792349269422427 41562037088688523904133641)
  ·
    refine ⟨31171527816516392928100231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41562037088688523904133641 31171527816516392928100231)
    ·
      refine ⟨46757291724774589392150347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31171527816516392928100231 46757291724774589392150347)
      ·
        refine ⟨70135937587161884088225521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46757291724774589392150347 70135937587161884088225521)
        ·
          refine ⟨52601953190371413066169141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70135937587161884088225521 52601953190371413066169141)
          ·
            refine ⟨4931433111597319974953357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52601953190371413066169141 4931433111597319974953357)
            ·
              refine ⟨1849287416848994990607509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4931433111597319974953357 1849287416848994990607509)
              ·
                refine ⟨86685347664796640184727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1849287416848994990607509 86685347664796640184727)
                ·
                  rfl

theorem cell21_1139529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 6].length) (baseStart_1139529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139529 prefixEnd_1139529 := by exact prefixLift 1139529
  have htrace : WordTrace (prefixWord ++ tailWord_1139529) baseStart_1139529 baseEnd_1139529 := by
    simpa [prefixWord, tailWord_1139529, baseEnd_1139529] using wordTrace_append hprefix tailTrace_1139529
  have hstable : (prefixWord ++ tailWord_1139529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139529).length < 2 ^ (prefixWord ++ tailWord_1139529).sum := by decide
  have hdescent : baseEnd_1139529 < baseStart_1139529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139546 : List Nat := [3, 1, 1, 2, 1, 5, 3, 5]
def baseStart_1139546 : Nat := 118140960795 + 1139546 * 2 ^ 59
def prefixEnd_1139546 : Nat := 4983230072969 + 3 ^ 40 * 1139546 * 2
def baseEnd_1139546 : Nat := 86686640875333889590271

theorem tailTrace_1139546 : CollatzResearch.WordTrace tailWord_1139546 prefixEnd_1139546 86686640875333889590271 := by
  unfold tailWord_1139546
  simp only [CollatzResearch.WordTrace]
  refine ⟨10390664282406733951875623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27708438086417957205001661 10390664282406733951875623)
  ·
    refine ⟨15585996423610100927813435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10390664282406733951875623 15585996423610100927813435)
    ·
      refine ⟨23378994635415151391720153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15585996423610100927813435 23378994635415151391720153)
      ·
        refine ⟨17534245976561363543790115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23378994635415151391720153 17534245976561363543790115)
        ·
          refine ⟨26301368964842045315685173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17534245976561363543790115 26301368964842045315685173)
          ·
            refine ⟨2465753340453941748345485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26301368964842045315685173 2465753340453941748345485)
            ·
              refine ⟨924657502670228155629557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2465753340453941748345485 924657502670228155629557)
              ·
                refine ⟨86686640875333889590271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924657502670228155629557 86686640875333889590271)
                ·
                  rfl

theorem cell21_1139546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 5].length) (baseStart_1139546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139546 prefixEnd_1139546 := by exact prefixLift 1139546
  have htrace : WordTrace (prefixWord ++ tailWord_1139546) baseStart_1139546 baseEnd_1139546 := by
    simpa [prefixWord, tailWord_1139546, baseEnd_1139546] using wordTrace_append hprefix tailTrace_1139546
  have hstable : (prefixWord ++ tailWord_1139546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139546).length < 2 ^ (prefixWord ++ tailWord_1139546).sum := by decide
  have hdescent : baseEnd_1139546 < baseStart_1139546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139566 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_1139566 : Nat := 118140960795 + 1139566 * 2 ^ 59
def prefixEnd_1139566 : Nat := 4983230072969 + 3 ^ 40 * 1139566 * 2
def baseEnd_1139566 : Nat := 260064486898486078437439

theorem tailTrace_1139566 : CollatzResearch.WordTrace tailWord_1139566 prefixEnd_1139566 260064486898486078437439 := by
  unfold tailWord_1139566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5195423323694309902903819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27708924393036319482153701 5195423323694309902903819)
  ·
    refine ⟨7793134985541464854355729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5195423323694309902903819 7793134985541464854355729)
    ·
      refine ⟨5844851239156098640766797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7793134985541464854355729 5844851239156098640766797)
      ·
        refine ⟨2191819214683536990287549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5844851239156098640766797 2191819214683536990287549)
        ·
          refine ⟨821932205506326371357831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2191819214683536990287549 821932205506326371357831)
          ·
            refine ⟨1232898308259489557036747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 821932205506326371357831 1232898308259489557036747)
            ·
              refine ⟨1849347462389234335555121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1232898308259489557036747 1849347462389234335555121)
              ·
                refine ⟨1387010596791925751666341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849347462389234335555121 1387010596791925751666341)
                ·
                  refine ⟨260064486898486078437439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387010596791925751666341 260064486898486078437439)
                  ·
                    rfl

theorem cell21_1139566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_1139566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139566 prefixEnd_1139566 := by exact prefixLift 1139566
  have htrace : WordTrace (prefixWord ++ tailWord_1139566) baseStart_1139566 baseEnd_1139566 := by
    simpa [prefixWord, tailWord_1139566, baseEnd_1139566] using wordTrace_append hprefix tailTrace_1139566
  have hstable : (prefixWord ++ tailWord_1139566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139566).length < 2 ^ (prefixWord ++ tailWord_1139566).sum := by decide
  have hdescent : baseEnd_1139566 < baseStart_1139566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139577 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 3]
def baseStart_1139577 : Nat := 118140960795 + 1139577 * 2 ^ 59
def prefixEnd_1139577 : Nat := 4983230072969 + 3 ^ 40 * 1139577 * 2
def baseEnd_1139577 : Nat := 260066997248352503754083

theorem tailTrace_1139577 : CollatzResearch.WordTrace tailWord_1139577 prefixEnd_1139577 260066997248352503754083 := by
  unfold tailWord_1139577
  simp only [CollatzResearch.WordTrace]
  refine ⟨41563787792514628101880985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27709191861676418734587323 41563787792514628101880985)
  ·
    refine ⟨31172840844385971076410739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41563787792514628101880985 31172840844385971076410739)
    ·
      refine ⟨46759261266578956614616109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31172840844385971076410739 46759261266578956614616109)
      ·
        refine ⟨17534722974967108730481041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46759261266578956614616109 17534722974967108730481041)
        ·
          refine ⟨13151042231225331547860781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17534722974967108730481041 13151042231225331547860781)
          ·
            refine ⟨4931640836709499330447793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13151042231225331547860781 4931640836709499330447793)
            ·
              refine ⟨3698730627532124497835845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4931640836709499330447793 3698730627532124497835845)
              ·
                refine ⟨693511992662273343344221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3698730627532124497835845 693511992662273343344221)
                ·
                  refine ⟨260066997248352503754083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693511992662273343344221 260066997248352503754083)
                  ·
                    rfl

theorem cell21_1139577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_1139577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139577 prefixEnd_1139577 := by exact prefixLift 1139577
  have htrace : WordTrace (prefixWord ++ tailWord_1139577) baseStart_1139577 baseEnd_1139577 := by
    simpa [prefixWord, tailWord_1139577, baseEnd_1139577] using wordTrace_append hprefix tailTrace_1139577
  have hstable : (prefixWord ++ tailWord_1139577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139577).length < 2 ^ (prefixWord ++ tailWord_1139577).sum := by decide
  have hdescent : baseEnd_1139577 < baseStart_1139577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139605 : List Nat := [1, 3, 2, 1, 1, 5, 1, 7]
def baseStart_1139605 : Nat := 118140960795 + 1139605 * 2 ^ 59
def prefixEnd_1139605 : Nat := 4983230072969 + 3 ^ 40 * 1139605 * 2
def baseEnd_1139605 : Nat := 86691129076610225762453

theorem tailTrace_1139605 : CollatzResearch.WordTrace tailWord_1139605 prefixEnd_1139605 86691129076610225762453 := by
  unfold tailWord_1139605
  simp only [CollatzResearch.WordTrace]
  refine ⟨41564809036413188883900269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27709872690942125922600179 41564809036413188883900269)
  ·
    refine ⟨15586803388654945831462601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41564809036413188883900269 15586803388654945831462601)
    ·
      refine ⟨11690102541491209373596951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15586803388654945831462601 11690102541491209373596951)
      ·
        refine ⟨17535153812236814060395427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11690102541491209373596951 17535153812236814060395427)
        ·
          refine ⟨26302730718355221090593141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17535153812236814060395427 26302730718355221090593141)
          ·
            refine ⟨2465881004845801977243107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26302730718355221090593141 2465881004845801977243107)
            ·
              refine ⟨3698821507268702965864661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2465881004845801977243107 3698821507268702965864661)
              ·
                refine ⟨86691129076610225762453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3698821507268702965864661 86691129076610225762453)
                ·
                  rfl

theorem cell21_1139605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 7].length) (baseStart_1139605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139605 prefixEnd_1139605 := by exact prefixLift 1139605
  have htrace : WordTrace (prefixWord ++ tailWord_1139605) baseStart_1139605 baseEnd_1139605 := by
    simpa [prefixWord, tailWord_1139605, baseEnd_1139605] using wordTrace_append hprefix tailTrace_1139605
  have hstable : (prefixWord ++ tailWord_1139605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139605).length < 2 ^ (prefixWord ++ tailWord_1139605).sum := by decide
  have hdescent : baseEnd_1139605 < baseStart_1139605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139619 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 7]
def baseStart_1139619 : Nat := 118140960795 + 1139619 * 2 ^ 59
def prefixEnd_1139619 : Nat := 4983230072969 + 3 ^ 40 * 1139619 * 2
def baseEnd_1139619 : Nat := 260076582220569764053997

theorem tailTrace_1139619 : CollatzResearch.WordTrace tailWord_1139619 prefixEnd_1139619 260076582220569764053997 := by
  unfold tailWord_1139619
  simp only [CollatzResearch.WordTrace]
  refine ⟨41565319658362469274909911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27710213105574979516606607 41565319658362469274909911)
  ·
    refine ⟨62347979487543703912364867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41565319658362469274909911 62347979487543703912364867)
    ·
      refine ⟨93521969231315555868547301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62347979487543703912364867 93521969231315555868547301)
      ·
        refine ⟨17535369230871666725352619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93521969231315555868547301 17535369230871666725352619)
        ·
          refine ⟨26303053846307500088028929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17535369230871666725352619 26303053846307500088028929)
          ·
            refine ⟨19727290384730625066021697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26303053846307500088028929 19727290384730625066021697)
            ·
              refine ⟨14795467788547968799516273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19727290384730625066021697 14795467788547968799516273)
              ·
                refine ⟨11096600841410976599637205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14795467788547968799516273 11096600841410976599637205)
                ·
                  refine ⟨260076582220569764053997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11096600841410976599637205 260076582220569764053997)
                  ·
                    rfl

theorem cell21_1139619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 7].length) (baseStart_1139619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139619 prefixEnd_1139619 := by exact prefixLift 1139619
  have htrace : WordTrace (prefixWord ++ tailWord_1139619) baseStart_1139619 baseEnd_1139619 := by
    simpa [prefixWord, tailWord_1139619, baseEnd_1139619] using wordTrace_append hprefix tailTrace_1139619
  have hstable : (prefixWord ++ tailWord_1139619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139619).length < 2 ^ (prefixWord ++ tailWord_1139619).sum := by decide
  have hdescent : baseEnd_1139619 < baseStart_1139619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139687 : List Nat := [1, 1, 5, 2, 2, 3, 2, 2, 3]
def baseStart_1139687 : Nat := 118140960795 + 1139687 * 2 ^ 59
def prefixEnd_1139687 : Nat := 4983230072969 + 3 ^ 40 * 1139687 * 2
def baseEnd_1139687 : Nat := 260092100747016756920525

theorem tailTrace_1139687 : CollatzResearch.WordTrace tailWord_1139687 prefixEnd_1139687 260092100747016756920525 := by
  unfold tailWord_1139687
  simp only [CollatzResearch.WordTrace]
  refine ⟨41567799822116116888385315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27711866548077411258923543 41567799822116116888385315)
  ·
    refine ⟨62351699733174175332577973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41567799822116116888385315 62351699733174175332577973)
    ·
      refine ⟨5845471849985078937429185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62351699733174175332577973 5845471849985078937429185)
      ·
        refine ⟨4384103887488809203071889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5845471849985078937429185 4384103887488809203071889)
        ·
          refine ⟨3288077915616606902303917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4384103887488809203071889 3288077915616606902303917)
          ·
            refine ⟨1233029218356227588363969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3288077915616606902303917 1233029218356227588363969)
            ·
              refine ⟨924771913767170691272977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233029218356227588363969 924771913767170691272977)
              ·
                refine ⟨693578935325378018454733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 924771913767170691272977 693578935325378018454733)
                ·
                  refine ⟨260092100747016756920525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693578935325378018454733 260092100747016756920525)
                  ·
                    rfl

theorem cell21_1139687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 2, 3].length) (baseStart_1139687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139687 prefixEnd_1139687 := by exact prefixLift 1139687
  have htrace : WordTrace (prefixWord ++ tailWord_1139687) baseStart_1139687 baseEnd_1139687 := by
    simpa [prefixWord, tailWord_1139687, baseEnd_1139687] using wordTrace_append hprefix tailTrace_1139687
  have hstable : (prefixWord ++ tailWord_1139687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139687).length < 2 ^ (prefixWord ++ tailWord_1139687).sum := by decide
  have hdescent : baseEnd_1139687 < baseStart_1139687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139743 : List Nat := [1, 1, 2, 4, 1, 3, 3, 2, 4]
def baseStart_1139743 : Nat := 118140960795 + 1139743 * 2 ^ 59
def prefixEnd_1139743 : Nat := 4983230072969 + 3 ^ 40 * 1139743 * 2
def baseEnd_1139743 : Nat := 260104880709973103987077

theorem tailTrace_1139743 : CollatzResearch.WordTrace tailWord_1139743 prefixEnd_1139743 260104880709973103987077 := by
  unfold tailWord_1139743
  simp only [CollatzResearch.WordTrace]
  refine ⟨41569842309913238452423883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27713228206608825634949255 41569842309913238452423883)
  ·
    refine ⟨62354763464869857678635825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41569842309913238452423883 62354763464869857678635825)
    ·
      refine ⟨46766072598652393258976869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62354763464869857678635825 46766072598652393258976869)
      ·
        refine ⟨8768638612247323736058163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46766072598652393258976869 8768638612247323736058163)
        ·
          refine ⟨13152957918370985604087245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8768638612247323736058163 13152957918370985604087245)
          ·
            refine ⟨4932359219389119601532717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13152957918370985604087245 4932359219389119601532717)
            ·
              refine ⟨1849634707270919850574769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4932359219389119601532717 1849634707270919850574769)
              ·
                refine ⟨1387226030453189887931077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1849634707270919850574769 1387226030453189887931077)
                ·
                  refine ⟨260104880709973103987077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387226030453189887931077 260104880709973103987077)
                  ·
                    rfl

theorem cell21_1139743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_1139743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139743 prefixEnd_1139743 := by exact prefixLift 1139743
  have htrace : WordTrace (prefixWord ++ tailWord_1139743) baseStart_1139743 baseEnd_1139743 := by
    simpa [prefixWord, tailWord_1139743, baseEnd_1139743] using wordTrace_append hprefix tailTrace_1139743
  have hstable : (prefixWord ++ tailWord_1139743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139743).length < 2 ^ (prefixWord ++ tailWord_1139743).sum := by decide
  have hdescent : baseEnd_1139743 < baseStart_1139743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139774 : List Nat := [4, 2, 1, 3, 1, 2, 1, 7]
def baseStart_1139774 : Nat := 118140960795 + 1139774 * 2 ^ 59
def prefixEnd_1139774 : Nat := 4983230072969 + 3 ^ 40 * 1139774 * 2
def baseEnd_1139774 : Nat := 86703985110774646323449

theorem tailTrace_1139774 : CollatzResearch.WordTrace tailWord_1139774 prefixEnd_1139774 86703985110774646323449 := by
  unfold tailWord_1139774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5196371621600116343350297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27713981981867287164534917 5196371621600116343350297)
  ·
    refine ⟨3897278716200087257512723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5196371621600116343350297 3897278716200087257512723)
    ·
      refine ⟨5845918074300130886269085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3897278716200087257512723 5845918074300130886269085)
      ·
        refine ⟨2192219277862549082350907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5845918074300130886269085 2192219277862549082350907)
        ·
          refine ⟨3288328916793823623526361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2192219277862549082350907 3288328916793823623526361)
          ·
            refine ⟨2466246687595367717644771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3288328916793823623526361 2466246687595367717644771)
            ·
              refine ⟨3699370031393051576467157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2466246687595367717644771 3699370031393051576467157)
              ·
                refine ⟨86703985110774646323449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3699370031393051576467157 86703985110774646323449)
                ·
                  rfl

theorem cell21_1139774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 7].length) (baseStart_1139774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139774 prefixEnd_1139774 := by exact prefixLift 1139774
  have htrace : WordTrace (prefixWord ++ tailWord_1139774) baseStart_1139774 baseEnd_1139774 := by
    simpa [prefixWord, tailWord_1139774, baseEnd_1139774] using wordTrace_append hprefix tailTrace_1139774
  have hstable : (prefixWord ++ tailWord_1139774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139774).length < 2 ^ (prefixWord ++ tailWord_1139774).sum := by decide
  have hdescent : baseEnd_1139774 < baseStart_1139774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1139943 : List Nat := [1, 1, 5, 3, 2, 2, 2, 5]
def baseStart_1139943 : Nat := 118140960795 + 1139943 * 2 ^ 59
def prefixEnd_1139943 : Nat := 4983230072969 + 3 ^ 40 * 1139943 * 2
def baseEnd_1139943 : Nat := 86716841144939066884445

theorem tailTrace_1139943 : CollatzResearch.WordTrace tailWord_1139943 prefixEnd_1139943 86716841144939066884445 := by
  unfold tailWord_1139943
  simp only [CollatzResearch.WordTrace]
  refine ⟨41577136909188672609704483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27718091272792448406469655 41577136909188672609704483)
  ·
    refine ⟨62365705363783008914556725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41577136909188672609704483 62365705363783008914556725)
    ·
      refine ⟨5846784877854657085739693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62365705363783008914556725 5846784877854657085739693)
      ·
        refine ⟨2192544329195496407152385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5846784877854657085739693 2192544329195496407152385)
        ·
          refine ⟨1644408246896622305364289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2192544329195496407152385 1644408246896622305364289)
          ·
            refine ⟨1233306185172466729023217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1644408246896622305364289 1233306185172466729023217)
            ·
              refine ⟨924979638879350046767413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1233306185172466729023217 924979638879350046767413)
              ·
                refine ⟨86716841144939066884445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 924979638879350046767413 86716841144939066884445)
                ·
                  rfl

theorem cell21_1139943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 5].length) (baseStart_1139943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1139943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1139943 prefixEnd_1139943 := by exact prefixLift 1139943
  have htrace : WordTrace (prefixWord ++ tailWord_1139943) baseStart_1139943 baseEnd_1139943 := by
    simpa [prefixWord, tailWord_1139943, baseEnd_1139943] using wordTrace_append hprefix tailTrace_1139943
  have hstable : (prefixWord ++ tailWord_1139943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1139943).length < 2 ^ (prefixWord ++ tailWord_1139943).sum := by decide
  have hdescent : baseEnd_1139943 < baseStart_1139943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1139943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140016 : List Nat := [2, 1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_1140016 : Nat := 118140960795 + 1140016 * 2 ^ 59
def prefixEnd_1140016 : Nat := 4983230072969 + 3 ^ 40 * 1140016 * 2
def baseEnd_1140016 : Nat := 260167183029385295936519

theorem tailTrace_1140016 : CollatzResearch.WordTrace tailWord_1140016 prefixEnd_1140016 260167183029385295936519 := by
  unfold tailWord_1140016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20789899718962103038555951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27719866291949470718074601 20789899718962103038555951)
  ·
    refine ⟨31184849578443154557833927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20789899718962103038555951 31184849578443154557833927)
    ·
      refine ⟨46777274367664731836750891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31184849578443154557833927 46777274367664731836750891)
      ·
        refine ⟨70165911551497097755126337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46777274367664731836750891 70165911551497097755126337)
        ·
          refine ⟨52624433663622823316344753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70165911551497097755126337 52624433663622823316344753)
          ·
            refine ⟨39468325247717117487258565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52624433663622823316344753 39468325247717117487258565)
            ·
              refine ⟨7400310983946959528860981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39468325247717117487258565 7400310983946959528860981)
              ·
                refine ⟨693779154745027455830717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7400310983946959528860981 693779154745027455830717)
                ·
                  refine ⟨260167183029385295936519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693779154745027455830717 260167183029385295936519)
                  ·
                    rfl

theorem cell21_1140016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_1140016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140016 prefixEnd_1140016 := by exact prefixLift 1140016
  have htrace : WordTrace (prefixWord ++ tailWord_1140016) baseStart_1140016 baseEnd_1140016 := by
    simpa [prefixWord, tailWord_1140016, baseEnd_1140016] using wordTrace_append hprefix tailTrace_1140016
  have hstable : (prefixWord ++ tailWord_1140016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140016).length < 2 ^ (prefixWord ++ tailWord_1140016).sum := by decide
  have hdescent : baseEnd_1140016 < baseStart_1140016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140078 : List Nat := [4, 1, 2, 4, 1, 1, 8]
def baseStart_1140078 : Nat := 118140960795 + 1140078 * 2 ^ 59
def prefixEnd_1140078 : Nat := 4983230072969 + 3 ^ 40 * 1140078 * 2
def baseEnd_1140078 : Nat := 28909036919342996211451

theorem tailTrace_1140078 : CollatzResearch.WordTrace tailWord_1140078 prefixEnd_1140078 28909036919342996211451 := by
  unfold tailWord_1140078
  simp only [CollatzResearch.WordTrace]
  refine ⟨5197757595462448833233611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27721373842466393777245925 5197757595462448833233611)
  ·
    refine ⟨7796636393193673249850417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5197757595462448833233611 7796636393193673249850417)
    ·
      refine ⟨5847477294895254937387813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7796636393193673249850417 5847477294895254937387813)
      ·
        refine ⟨1096401992792860300760215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5847477294895254937387813 1096401992792860300760215)
        ·
          refine ⟨1644602989189290451140323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1096401992792860300760215 1644602989189290451140323)
          ·
            refine ⟨2466904483783935676710485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1644602989189290451140323 2466904483783935676710485)
            ·
              refine ⟨28909036919342996211451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2466904483783935676710485 28909036919342996211451)
              ·
                rfl

theorem cell21_1140078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 8].length) (baseStart_1140078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140078 prefixEnd_1140078 := by exact prefixLift 1140078
  have htrace : WordTrace (prefixWord ++ tailWord_1140078) baseStart_1140078 baseEnd_1140078 := by
    simpa [prefixWord, tailWord_1140078, baseEnd_1140078] using wordTrace_append hprefix tailTrace_1140078
  have hstable : (prefixWord ++ tailWord_1140078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140078).length < 2 ^ (prefixWord ++ tailWord_1140078).sum := by decide
  have hdescent : baseEnd_1140078 < baseStart_1140078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140092 : List Nat := [2, 2, 2, 1, 1, 1, 3, 6, 3]
def baseStart_1140092 : Nat := 118140960795 + 1140092 * 2 ^ 59
def prefixEnd_1140092 : Nat := 4983230072969 + 3 ^ 40 * 1140092 * 2
def baseEnd_1140092 : Nat := 260184527264826052669697

theorem tailTrace_1140092 : CollatzResearch.WordTrace tailWord_1140092 prefixEnd_1140092 260184527264826052669697 := by
  unfold tailWord_1140092
  simp only [CollatzResearch.WordTrace]
  refine ⟨20791285692824435528439265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27721714257099247371252353 20791285692824435528439265)
  ·
    refine ⟨15593464269618326646329449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20791285692824435528439265 15593464269618326646329449)
    ·
      refine ⟨11695098202213744984747087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15593464269618326646329449 11695098202213744984747087)
      ·
        refine ⟨17542647303320617477120631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11695098202213744984747087 17542647303320617477120631)
        ·
          refine ⟨26313970954980926215680947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17542647303320617477120631 26313970954980926215680947)
          ·
            refine ⟨39470956432471389323521421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26313970954980926215680947 39470956432471389323521421)
            ·
              refine ⟨14801608662176770996320533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39470956432471389323521421 14801608662176770996320533)
              ·
                refine ⟨693825406039536140452525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14801608662176770996320533 693825406039536140452525)
                ·
                  refine ⟨260184527264826052669697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 693825406039536140452525 260184527264826052669697)
                  ·
                    rfl

theorem cell21_1140092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_1140092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140092 prefixEnd_1140092 := by exact prefixLift 1140092
  have htrace : WordTrace (prefixWord ++ tailWord_1140092) baseStart_1140092 baseEnd_1140092 := by
    simpa [prefixWord, tailWord_1140092, baseEnd_1140092] using wordTrace_append hprefix tailTrace_1140092
  have hstable : (prefixWord ++ tailWord_1140092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140092).length < 2 ^ (prefixWord ++ tailWord_1140092).sum := by decide
  have hdescent : baseEnd_1140092 < baseStart_1140092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140199 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 4]
def baseStart_1140199 : Nat := 118140960795 + 1140199 * 2 ^ 59
def prefixEnd_1140199 : Nat := 4983230072969 + 3 ^ 40 * 1140199 * 2
def baseEnd_1140199 : Nat := 260208946122617644386145

theorem tailTrace_1140199 : CollatzResearch.WordTrace tailWord_1140199 prefixEnd_1140199 260208946122617644386145 := by
  unfold tailWord_1140199
  simp only [CollatzResearch.WordTrace]
  refine ⟨41586473996261228331023651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27724315997507485554015767 41586473996261228331023651)
  ·
    refine ⟨62379710994391842496535477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41586473996261228331023651 62379710994391842496535477)
    ·
      refine ⟨5848097905724235234050201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62379710994391842496535477 5848097905724235234050201)
      ·
        refine ⟨4386073429293176425537651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5848097905724235234050201 4386073429293176425537651)
        ·
          refine ⟨6579110143939764638306477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386073429293176425537651 6579110143939764638306477)
          ·
            refine ⟨2467166303977411739364929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6579110143939764638306477 2467166303977411739364929)
            ·
              refine ⟨1850374727983058804523697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2467166303977411739364929 1850374727983058804523697)
              ·
                refine ⟨1387781045987294103392773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1850374727983058804523697 1387781045987294103392773)
                ·
                  refine ⟨260208946122617644386145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387781045987294103392773 260208946122617644386145)
                  ·
                    rfl

theorem cell21_1140199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 4].length) (baseStart_1140199 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140199 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140199 prefixEnd_1140199 := by exact prefixLift 1140199
  have htrace : WordTrace (prefixWord ++ tailWord_1140199) baseStart_1140199 baseEnd_1140199 := by
    simpa [prefixWord, tailWord_1140199, baseEnd_1140199] using wordTrace_append hprefix tailTrace_1140199
  have hstable : (prefixWord ++ tailWord_1140199).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140199).length < 2 ^ (prefixWord ++ tailWord_1140199).sum := by decide
  have hdescent : baseEnd_1140199 < baseStart_1140199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140241 : List Nat := [1, 2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_1140241 : Nat := 118140960795 + 1140241 * 2 ^ 59
def prefixEnd_1140241 : Nat := 4983230072969 + 3 ^ 40 * 1140241 * 2
def baseEnd_1140241 : Nat := 260218531094834904686059

theorem tailTrace_1140241 : CollatzResearch.WordTrace tailWord_1140241 prefixEnd_1140241 260218531094834904686059 := by
  unfold tailWord_1140241
  simp only [CollatzResearch.WordTrace]
  refine ⟨41588005862109069504052577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27725337241406046336035051 41588005862109069504052577)
  ·
    refine ⟨31191004396581802128039433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41588005862109069504052577 31191004396581802128039433)
    ·
      refine ⟨23393253297436351596029575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31191004396581802128039433 23393253297436351596029575)
      ·
        refine ⟨35089879946154527394044363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23393253297436351596029575 35089879946154527394044363)
        ·
          refine ⟨52634819919231791091066545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35089879946154527394044363 52634819919231791091066545)
          ·
            refine ⟨39476114939423843318299909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52634819919231791091066545 39476114939423843318299909)
            ·
              refine ⟨7401771551141970622181233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39476114939423843318299909 7401771551141970622181233)
              ·
                refine ⟨5551328663356477966635925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7401771551141970622181233 5551328663356477966635925)
                ·
                  refine ⟨260218531094834904686059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5551328663356477966635925 260218531094834904686059)
                  ·
                    rfl

theorem cell21_1140241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_1140241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140241 prefixEnd_1140241 := by exact prefixLift 1140241
  have htrace : WordTrace (prefixWord ++ tailWord_1140241) baseStart_1140241 baseEnd_1140241 := by
    simpa [prefixWord, tailWord_1140241, baseEnd_1140241] using wordTrace_append hprefix tailTrace_1140241
  have hstable : (prefixWord ++ tailWord_1140241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140241).length < 2 ^ (prefixWord ++ tailWord_1140241).sum := by decide
  have hdescent : baseEnd_1140241 < baseStart_1140241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140275 : List Nat := [1, 1, 1, 2, 4, 4, 3, 1, 4]
def baseStart_1140275 : Nat := 118140960795 + 1140275 * 2 ^ 59
def prefixEnd_1140275 : Nat := 4983230072969 + 3 ^ 40 * 1140275 * 2
def baseEnd_1140275 : Nat := 260226290358058401119323

theorem tailTrace_1140275 : CollatzResearch.WordTrace tailWord_1140275 prefixEnd_1140275 260226290358058401119323 := by
  unfold tailWord_1140275
  simp only [CollatzResearch.WordTrace]
  refine ⟨41589245943985893310790279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27726163962657262207193519 41589245943985893310790279)
  ·
    refine ⟨62383868915978839966185419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41589245943985893310790279 62383868915978839966185419)
    ·
      refine ⟨93575803373968259949278129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62383868915978839966185419 93575803373968259949278129)
      ·
        refine ⟨70181852530476194961958597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93575803373968259949278129 70181852530476194961958597)
        ·
          refine ⟨13159097349464286555367237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70181852530476194961958597 13159097349464286555367237)
          ·
            refine ⟨2467330753024553729131357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13159097349464286555367237 2467330753024553729131357)
            ·
              refine ⟨925249032384207648424259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2467330753024553729131357 925249032384207648424259)
              ·
                refine ⟨1387873548576311472636389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925249032384207648424259 1387873548576311472636389)
                ·
                  refine ⟨260226290358058401119323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1387873548576311472636389 260226290358058401119323)
                  ·
                    rfl

theorem cell21_1140275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 1, 4].length) (baseStart_1140275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140275 prefixEnd_1140275 := by exact prefixLift 1140275
  have htrace : WordTrace (prefixWord ++ tailWord_1140275) baseStart_1140275 baseEnd_1140275 := by
    simpa [prefixWord, tailWord_1140275, baseEnd_1140275] using wordTrace_append hprefix tailTrace_1140275
  have hstable : (prefixWord ++ tailWord_1140275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140275).length < 2 ^ (prefixWord ++ tailWord_1140275).sum := by decide
  have hdescent : baseEnd_1140275 < baseStart_1140275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140382 : List Nat := [4, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1140382 : Nat := 118140960795 + 1140382 * 2 ^ 59
def prefixEnd_1140382 : Nat := 4983230072969 + 3 ^ 40 * 1140382 * 2
def baseEnd_1140382 : Nat := 86750236405283330945257

theorem tailTrace_1140382 : CollatzResearch.WordTrace tailWord_1140382 prefixEnd_1140382 86750236405283330945257 := by
  unfold tailWord_1140382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5199143569324781323116925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27728765703065500389956933 5199143569324781323116925)
  ·
    refine ⟨1949678838496792996168847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5199143569324781323116925 1949678838496792996168847)
    ·
      refine ⟨2924518257745189494253271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1949678838496792996168847 2924518257745189494253271)
      ·
        refine ⟨4386777386617784241379907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2924518257745189494253271 4386777386617784241379907)
        ·
          refine ⟨6580166079926676362069861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4386777386617784241379907 6580166079926676362069861)
          ·
            refine ⟨1233781139986251817888099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6580166079926676362069861 1233781139986251817888099)
            ·
              refine ⟨1850671709979377726832149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1233781139986251817888099 1850671709979377726832149)
              ·
                refine ⟨86750236405283330945257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1850671709979377726832149 86750236405283330945257)
                ·
                  rfl

theorem cell21_1140382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1140382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140382 prefixEnd_1140382 := by exact prefixLift 1140382
  have htrace : WordTrace (prefixWord ++ tailWord_1140382) baseStart_1140382 baseEnd_1140382 := by
    simpa [prefixWord, tailWord_1140382, baseEnd_1140382] using wordTrace_append hprefix tailTrace_1140382
  have hstable : (prefixWord ++ tailWord_1140382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140382).length < 2 ^ (prefixWord ++ tailWord_1140382).sum := by decide
  have hdescent : baseEnd_1140382 < baseStart_1140382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140483 : List Nat := [1, 1, 1, 3, 2, 2, 11]
def baseStart_1140483 : Nat := 118140960795 + 1140483 * 2 ^ 59
def prefixEnd_1140483 : Nat := 4983230072969 + 3 ^ 40 * 1140483 * 2
def baseEnd_1140483 : Nat := 28919306532432917961359

theorem tailTrace_1140483 : CollatzResearch.WordTrace tailWord_1140483 prefixEnd_1140483 28919306532432917961359 := by
  unfold tailWord_1140483
  simp only [CollatzResearch.WordTrace]
  refine ⟨41596832327232344834362103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27731221551488229889574735 41596832327232344834362103)
  ·
    refine ⟨62395248490848517251543155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41596832327232344834362103 62395248490848517251543155)
    ·
      refine ⟨93592872736272775877314733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62395248490848517251543155 93592872736272775877314733)
      ·
        refine ⟨35097327276102290953993025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93592872736272775877314733 35097327276102290953993025)
        ·
          refine ⟨26322995457076718215494769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35097327276102290953993025 26322995457076718215494769)
          ·
            refine ⟨19742246592807538661621077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26322995457076718215494769 19742246592807538661621077)
            ·
              refine ⟨28919306532432917961359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19742246592807538661621077 28919306532432917961359)
              ·
                rfl

theorem cell21_1140483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 11].length) (baseStart_1140483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140483 prefixEnd_1140483 := by exact prefixLift 1140483
  have htrace : WordTrace (prefixWord ++ tailWord_1140483) baseStart_1140483 baseEnd_1140483 := by
    simpa [prefixWord, tailWord_1140483, baseEnd_1140483] using wordTrace_append hprefix tailTrace_1140483
  have hstable : (prefixWord ++ tailWord_1140483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140483).length < 2 ^ (prefixWord ++ tailWord_1140483).sum := by decide
  have hdescent : baseEnd_1140483 < baseStart_1140483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140503 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 4]
def baseStart_1140503 : Nat := 118140960795 + 1140503 * 2 ^ 59
def prefixEnd_1140503 : Nat := 4983230072969 + 3 ^ 40 * 1140503 * 2
def baseEnd_1140503 : Nat := 260278323064380671318857

theorem tailTrace_1140503 : CollatzResearch.WordTrace tailWord_1140503 prefixEnd_1140503 260278323064380671318857 := by
  unfold tailWord_1140503
  simp only [CollatzResearch.WordTrace]
  refine ⟨41597561787159888250090163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27731707858106592166726775 41597561787159888250090163)
  ·
    refine ⟨62396342680739832375135245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41597561787159888250090163 62396342680739832375135245)
    ·
      refine ⟨23398628505277437140675717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62396342680739832375135245 23398628505277437140675717)
      ·
        refine ⟨4387242844739519463876697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23398628505277437140675717 4387242844739519463876697)
        ·
          refine ⟨3290432133554639597907523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4387242844739519463876697 3290432133554639597907523)
          ·
            refine ⟨4935648200331959396861285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3290432133554639597907523 4935648200331959396861285)
            ·
              refine ⟨925434037562242386911491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4935648200331959396861285 925434037562242386911491)
              ·
                refine ⟨1388151056343363580367237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 925434037562242386911491 1388151056343363580367237)
                ·
                  refine ⟨260278323064380671318857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388151056343363580367237 260278323064380671318857)
                  ·
                    rfl

theorem cell21_1140503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 4].length) (baseStart_1140503 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140503 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140503 prefixEnd_1140503 := by exact prefixLift 1140503
  have htrace : WordTrace (prefixWord ++ tailWord_1140503) baseStart_1140503 baseEnd_1140503 := by
    simpa [prefixWord, tailWord_1140503, baseEnd_1140503] using wordTrace_append hprefix tailTrace_1140503
  have hstable : (prefixWord ++ tailWord_1140503).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140503).length < 2 ^ (prefixWord ++ tailWord_1140503).sum := by decide
  have hdescent : baseEnd_1140503 < baseStart_1140503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140562 : List Nat := [3, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1140562 : Nat := 118140960795 + 1140562 * 2 ^ 59
def prefixEnd_1140562 : Nat := 4983230072969 + 3 ^ 40 * 1140562 * 2
def baseEnd_1140562 : Nat := 260291787668209679835403

theorem tailTrace_1140562 : CollatzResearch.WordTrace tailWord_1140562 prefixEnd_1140562 260291787668209679835403 := by
  unfold tailWord_1140562
  simp only [CollatzResearch.WordTrace]
  refine ⟨10399928423486535331621985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27733142462630760884325293 10399928423486535331621985)
  ·
    refine ⟨7799946317614901498716489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10399928423486535331621985 7799946317614901498716489)
    ·
      refine ⟨5849959738211176124037367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7799946317614901498716489 5849959738211176124037367)
      ·
        refine ⟨8774939607316764186056051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5849959738211176124037367 8774939607316764186056051)
        ·
          refine ⟨13162409410975146279084077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8774939607316764186056051 13162409410975146279084077)
          ·
            refine ⟨4935903529115679854656529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13162409410975146279084077 4935903529115679854656529)
            ·
              refine ⟨3701927646836759890992397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4935903529115679854656529 3701927646836759890992397)
              ·
                refine ⟨1388222867563784959122149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3701927646836759890992397 1388222867563784959122149)
                ·
                  refine ⟨260291787668209679835403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388222867563784959122149 260291787668209679835403)
                  ·
                    rfl

theorem cell21_1140562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1140562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140562 prefixEnd_1140562 := by exact prefixLift 1140562
  have htrace : WordTrace (prefixWord ++ tailWord_1140562) baseStart_1140562 baseEnd_1140562 := by
    simpa [prefixWord, tailWord_1140562, baseEnd_1140562] using wordTrace_append hprefix tailTrace_1140562
  have hstable : (prefixWord ++ tailWord_1140562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140562).length < 2 ^ (prefixWord ++ tailWord_1140562).sum := by decide
  have hdescent : baseEnd_1140562 < baseStart_1140562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140666 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_1140666 : Nat := 118140960795 + 1140666 * 2 ^ 59
def prefixEnd_1140666 : Nat := 4983230072969 + 3 ^ 40 * 1140666 * 2
def baseEnd_1140666 : Nat := 260315521885128610101857

theorem tailTrace_1140666 : CollatzResearch.WordTrace tailWord_1140666 prefixEnd_1140666 260315521885128610101857 := by
  unfold tailWord_1140666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10400876721392341772068463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27735671257046244725515901 10400876721392341772068463)
  ·
    refine ⟨15601315082088512658102695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10400876721392341772068463 15601315082088512658102695)
    ·
      refine ⟨23401972623132768987154043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15601315082088512658102695 23401972623132768987154043)
      ·
        refine ⟨35102958934699153480731065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23401972623132768987154043 35102958934699153480731065)
        ·
          refine ⟨26327219201024365110548299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35102958934699153480731065 26327219201024365110548299)
          ·
            refine ⟨39490828801536547665822449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26327219201024365110548299 39490828801536547665822449)
            ·
              refine ⟨29618121601152410749366837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39490828801536547665822449 29618121601152410749366837)
              ·
                refine ⟨2776698900108038507753141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29618121601152410749366837 2776698900108038507753141)
                ·
                  refine ⟨260315521885128610101857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2776698900108038507753141 260315521885128610101857)
                  ·
                    rfl

theorem cell21_1140666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_1140666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140666 prefixEnd_1140666 := by exact prefixLift 1140666
  have htrace : WordTrace (prefixWord ++ tailWord_1140666) baseStart_1140666 baseEnd_1140666 := by
    simpa [prefixWord, tailWord_1140666, baseEnd_1140666] using wordTrace_append hprefix tailTrace_1140666
  have hstable : (prefixWord ++ tailWord_1140666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140666).length < 2 ^ (prefixWord ++ tailWord_1140666).sum := by decide
  have hdescent : baseEnd_1140666 < baseStart_1140666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140711 : List Nat := [1, 1, 5, 2, 12]
def baseStart_1140711 : Nat := 118140960795 + 1140711 * 2 ^ 59
def prefixEnd_1140711 : Nat := 4983230072969 + 3 ^ 40 * 1140711 * 2
def baseEnd_1140711 : Nat := 3213898660471833726565

theorem tailTrace_1140711 : CollatzResearch.WordTrace tailWord_1140711 prefixEnd_1140711 3213898660471833726565 := by
  unfold tailWord_1140711
  simp only [CollatzResearch.WordTrace]
  refine ⟨41605148170406339773661987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27736765446937559849107991 41605148170406339773661987)
  ·
    refine ⟨62407722255609509660492981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41605148170406339773661987 62407722255609509660492981)
    ·
      refine ⟨5850723961463391530671217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62407722255609509660492981 5850723961463391530671217)
      ·
        refine ⟨4388042971097543648003413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5850723961463391530671217 4388042971097543648003413)
        ·
          refine ⟨3213898660471833726565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4388042971097543648003413 3213898660471833726565)
          ·
            rfl

theorem cell21_1140711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 12].length) (baseStart_1140711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140711 prefixEnd_1140711 := by exact prefixLift 1140711
  have htrace : WordTrace (prefixWord ++ tailWord_1140711) baseStart_1140711 baseEnd_1140711 := by
    simpa [prefixWord, tailWord_1140711, baseEnd_1140711] using wordTrace_append hprefix tailTrace_1140711
  have hstable : (prefixWord ++ tailWord_1140711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140711).length < 2 ^ (prefixWord ++ tailWord_1140711).sum := by decide
  have hdescent : baseEnd_1140711 < baseStart_1140711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140714 : List Nat := [3, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_1140714 : Nat := 118140960795 + 1140714 * 2 ^ 59
def prefixEnd_1140714 : Nat := 4983230072969 + 3 ^ 40 * 1140714 * 2
def baseEnd_1140714 : Nat := 260326476139091193301759

theorem tailTrace_1140714 : CollatzResearch.WordTrace tailWord_1140714 prefixEnd_1140714 260326476139091193301759 := by
  unfold tailWord_1140714
  simp only [CollatzResearch.WordTrace]
  refine ⟨10401314397348867821505299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27736838392930314190680797 10401314397348867821505299)
  ·
    refine ⟨15601971596023301732257949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10401314397348867821505299 15601971596023301732257949)
    ·
      refine ⟨5850739348508738149596731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15601971596023301732257949 5850739348508738149596731)
      ·
        refine ⟨8776109022763107224395097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5850739348508738149596731 8776109022763107224395097)
        ·
          refine ⟨6582081767072330418296323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8776109022763107224395097 6582081767072330418296323)
          ·
            refine ⟨9873122650608495627444485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6582081767072330418296323 9873122650608495627444485)
            ·
              refine ⟨1851210496989092930145841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9873122650608495627444485 1851210496989092930145841)
              ·
                refine ⟨1388407872741819697609381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851210496989092930145841 1388407872741819697609381)
                ·
                  refine ⟨260326476139091193301759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388407872741819697609381 260326476139091193301759)
                  ·
                    rfl

theorem cell21_1140714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_1140714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140714 prefixEnd_1140714 := by exact prefixLift 1140714
  have htrace : WordTrace (prefixWord ++ tailWord_1140714) baseStart_1140714 baseEnd_1140714 := by
    simpa [prefixWord, tailWord_1140714, baseEnd_1140714] using wordTrace_append hprefix tailTrace_1140714
  have hstable : (prefixWord ++ tailWord_1140714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140714).length < 2 ^ (prefixWord ++ tailWord_1140714).sum := by decide
  have hdescent : baseEnd_1140714 < baseStart_1140714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140773 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 6]
def baseStart_1140773 : Nat := 118140960795 + 1140773 * 2 ^ 59
def prefixEnd_1140773 : Nat := 4983230072969 + 3 ^ 40 * 1140773 * 2
def baseEnd_1140773 : Nat := 260339940742920201818305

theorem tailTrace_1140773 : CollatzResearch.WordTrace tailWord_1140773 prefixEnd_1140773 260339940742920201818305 := by
  unfold tailWord_1140773
  simp only [CollatzResearch.WordTrace]
  refine ⟨41607409496181724362418973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27738272997454482908279315 41607409496181724362418973)
  ·
    refine ⟨15602778561068146635907115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41607409496181724362418973 15602778561068146635907115)
    ·
      refine ⟨23404167841602219953860673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15602778561068146635907115 23404167841602219953860673)
      ·
        refine ⟨17553125881201664965395505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23404167841602219953860673 17553125881201664965395505)
        ·
          refine ⟨13164844410901248724046629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17553125881201664965395505 13164844410901248724046629)
          ·
            refine ⟨2468408327043984135758743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13164844410901248724046629 2468408327043984135758743)
            ·
              refine ⟨3702612490565976203638115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468408327043984135758743 3702612490565976203638115)
              ·
                refine ⟨5553918735848964305457173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3702612490565976203638115 5553918735848964305457173)
                ·
                  refine ⟨260339940742920201818305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5553918735848964305457173 260339940742920201818305)
                  ·
                    rfl

theorem cell21_1140773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_1140773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140773 prefixEnd_1140773 := by exact prefixLift 1140773
  have htrace : WordTrace (prefixWord ++ tailWord_1140773) baseStart_1140773 baseEnd_1140773 := by
    simpa [prefixWord, tailWord_1140773, baseEnd_1140773] using wordTrace_append hprefix tailTrace_1140773
  have hstable : (prefixWord ++ tailWord_1140773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140773).length < 2 ^ (prefixWord ++ tailWord_1140773).sum := by decide
  have hdescent : baseEnd_1140773 < baseStart_1140773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140835 : List Nat := [1, 1, 1, 5, 1, 1, 2, 6, 3]
def baseStart_1140835 : Nat := 118140960795 + 1140835 * 2 ^ 59
def prefixEnd_1140835 : Nat := 4983230072969 + 3 ^ 40 * 1140835 * 2
def baseEnd_1140835 : Nat := 260354089987621871784845

theorem tailTrace_1140835 : CollatzResearch.WordTrace tailWord_1140835 prefixEnd_1140835 260354089987621871784845 := by
  unfold tailWord_1140835
  simp only [CollatzResearch.WordTrace]
  refine ⟨41609670821957108951175959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27739780547971405967450639 41609670821957108951175959)
  ·
    refine ⟨62414506232935663426763939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41609670821957108951175959 62414506232935663426763939)
    ·
      refine ⟨93621759349403495140145909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62414506232935663426763939 93621759349403495140145909)
      ·
        refine ⟨8777039939006577669388679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93621759349403495140145909 8777039939006577669388679)
        ·
          refine ⟨13165559908509866504083019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8777039939006577669388679 13165559908509866504083019)
          ·
            refine ⟨19748339862764799756124529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13165559908509866504083019 19748339862764799756124529)
            ·
              refine ⟨14811254897073599817093397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19748339862764799756124529 14811254897073599817093397)
              ·
                refine ⟨694277573300324991426253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 14811254897073599817093397 694277573300324991426253)
                ·
                  refine ⟨260354089987621871784845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694277573300324991426253 260354089987621871784845)
                  ·
                    rfl

theorem cell21_1140835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 3].length) (baseStart_1140835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140835 prefixEnd_1140835 := by exact prefixLift 1140835
  have htrace : WordTrace (prefixWord ++ tailWord_1140835) baseStart_1140835 baseEnd_1140835 := by
    simpa [prefixWord, tailWord_1140835, baseEnd_1140835] using wordTrace_append hprefix tailTrace_1140835
  have hstable : (prefixWord ++ tailWord_1140835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140835).length < 2 ^ (prefixWord ++ tailWord_1140835).sum := by decide
  have hdescent : baseEnd_1140835 < baseStart_1140835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140849 : List Nat := [1, 2, 2, 2, 1, 1, 5, 3, 4]
def baseStart_1140849 : Nat := 118140960795 + 1140849 * 2 ^ 59
def prefixEnd_1140849 : Nat := 4983230072969 + 3 ^ 40 * 1140849 * 2
def baseEnd_1140849 : Nat := 260357284978360958551483

theorem tailTrace_1140849 : CollatzResearch.WordTrace tailWord_1140849 prefixEnd_1140849 260357284978360958551483 := by
  unfold tailWord_1140849
  simp only [CollatzResearch.WordTrace]
  refine ⟨41610181443906389342185601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27740120962604259561457067 41610181443906389342185601)
  ·
    refine ⟨31207636082929792006639201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41610181443906389342185601 31207636082929792006639201)
    ·
      refine ⟨23405727062197344004979401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31207636082929792006639201 23405727062197344004979401)
      ·
        refine ⟨17554295296648008003734551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23405727062197344004979401 17554295296648008003734551)
        ·
          refine ⟨26331442944972012005601827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17554295296648008003734551 26331442944972012005601827)
          ·
            refine ⟨39497164417458018008402741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26331442944972012005601827 39497164417458018008402741)
            ·
              refine ⟨3702859164136689188287757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39497164417458018008402741 3702859164136689188287757)
              ·
                refine ⟨1388572186551258445607909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3702859164136689188287757 1388572186551258445607909)
                ·
                  refine ⟨260357284978360958551483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388572186551258445607909 260357284978360958551483)
                  ·
                    rfl

theorem cell21_1140849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 3, 4].length) (baseStart_1140849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140849 prefixEnd_1140849 := by exact prefixLift 1140849
  have htrace : WordTrace (prefixWord ++ tailWord_1140849) baseStart_1140849 baseEnd_1140849 := by
    simpa [prefixWord, tailWord_1140849, baseEnd_1140849] using wordTrace_append hprefix tailTrace_1140849
  have hstable : (prefixWord ++ tailWord_1140849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140849).length < 2 ^ (prefixWord ++ tailWord_1140849).sum := by decide
  have hdescent : baseEnd_1140849 < baseStart_1140849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140928 : List Nat := [2, 1, 1, 2, 5, 2, 2, 3, 3]
def baseStart_1140928 : Nat := 118140960795 + 1140928 * 2 ^ 59
def prefixEnd_1140928 : Nat := 4983230072969 + 3 ^ 40 * 1140928 * 2
def baseEnd_1140928 : Nat := 260375313854674376734655

theorem tailTrace_1140928 : CollatzResearch.WordTrace tailWord_1140928 prefixEnd_1140928 260375313854674376734655 := by
  unfold tailWord_1140928
  simp only [CollatzResearch.WordTrace]
  refine ⟨20806531405310092917155719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27742041873746790556207625 20806531405310092917155719)
  ·
    refine ⟨31209797107965139375733579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20806531405310092917155719 31209797107965139375733579)
    ·
      refine ⟨46814695661947709063600369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31209797107965139375733579 46814695661947709063600369)
      ·
        refine ⟨35111021746460781797700277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46814695661947709063600369 35111021746460781797700277)
        ·
          refine ⟨3291658288730698293534401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35111021746460781797700277 3291658288730698293534401)
          ·
            refine ⟨2468743716548023720150801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3291658288730698293534401 2468743716548023720150801)
            ·
              refine ⟨1851557787411017790113101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2468743716548023720150801 1851557787411017790113101)
              ·
                refine ⟨694334170279131671292413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1851557787411017790113101 694334170279131671292413)
                ·
                  refine ⟨260375313854674376734655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694334170279131671292413 260375313854674376734655)
                  ·
                    rfl

theorem cell21_1140928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 3, 3].length) (baseStart_1140928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140928 prefixEnd_1140928 := by exact prefixLift 1140928
  have htrace : WordTrace (prefixWord ++ tailWord_1140928) baseStart_1140928 baseEnd_1140928 := by
    simpa [prefixWord, tailWord_1140928, baseEnd_1140928] using wordTrace_append hprefix tailTrace_1140928
  have hstable : (prefixWord ++ tailWord_1140928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140928).length < 2 ^ (prefixWord ++ tailWord_1140928).sum := by decide
  have hdescent : baseEnd_1140928 < baseStart_1140928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140942 : List Nat := [4, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_1140942 : Nat := 118140960795 + 1140942 * 2 ^ 59
def prefixEnd_1140942 : Nat := 4983230072969 + 3 ^ 40 * 1140942 * 2
def baseEnd_1140942 : Nat := 260378508845413463501293

theorem tailTrace_1140942 : CollatzResearch.WordTrace tailWord_1140942 prefixEnd_1140942 260378508845413463501293 := by
  unfold tailWord_1140942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5201696679071183278165135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27742382288379644150214053 5201696679071183278165135)
  ·
    refine ⟨7802545018606774917247703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5201696679071183278165135 7802545018606774917247703)
    ·
      refine ⟨11703817527910162375871555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7802545018606774917247703 11703817527910162375871555)
      ·
        refine ⟨17555726291865243563807333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11703817527910162375871555 17555726291865243563807333)
        ·
          refine ⟨3291698679724733168213875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17555726291865243563807333 3291698679724733168213875)
          ·
            refine ⟨4937548019587099752320813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3291698679724733168213875 4937548019587099752320813)
            ·
              refine ⟨1851580507345162407120305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4937548019587099752320813 1851580507345162407120305)
              ·
                refine ⟨1388685380508871805340229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1851580507345162407120305 1388685380508871805340229)
                ·
                  refine ⟨260378508845413463501293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388685380508871805340229 260378508845413463501293)
                  ·
                    rfl

theorem cell21_1140942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_1140942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140942 prefixEnd_1140942 := by exact prefixLift 1140942
  have htrace : WordTrace (prefixWord ++ tailWord_1140942) baseStart_1140942 baseEnd_1140942 := by
    simpa [prefixWord, tailWord_1140942, baseEnd_1140942] using wordTrace_append hprefix tailTrace_1140942
  have hstable : (prefixWord ++ tailWord_1140942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140942).length < 2 ^ (prefixWord ++ tailWord_1140942).sum := by decide
  have hdescent : baseEnd_1140942 < baseStart_1140942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1140970 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1140970 : Nat := 118140960795 + 1140970 * 2 ^ 59
def prefixEnd_1140970 : Nat := 4983230072969 + 3 ^ 40 * 1140970 * 2
def baseEnd_1140970 : Nat := 260384898826891637034569

theorem tailTrace_1140970 : CollatzResearch.WordTrace tailWord_1140970 prefixEnd_1140970 260384898826891637034569 := by
  unfold tailWord_1140970
  simp only [CollatzResearch.WordTrace]
  refine ⟨10403648669117006751835091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27743063117645351338226909 10403648669117006751835091)
  ·
    refine ⟨15605473003675510127752637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10403648669117006751835091 15605473003675510127752637)
    ·
      refine ⟨5852052376378316297907239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15605473003675510127752637 5852052376378316297907239)
      ·
        refine ⟨8778078564567474446860859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5852052376378316297907239 8778078564567474446860859)
        ·
          refine ⟨13167117846851211670291289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8778078564567474446860859 13167117846851211670291289)
          ·
            refine ⟨9875338385138408752718467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13167117846851211670291289 9875338385138408752718467)
            ·
              refine ⟨14813007577707613129077701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9875338385138408752718467 14813007577707613129077701)
              ·
                refine ⟨2777438920820177461702069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14813007577707613129077701 2777438920820177461702069)
                ·
                  refine ⟨260384898826891637034569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2777438920820177461702069 260384898826891637034569)
                  ·
                    rfl

theorem cell21_1140970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1140970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1140970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1140970 prefixEnd_1140970 := by exact prefixLift 1140970
  have htrace : WordTrace (prefixWord ++ tailWord_1140970) baseStart_1140970 baseEnd_1140970 := by
    simpa [prefixWord, tailWord_1140970, baseEnd_1140970] using wordTrace_append hprefix tailTrace_1140970
  have hstable : (prefixWord ++ tailWord_1140970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1140970).length < 2 ^ (prefixWord ++ tailWord_1140970).sum := by decide
  have hdescent : baseEnd_1140970 < baseStart_1140970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1140970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141004 : List Nat := [2, 2, 1, 2, 2, 2, 5, 2, 3]
def baseStart_1141004 : Nat := 118140960795 + 1141004 * 2 ^ 59
def prefixEnd_1141004 : Nat := 4983230072969 + 3 ^ 40 * 1141004 * 2
def baseEnd_1141004 : Nat := 260392658090115133467833

theorem tailTrace_1141004 : CollatzResearch.WordTrace tailWord_1141004 prefixEnd_1141004 260392658090115133467833 := by
  unfold tailWord_1141004
  simp only [CollatzResearch.WordTrace]
  refine ⟨20807917379172425407039033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27743889838896567209385377 20807917379172425407039033)
  ·
    refine ⟨15605938034379319055279275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20807917379172425407039033 15605938034379319055279275)
    ·
      refine ⟨23408907051568978582918913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15605938034379319055279275 23408907051568978582918913)
      ·
        refine ⟨17556680288676733937189185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23408907051568978582918913 17556680288676733937189185)
        ·
          refine ⟨13167510216507550452891889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17556680288676733937189185 13167510216507550452891889)
          ·
            refine ⟨9875632662380662839668917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13167510216507550452891889 9875632662380662839668917)
            ·
              refine ⟨925840562098187141218961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9875632662380662839668917 925840562098187141218961)
              ·
                refine ⟨694380421573640355914221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925840562098187141218961 694380421573640355914221)
                ·
                  refine ⟨260392658090115133467833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694380421573640355914221 260392658090115133467833)
                  ·
                    rfl

theorem cell21_1141004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 2, 3].length) (baseStart_1141004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141004 prefixEnd_1141004 := by exact prefixLift 1141004
  have htrace : WordTrace (prefixWord ++ tailWord_1141004) baseStart_1141004 baseEnd_1141004 := by
    simpa [prefixWord, tailWord_1141004, baseEnd_1141004] using wordTrace_append hprefix tailTrace_1141004
  have hstable : (prefixWord ++ tailWord_1141004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141004).length < 2 ^ (prefixWord ++ tailWord_1141004).sum := by decide
  have hdescent : baseEnd_1141004 < baseStart_1141004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141015 : List Nat := [1, 1, 3, 4, 1, 2, 1, 8]
def baseStart_1141015 : Nat := 118140960795 + 1141015 * 2 ^ 59
def prefixEnd_1141015 : Nat := 4983230072969 + 3 ^ 40 * 1141015 * 2
def baseEnd_1141015 : Nat := 86798389479993852928159

theorem tailTrace_1141015 : CollatzResearch.WordTrace tailWord_1141015 prefixEnd_1141015 86798389479993852928159 := by
  unfold tailWord_1141015
  simp only [CollatzResearch.WordTrace]
  refine ⟨41616235961304999692728499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27744157307536666461818999 41616235961304999692728499)
  ·
    refine ⟨62424353941957499539092749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41616235961304999692728499 62424353941957499539092749)
    ·
      refine ⟨23409132728234062327159781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62424353941957499539092749 23409132728234062327159781)
      ·
        refine ⟨4389212386543886686342459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23409132728234062327159781 4389212386543886686342459)
        ·
          refine ⟨6583818579815830029513689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4389212386543886686342459 6583818579815830029513689)
          ·
            refine ⟨4937863934861872522135267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6583818579815830029513689 4937863934861872522135267)
            ·
              refine ⟨7406795902292808783202901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4937863934861872522135267 7406795902292808783202901)
              ·
                refine ⟨86798389479993852928159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7406795902292808783202901 86798389479993852928159)
                ·
                  rfl

theorem cell21_1141015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_1141015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141015 prefixEnd_1141015 := by exact prefixLift 1141015
  have htrace : WordTrace (prefixWord ++ tailWord_1141015) baseStart_1141015 baseEnd_1141015 := by
    simpa [prefixWord, tailWord_1141015, baseEnd_1141015] using wordTrace_append hprefix tailTrace_1141015
  have hstable : (prefixWord ++ tailWord_1141015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141015).length < 2 ^ (prefixWord ++ tailWord_1141015).sum := by decide
  have hdescent : baseEnd_1141015 < baseStart_1141015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141018 : List Nat := [3, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_1141018 : Nat := 118140960795 + 1141018 * 2 ^ 59
def prefixEnd_1141018 : Nat := 4983230072969 + 3 ^ 40 * 1141018 * 2
def baseEnd_1141018 : Nat := 260395853080854220234471

theorem tailTrace_1141018 : CollatzResearch.WordTrace tailWord_1141018 prefixEnd_1141018 260395853080854220234471 := by
  unfold tailWord_1141018
  simp only [CollatzResearch.WordTrace]
  refine ⟨10404086345073532801271927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 27744230253529420803391805 10404086345073532801271927)
  ·
    refine ⟨15606129517610299201907891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10404086345073532801271927 15606129517610299201907891)
    ·
      refine ⟨23409194276415448802861837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15606129517610299201907891 23409194276415448802861837)
      ·
        refine ⟨8778447853655793301073189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23409194276415448802861837 8778447853655793301073189)
        ·
          refine ⟨1645958972560461243951223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8778447853655793301073189 1645958972560461243951223)
          ·
            refine ⟨2468938458840691865926835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1645958972560461243951223 2468938458840691865926835)
            ·
              refine ⟨3703407688261037798890253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2468938458840691865926835 3703407688261037798890253)
              ·
                refine ⟨1388777883097889174583845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3703407688261037798890253 1388777883097889174583845)
                ·
                  refine ⟨260395853080854220234471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1388777883097889174583845 260395853080854220234471)
                  ·
                    rfl

theorem cell21_1141018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_1141018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141018 prefixEnd_1141018 := by exact prefixLift 1141018
  have htrace : WordTrace (prefixWord ++ tailWord_1141018) baseStart_1141018 baseEnd_1141018 := by
    simpa [prefixWord, tailWord_1141018, baseEnd_1141018] using wordTrace_append hprefix tailTrace_1141018
  have hstable : (prefixWord ++ tailWord_1141018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141018).length < 2 ^ (prefixWord ++ tailWord_1141018).sum := by decide
  have hdescent : baseEnd_1141018 < baseStart_1141018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141063 : List Nat := [1, 1, 4, 1, 2, 2, 3, 4, 3]
def baseStart_1141063 : Nat := 118140960795 + 1141063 * 2 ^ 59
def prefixEnd_1141063 : Nat := 4983230072969 + 3 ^ 40 * 1141063 * 2
def baseEnd_1141063 : Nat := 260406122693944141984379

theorem tailTrace_1141063 : CollatzResearch.WordTrace tailWord_1141063 prefixEnd_1141063 260406122693944141984379 := by
  unfold tailWord_1141063
  simp only [CollatzResearch.WordTrace]
  refine ⟨41617986665131103890475843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27745324443420735926983895 41617986665131103890475843)
  ·
    refine ⟨62426979997696655835713765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41617986665131103890475843 62426979997696655835713765)
    ·
      refine ⟨11705058749568122969196331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62426979997696655835713765 11705058749568122969196331)
      ·
        refine ⟨17557588124352184453794497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11705058749568122969196331 17557588124352184453794497)
        ·
          refine ⟨13168191093264138340345873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17557588124352184453794497 13168191093264138340345873)
          ·
            refine ⟨9876143319948103755259405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13168191093264138340345873 9876143319948103755259405)
            ·
              refine ⟨3703553744980538908222277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9876143319948103755259405 3703553744980538908222277)
              ·
                refine ⟨694416327183851045291677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3703553744980538908222277 694416327183851045291677)
                ·
                  refine ⟨260406122693944141984379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694416327183851045291677 260406122693944141984379)
                  ·
                    rfl

theorem cell21_1141063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 4, 3].length) (baseStart_1141063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141063 prefixEnd_1141063 := by exact prefixLift 1141063
  have htrace : WordTrace (prefixWord ++ tailWord_1141063) baseStart_1141063 baseEnd_1141063 := by
    simpa [prefixWord, tailWord_1141063, baseEnd_1141063] using wordTrace_append hprefix tailTrace_1141063
  have hstable : (prefixWord ++ tailWord_1141063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141063).length < 2 ^ (prefixWord ++ tailWord_1141063).sum := by decide
  have hdescent : baseEnd_1141063 < baseStart_1141063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141105 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_1141105 : Nat := 118140960795 + 1141105 * 2 ^ 59
def prefixEnd_1141105 : Nat := 4983230072969 + 3 ^ 40 * 1141105 * 2
def baseEnd_1141105 : Nat := 260415707666161402284293

theorem tailTrace_1141105 : CollatzResearch.WordTrace tailWord_1141105 prefixEnd_1141105 260415707666161402284293 := by
  unfold tailWord_1141105
  simp only [CollatzResearch.WordTrace]
  refine ⟨41619518530978945063504769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27746345687319296709003179 41619518530978945063504769)
  ·
    refine ⟨31214638898234208797628577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41619518530978945063504769 31214638898234208797628577)
    ·
      refine ⟨23410979173675656598221433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31214638898234208797628577 23410979173675656598221433)
      ·
        refine ⟨17558234380256742448666075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23410979173675656598221433 17558234380256742448666075)
        ·
          refine ⟨26337351570385113672999113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17558234380256742448666075 26337351570385113672999113)
          ·
            refine ⟨19753013677788835254749335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26337351570385113672999113 19753013677788835254749335)
            ·
              refine ⟨29629520516683252882124003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19753013677788835254749335 29629520516683252882124003)
              ·
                refine ⟨44444280775024879323186005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29629520516683252882124003 44444280775024879323186005)
                ·
                  refine ⟨260415707666161402284293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44444280775024879323186005 260415707666161402284293)
                  ·
                    rfl

theorem cell21_1141105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_1141105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141105 prefixEnd_1141105 := by exact prefixLift 1141105
  have htrace : WordTrace (prefixWord ++ tailWord_1141105) baseStart_1141105 baseEnd_1141105 := by
    simpa [prefixWord, tailWord_1141105, baseEnd_1141105] using wordTrace_append hprefix tailTrace_1141105
  have hstable : (prefixWord ++ tailWord_1141105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141105).length < 2 ^ (prefixWord ++ tailWord_1141105).sum := by decide
  have hdescent : baseEnd_1141105 < baseStart_1141105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141173 : List Nat := [1, 3, 3, 2, 3, 1, 3, 2, 3]
def baseStart_1141173 : Nat := 118140960795 + 1141173 * 2 ^ 59
def prefixEnd_1141173 : Nat := 4983230072969 + 3 ^ 40 * 1141173 * 2
def baseEnd_1141173 : Nat := 260431226192608395150821

theorem tailTrace_1141173 : CollatzResearch.WordTrace tailWord_1141173 prefixEnd_1141173 260431226192608395150821 := by
  unfold tailWord_1141173
  simp only [CollatzResearch.WordTrace]
  refine ⟨41621998694732592676980173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27747999129821728451320115 41621998694732592676980173)
  ·
    refine ⟨15608249510524722253867565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41621998694732592676980173 15608249510524722253867565)
    ·
      refine ⟨5853093566446770845200337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15608249510524722253867565 5853093566446770845200337)
      ·
        refine ⟨4389820174835078133900253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5853093566446770845200337 4389820174835078133900253)
        ·
          refine ⟨1646182565563154300212595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4389820174835078133900253 1646182565563154300212595)
          ·
            refine ⟨2469273848344731450318893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646182565563154300212595 2469273848344731450318893)
            ·
              refine ⟨925977693129274293869585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2469273848344731450318893 925977693129274293869585)
              ·
                refine ⟨694483269846955720402189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925977693129274293869585 694483269846955720402189)
                ·
                  refine ⟨260431226192608395150821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694483269846955720402189 260431226192608395150821)
                  ·
                    rfl

theorem cell21_1141173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_1141173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141173 prefixEnd_1141173 := by exact prefixLift 1141173
  have htrace : WordTrace (prefixWord ++ tailWord_1141173) baseStart_1141173 baseEnd_1141173 := by
    simpa [prefixWord, tailWord_1141173, baseEnd_1141173] using wordTrace_append hprefix tailTrace_1141173
  have hstable : (prefixWord ++ tailWord_1141173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141173).length < 2 ^ (prefixWord ++ tailWord_1141173).sum := by decide
  have hdescent : baseEnd_1141173 < baseStart_1141173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141260 : List Nat := [2, 2, 1, 2, 4, 2, 3, 5]
def baseStart_1141260 : Nat := 118140960795 + 1141260 * 2 ^ 59
def prefixEnd_1141260 : Nat := 4983230072969 + 3 ^ 40 * 1141260 * 2
def baseEnd_1141260 : Nat := 86817026925971859066881

theorem tailTrace_1141260 : CollatzResearch.WordTrace tailWord_1141260 prefixEnd_1141260 86817026925971859066881 := by
  unfold tailWord_1141260
  simp only [CollatzResearch.WordTrace]
  refine ⟨20812585922708703267698617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27750114563611604356931489 20812585922708703267698617)
  ·
    refine ⟨15609439442031527450773963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20812585922708703267698617 15609439442031527450773963)
    ·
      refine ⟨23414159163047291176160945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15609439442031527450773963 23414159163047291176160945)
      ·
        refine ⟨17560619372285468382120709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23414159163047291176160945 17560619372285468382120709)
        ·
          refine ⟨3292616132303525321647633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17560619372285468382120709 3292616132303525321647633)
          ·
            refine ⟨2469462099227643991235725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3292616132303525321647633 2469462099227643991235725)
            ·
              refine ⟨926048287210366496713397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2469462099227643991235725 926048287210366496713397)
              ·
                refine ⟨86817026925971859066881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 926048287210366496713397 86817026925971859066881)
                ·
                  rfl

theorem cell21_1141260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_1141260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141260 prefixEnd_1141260 := by exact prefixLift 1141260
  have htrace : WordTrace (prefixWord ++ tailWord_1141260) baseStart_1141260 baseEnd_1141260 := by
    simpa [prefixWord, tailWord_1141260, baseEnd_1141260] using wordTrace_append hprefix tailTrace_1141260
  have hstable : (prefixWord ++ tailWord_1141260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141260).length < 2 ^ (prefixWord ++ tailWord_1141260).sum := by decide
  have hdescent : baseEnd_1141260 < baseStart_1141260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141319 : List Nat := [1, 1, 4, 1, 4, 2, 1, 7]
def baseStart_1141319 : Nat := 118140960795 + 1141319 * 2 ^ 59
def prefixEnd_1141319 : Nat := 4983230072969 + 3 ^ 40 * 1141319 * 2
def baseEnd_1141319 : Nat := 86821515127248195239063

theorem tailTrace_1141319 : CollatzResearch.WordTrace tailWord_1141319 prefixEnd_1141319 86821515127248195239063 := by
  unfold tailWord_1141319
  simp only [CollatzResearch.WordTrace]
  refine ⟨41627323752203659611795011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27751549168135773074530007 41627323752203659611795011)
  ·
    refine ⟨62440985628305489417692517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41627323752203659611795011 62440985628305489417692517)
    ·
      refine ⟨11707684805307279265817347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62440985628305489417692517 11707684805307279265817347)
      ·
        refine ⟨17561527207960918898726021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11707684805307279265817347 17561527207960918898726021)
        ·
          refine ⟨3292786351492672293511129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17561527207960918898726021 3292786351492672293511129)
          ·
            refine ⟨2469589763619504220133347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3292786351492672293511129 2469589763619504220133347)
            ·
              refine ⟨3704384645429256330200021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469589763619504220133347 3704384645429256330200021)
              ·
                refine ⟨86821515127248195239063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3704384645429256330200021 86821515127248195239063)
                ·
                  rfl

theorem cell21_1141319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 7].length) (baseStart_1141319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141319 prefixEnd_1141319 := by exact prefixLift 1141319
  have htrace : WordTrace (prefixWord ++ tailWord_1141319) baseStart_1141319 baseEnd_1141319 := by
    simpa [prefixWord, tailWord_1141319, baseEnd_1141319] using wordTrace_append hprefix tailTrace_1141319
  have hstable : (prefixWord ++ tailWord_1141319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141319).length < 2 ^ (prefixWord ++ tailWord_1141319).sum := by decide
  have hdescent : baseEnd_1141319 < baseStart_1141319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141325 : List Nat := [1, 6, 1, 1, 2, 3, 1, 3, 3]
def baseStart_1141325 : Nat := 118140960795 + 1141325 * 2 ^ 59
def prefixEnd_1141325 : Nat := 4983230072969 + 3 ^ 40 * 1141325 * 2
def baseEnd_1141325 : Nat := 260465914663489908617177

theorem tailTrace_1141325 : CollatzResearch.WordTrace tailWord_1141325 prefixEnd_1141325 260465914663489908617177 := by
  unfold tailWord_1141325
  simp only [CollatzResearch.WordTrace]
  refine ⟨41627542590181922636513429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27751695060121281757675619 41627542590181922636513429)
  ·
    refine ⟨1951291058914777623586567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41627542590181922636513429 1951291058914777623586567)
    ·
      refine ⟨2926936588372166435379851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951291058914777623586567 2926936588372166435379851)
      ·
        refine ⟨4390404882558249653069777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2926936588372166435379851 4390404882558249653069777)
        ·
          refine ⟨3292803661918687239802333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4390404882558249653069777 3292803661918687239802333)
          ·
            refine ⟨1234801373219507714925875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3292803661918687239802333 1234801373219507714925875)
            ·
              refine ⟨1852202059829261572388813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234801373219507714925875 1852202059829261572388813)
              ·
                refine ⟨694575772435973089645805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1852202059829261572388813 694575772435973089645805)
                ·
                  refine ⟨260465914663489908617177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694575772435973089645805 260465914663489908617177)
                  ·
                    rfl

theorem cell21_1141325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_1141325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141325 prefixEnd_1141325 := by exact prefixLift 1141325
  have htrace : WordTrace (prefixWord ++ tailWord_1141325) baseStart_1141325 baseEnd_1141325 := by
    simpa [prefixWord, tailWord_1141325, baseEnd_1141325] using wordTrace_append hprefix tailTrace_1141325
  have hstable : (prefixWord ++ tailWord_1141325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141325).length < 2 ^ (prefixWord ++ tailWord_1141325).sum := by decide
  have hdescent : baseEnd_1141325 < baseStart_1141325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141333 : List Nat := [1, 3, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1141333 : Nat := 118140960795 + 1141333 * 2 ^ 59
def prefixEnd_1141333 : Nat := 4983230072969 + 3 ^ 40 * 1141333 * 2
def baseEnd_1141333 : Nat := 260467740372483672483827

theorem tailTrace_1141333 : CollatzResearch.WordTrace tailWord_1141333 prefixEnd_1141333 260467740372483672483827 := by
  unfold tailWord_1141333
  simp only [CollatzResearch.WordTrace]
  refine ⟨41627834374152940002804653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27751889582768626668536435 41627834374152940002804653)
  ·
    refine ⟨15610437890307352501051745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41627834374152940002804653 15610437890307352501051745)
    ·
      refine ⟨11707828417730514375788809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15610437890307352501051745 11707828417730514375788809)
      ·
        refine ⟨8780871313297885781841607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11707828417730514375788809 8780871313297885781841607)
        ·
          refine ⟨13171306969946828672762411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8780871313297885781841607 13171306969946828672762411)
          ·
            refine ⟨19756960454920243009143617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13171306969946828672762411 19756960454920243009143617)
            ·
              refine ⟨14817720341190182256857713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19756960454920243009143617 14817720341190182256857713)
              ·
                refine ⟨11113290255892636692643285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14817720341190182256857713 11113290255892636692643285)
                ·
                  refine ⟨260467740372483672483827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11113290255892636692643285 260467740372483672483827)
                  ·
                    rfl

theorem cell21_1141333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1141333 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141333 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141333 prefixEnd_1141333 := by exact prefixLift 1141333
  have htrace : WordTrace (prefixWord ++ tailWord_1141333) baseStart_1141333 baseEnd_1141333 := by
    simpa [prefixWord, tailWord_1141333, baseEnd_1141333] using wordTrace_append hprefix tailTrace_1141333
  have hstable : (prefixWord ++ tailWord_1141333).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141333).length < 2 ^ (prefixWord ++ tailWord_1141333).sum := by decide
  have hdescent : baseEnd_1141333 < baseStart_1141333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141342 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1141342 : Nat := 118140960795 + 1141342 * 2 ^ 59
def prefixEnd_1141342 : Nat := 4983230072969 + 3 ^ 40 * 1141342 * 2
def baseEnd_1141342 : Nat := 260469794295101656833809

theorem tailTrace_1141342 : CollatzResearch.WordTrace tailWord_1141342 prefixEnd_1141342 260469794295101656833809 := by
  unfold tailWord_1141342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203520328890041817485285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 27752108420746889693254853 5203520328890041817485285)
  ·
    refine ⟨975660061666882840778491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5203520328890041817485285 975660061666882840778491)
    ·
      refine ⟨1463490092500324261167737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 975660061666882840778491 1463490092500324261167737)
      ·
        refine ⟨1097617569375243195875803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1463490092500324261167737 1097617569375243195875803)
        ·
          refine ⟨1646426354062864793813705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1097617569375243195875803 1646426354062864793813705)
          ·
            refine ⟨1234819765547148595360279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646426354062864793813705 1234819765547148595360279)
            ·
              refine ⟨1852229648320722893040419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1234819765547148595360279 1852229648320722893040419)
              ·
                refine ⟨2778344472481084339560629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852229648320722893040419 2778344472481084339560629)
                ·
                  refine ⟨260469794295101656833809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2778344472481084339560629 260469794295101656833809)
                  ·
                    rfl

theorem cell21_1141342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1141342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141342 prefixEnd_1141342 := by exact prefixLift 1141342
  have htrace : WordTrace (prefixWord ++ tailWord_1141342) baseStart_1141342 baseEnd_1141342 := by
    simpa [prefixWord, tailWord_1141342, baseEnd_1141342] using wordTrace_append hprefix tailTrace_1141342
  have hstable : (prefixWord ++ tailWord_1141342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141342).length < 2 ^ (prefixWord ++ tailWord_1141342).sum := by decide
  have hdescent : baseEnd_1141342 < baseStart_1141342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141516 : List Nat := [2, 2, 1, 2, 2, 1, 1, 6, 4]
def baseStart_1141516 : Nat := 118140960795 + 1141516 * 2 ^ 59
def prefixEnd_1141516 : Nat := 4983230072969 + 3 ^ 40 * 1141516 * 2
def baseEnd_1141516 : Nat := 260509503465716020933453

theorem tailTrace_1141516 : CollatzResearch.WordTrace tailWord_1141516 prefixEnd_1141516 260509503465716020933453 := by
  unfold tailWord_1141516
  simp only [CollatzResearch.WordTrace]
  refine ⟨20817254466244981128358201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 27756339288326641504477601 20817254466244981128358201)
  ·
    refine ⟨15612940849683735846268651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20817254466244981128358201 15612940849683735846268651)
    ·
      refine ⟨23419411274525603769402977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15612940849683735846268651 23419411274525603769402977)
      ·
        refine ⟨17564558455894202827052233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23419411274525603769402977 17564558455894202827052233)
        ·
          refine ⟨13173418841920652120289175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17564558455894202827052233 13173418841920652120289175)
          ·
            refine ⟨19760128262880978180433763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13173418841920652120289175 19760128262880978180433763)
            ·
              refine ⟨29640192394321467270650645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19760128262880978180433763 29640192394321467270650645)
              ·
                refine ⟨1389384018483818778311749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29640192394321467270650645 1389384018483818778311749)
                ·
                  refine ⟨260509503465716020933453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1389384018483818778311749 260509503465716020933453)
                  ·
                    rfl

theorem cell21_1141516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_1141516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141516 prefixEnd_1141516 := by exact prefixLift 1141516
  have htrace : WordTrace (prefixWord ++ tailWord_1141516) baseStart_1141516 baseEnd_1141516 := by
    simpa [prefixWord, tailWord_1141516, baseEnd_1141516] using wordTrace_append hprefix tailTrace_1141516
  have hstable : (prefixWord ++ tailWord_1141516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141516).length < 2 ^ (prefixWord ++ tailWord_1141516).sum := by decide
  have hdescent : baseEnd_1141516 < baseStart_1141516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141519 : List Nat := [1, 1, 2, 1, 1, 1, 9, 2, 3]
def baseStart_1141519 : Nat := 118140960795 + 1141519 * 2 ^ 59
def prefixEnd_1141519 : Nat := 4983230072969 + 3 ^ 40 * 1141519 * 2
def baseEnd_1141519 : Nat := 260510188106588682383447

theorem tailTrace_1141519 : CollatzResearch.WordTrace tailWord_1141519 prefixEnd_1141519 260510188106588682383447 := by
  unfold tailWord_1141519
  simp only [CollatzResearch.WordTrace]
  refine ⟨41634618351479093769075611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27756412234319395846050407 41634618351479093769075611)
  ·
    refine ⟨62451927527218640653613417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41634618351479093769075611 62451927527218640653613417)
    ·
      refine ⟨46838945645413980490210063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62451927527218640653613417 46838945645413980490210063)
      ·
        refine ⟨70258418468120970735315095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46838945645413980490210063 70258418468120970735315095)
        ·
          refine ⟨105387627702181456102972643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70258418468120970735315095 105387627702181456102972643)
          ·
            refine ⟨158081441553272184154458965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105387627702181456102972643 158081441553272184154458965)
            ·
              refine ⟨926258446601204204030033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 158081441553272184154458965 926258446601204204030033)
              ·
                refine ⟨694693834950903153022525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 926258446601204204030033 694693834950903153022525)
                ·
                  refine ⟨260510188106588682383447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 694693834950903153022525 260510188106588682383447)
                  ·
                    rfl

theorem cell21_1141519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 3].length) (baseStart_1141519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141519 prefixEnd_1141519 := by exact prefixLift 1141519
  have htrace : WordTrace (prefixWord ++ tailWord_1141519) baseStart_1141519 baseEnd_1141519 := by
    simpa [prefixWord, tailWord_1141519, baseEnd_1141519] using wordTrace_append hprefix tailTrace_1141519
  have hstable : (prefixWord ++ tailWord_1141519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141519).length < 2 ^ (prefixWord ++ tailWord_1141519).sum := by decide
  have hdescent : baseEnd_1141519 < baseStart_1141519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141581 : List Nat := [1, 6, 1, 2, 2, 2, 1, 6]
def baseStart_1141581 : Nat := 118140960795 + 1141581 * 2 ^ 59
def prefixEnd_1141581 : Nat := 4983230072969 + 3 ^ 40 * 1141581 * 2
def baseEnd_1141581 : Nat := 86841445783763450783329

theorem tailTrace_1141581 : CollatzResearch.WordTrace tailWord_1141581 prefixEnd_1141581 86841445783763450783329 := by
  unfold tailWord_1141581
  simp only [CollatzResearch.WordTrace]
  refine ⟨41636879677254478357832597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27757919784836318905221731 41636879677254478357832597)
  ·
    refine ⟨1951728734871303673023403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41636879677254478357832597 1951728734871303673023403)
    ·
      refine ⟨2927593102306955509535105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951728734871303673023403 2927593102306955509535105)
      ·
        refine ⟨2195694826730216632151329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2927593102306955509535105 2195694826730216632151329)
        ·
          refine ⟨1646771120047662474113497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2195694826730216632151329 1646771120047662474113497)
          ·
            refine ⟨1235078340035746855585123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1646771120047662474113497 1235078340035746855585123)
            ·
              refine ⟨1852617510053620283377685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1235078340035746855585123 1852617510053620283377685)
              ·
                refine ⟨86841445783763450783329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1852617510053620283377685 86841445783763450783329)
                ·
                  rfl

theorem cell21_1141581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 1, 6].length) (baseStart_1141581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141581 prefixEnd_1141581 := by exact prefixLift 1141581
  have htrace : WordTrace (prefixWord ++ tailWord_1141581) baseStart_1141581 baseEnd_1141581 := by
    simpa [prefixWord, tailWord_1141581, baseEnd_1141581] using wordTrace_append hprefix tailTrace_1141581
  have hstable : (prefixWord ++ tailWord_1141581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141581).length < 2 ^ (prefixWord ++ tailWord_1141581).sum := by decide
  have hdescent : baseEnd_1141581 < baseStart_1141581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141637 : List Nat := [1, 3, 1, 1, 3, 3, 1, 3, 5]
def baseStart_1141637 : Nat := 118140960795 + 1141637 * 2 ^ 59
def prefixEnd_1141637 : Nat := 4983230072969 + 3 ^ 40 * 1141637 * 2
def baseEnd_1141637 : Nat := 260537117314246699416539

theorem tailTrace_1141637 : CollatzResearch.WordTrace tailWord_1141637 prefixEnd_1141637 260537117314246699416539 := by
  unfold tailWord_1141637
  simp only [CollatzResearch.WordTrace]
  refine ⟨41638922165051599921871165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27759281443367733281247443 41638922165051599921871165)
  ·
    refine ⟨15614595811894349970701687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41638922165051599921871165 15614595811894349970701687)
    ·
      refine ⟨23421893717841524956052531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15614595811894349970701687 23421893717841524956052531)
      ·
        refine ⟨35132840576762287434078797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23421893717841524956052531 35132840576762287434078797)
        ·
          refine ⟨13174815216285857787779549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35132840576762287434078797 13174815216285857787779549)
          ·
            refine ⟨4940555706107196670417331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13174815216285857787779549 4940555706107196670417331)
            ·
              refine ⟨7410833559160795005625997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940555706107196670417331 7410833559160795005625997)
              ·
                refine ⟨2779062584685298127109749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7410833559160795005625997 2779062584685298127109749)
                ·
                  refine ⟨260537117314246699416539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2779062584685298127109749 260537117314246699416539)
                  ·
                    rfl

theorem cell21_1141637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_1141637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141637 prefixEnd_1141637 := by exact prefixLift 1141637
  have htrace : WordTrace (prefixWord ++ tailWord_1141637) baseStart_1141637 baseEnd_1141637 := by
    simpa [prefixWord, tailWord_1141637, baseEnd_1141637] using wordTrace_append hprefix tailTrace_1141637
  have hstable : (prefixWord ++ tailWord_1141637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141637).length < 2 ^ (prefixWord ++ tailWord_1141637).sum := by decide
  have hdescent : baseEnd_1141637 < baseStart_1141637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1141803 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 6]
def baseStart_1141803 : Nat := 118140960795 + 1141803 * 2 ^ 59
def prefixEnd_1141803 : Nat := 4983230072969 + 3 ^ 40 * 1141803 * 2
def baseEnd_1141803 : Nat := 260575000775867299649533

theorem tailTrace_1141803 : CollatzResearch.WordTrace tailWord_1141803 prefixEnd_1141803 260575000775867299649533 := by
  unfold tailWord_1141803
  simp only [CollatzResearch.WordTrace]
  refine ⟨41644976682450210272414063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 27763317788300140181609375 41644976682450210272414063)
  ·
    refine ⟨62467465023675315408621095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41644976682450210272414063 62467465023675315408621095)
    ·
      refine ⟨93701197535512973112931643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62467465023675315408621095 93701197535512973112931643)
      ·
        refine ⟨140551796303269459669397465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93701197535512973112931643 140551796303269459669397465)
        ·
          refine ⟨105413847227452094752048099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140551796303269459669397465 105413847227452094752048099)
          ·
            refine ⟨158120770841178142128072149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105413847227452094752048099 158120770841178142128072149)
            ·
              refine ⟨3705955566590112706126691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 158120770841178142128072149 3705955566590112706126691)
              ·
                refine ⟨5558933349885169059190037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705955566590112706126691 5558933349885169059190037)
                ·
                  refine ⟨260575000775867299649533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5558933349885169059190037 260575000775867299649533)
                  ·
                    rfl

theorem cell21_1141803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 6].length) (baseStart_1141803 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1141803 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1141803 prefixEnd_1141803 := by exact prefixLift 1141803
  have htrace : WordTrace (prefixWord ++ tailWord_1141803) baseStart_1141803 baseEnd_1141803 := by
    simpa [prefixWord, tailWord_1141803, baseEnd_1141803] using wordTrace_append hprefix tailTrace_1141803
  have hstable : (prefixWord ++ tailWord_1141803).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1141803).length < 2 ^ (prefixWord ++ tailWord_1141803).sum := by decide
  have hdescent : baseEnd_1141803 < baseStart_1141803 := by decide
  rcases family_descends (prefixWord ++ tailWord_1141803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
