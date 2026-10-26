import V185TrunkScan23Chunk1160

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6878285 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 7]
def baseStart_6878285 : Nat := 118140960795 + 6878285 * 2 ^ 59
def prefixEnd_6878285 : Nat := 4983230072969 + 3 ^ 40 * 6878285 * 2
def baseEnd_6878285 : Nat := 392429587067858490222761

theorem tailTrace_6878285 : CollatzResearch.WordTrace tailWord_6878285 prefixEnd_6878285 392429587067858490222761 := by
  unfold tailWord_6878285
  simp only [CollatzResearch.WordTrace]
  refine ⟨250871663886155637399068309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167247775924103758266045539 250871663886155637399068309)
  ·
    refine ⟨11759609244663545503081327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250871663886155637399068309 11759609244663545503081327)
    ·
      refine ⟨17639413866995318254621991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11759609244663545503081327 17639413866995318254621991)
      ·
        refine ⟨26459120800492977381932987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17639413866995318254621991 26459120800492977381932987)
        ·
          refine ⟨39688681200739466072899481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26459120800492977381932987 39688681200739466072899481)
          ·
            refine ⟨29766510900554599554674611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39688681200739466072899481 29766510900554599554674611)
            ·
              refine ⟨44649766350831899332011917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29766510900554599554674611 44649766350831899332011917)
              ·
                refine ⟨16743662381561962249504469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44649766350831899332011917 16743662381561962249504469)
                ·
                  refine ⟨392429587067858490222761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16743662381561962249504469 392429587067858490222761)
                  ·
                    rfl

theorem cell23_6878285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_6878285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878285 prefixEnd_6878285 := by exact prefixLift 6878285
  have htrace : WordTrace (prefixWord ++ tailWord_6878285) baseStart_6878285 baseEnd_6878285 := by
    simpa [prefixWord, tailWord_6878285, baseEnd_6878285] using wordTrace_append hprefix tailTrace_6878285
  have hstable : (prefixWord ++ tailWord_6878285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878285).length < 2 ^ (prefixWord ++ tailWord_6878285).sum := by decide
  have hdescent : baseEnd_6878285 < baseStart_6878285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878298 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 6, 5]
def baseStart_6878298 : Nat := 118140960795 + 6878298 * 2 ^ 59
def prefixEnd_6878298 : Nat := 4983230072969 + 3 ^ 40 * 6878298 * 2
def baseEnd_6878298 : Nat := 1177290986286411620380763

theorem tailTrace_6878298 : CollatzResearch.WordTrace tailWord_6878298 prefixEnd_6878298 1177290986286411620380763 := by
  unfold tailWord_6878298
  simp only [CollatzResearch.WordTrace]
  refine ⟨62718034508777135154822887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167248092023405693746194365 62718034508777135154822887)
  ·
    refine ⟨94077051763165702732234331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62718034508777135154822887 94077051763165702732234331)
    ·
      refine ⟨141115577644748554098351497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94077051763165702732234331 141115577644748554098351497)
      ·
        refine ⟨105836683233561415573763623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141115577644748554098351497 105836683233561415573763623)
        ·
          refine ⟨158755024850342123360645435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105836683233561415573763623 158755024850342123360645435)
          ·
            refine ⟨238132537275513185040968153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158755024850342123360645435 238132537275513185040968153)
            ·
              refine ⟨178599402956634888780726115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238132537275513185040968153 178599402956634888780726115)
              ·
                refine ⟨267899104434952333171089173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178599402956634888780726115 267899104434952333171089173)
                ·
                  refine ⟨12557770520388390617394805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267899104434952333171089173 12557770520388390617394805)
                  ·
                    refine ⟨1177290986286411620380763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12557770520388390617394805 1177290986286411620380763)
                    ·
                      rfl

theorem cell23_6878298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 6, 5].length) (baseStart_6878298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878298 prefixEnd_6878298 := by exact prefixLift 6878298
  have htrace : WordTrace (prefixWord ++ tailWord_6878298) baseStart_6878298 baseEnd_6878298 := by
    simpa [prefixWord, tailWord_6878298, baseEnd_6878298] using wordTrace_append hprefix tailTrace_6878298
  have hstable : (prefixWord ++ tailWord_6878298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878298).length < 2 ^ (prefixWord ++ tailWord_6878298).sum := by decide
  have hdescent : baseEnd_6878298 < baseStart_6878298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878305 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 2, 5, 2]
def baseStart_6878305 : Nat := 118140960795 + 6878305 * 2 ^ 59
def prefixEnd_6878305 : Nat := 4983230072969 + 3 ^ 40 * 6878305 * 2
def baseEnd_6878305 : Nat := 3531876553223816333754757

theorem tailTrace_6878305 : CollatzResearch.WordTrace tailWord_6878305 prefixEnd_6878305 3531876553223816333754757 := by
  unfold tailWord_6878305
  simp only [CollatzResearch.WordTrace]
  refine ⟨250872393346083180814796369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167248262230722120543197579 250872393346083180814796369)
  ·
    refine ⟨188154295009562385611097277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250872393346083180814796369 188154295009562385611097277)
    ·
      refine ⟨70557860628585894604161479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188154295009562385611097277 70557860628585894604161479)
      ·
        refine ⟨105836790942878841906242219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70557860628585894604161479 105836790942878841906242219)
        ·
          refine ⟨158755186414318262859363329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105836790942878841906242219 158755186414318262859363329)
          ·
            refine ⟨119066389810738697144522497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158755186414318262859363329 119066389810738697144522497)
            ·
              refine ⟨89299792358054022858391873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119066389810738697144522497 89299792358054022858391873)
              ·
                refine ⟨66974844268540517143793905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89299792358054022858391873 66974844268540517143793905)
                ·
                  refine ⟨50231133201405387857845429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66974844268540517143793905 50231133201405387857845429)
                  ·
                    refine ⟨4709168737631755111673009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50231133201405387857845429 4709168737631755111673009)
                    ·
                      refine ⟨3531876553223816333754757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709168737631755111673009 3531876553223816333754757)
                      ·
                        rfl

theorem cell23_6878305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 5, 2].length) (baseStart_6878305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878305 prefixEnd_6878305 := by exact prefixLift 6878305
  have htrace : WordTrace (prefixWord ++ tailWord_6878305) baseStart_6878305 baseEnd_6878305 := by
    simpa [prefixWord, tailWord_6878305, baseEnd_6878305] using wordTrace_append hprefix tailTrace_6878305
  have hstable : (prefixWord ++ tailWord_6878305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878305).length < 2 ^ (prefixWord ++ tailWord_6878305).sum := by decide
  have hdescent : baseEnd_6878305 < baseStart_6878305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878308 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 3, 2, 5]
def baseStart_6878308 : Nat := 118140960795 + 6878308 * 2 ^ 59
def prefixEnd_6878308 : Nat := 4983230072969 + 3 ^ 40 * 6878308 * 2
def baseEnd_6878308 : Nat := 3531878093665779822017243

theorem tailTrace_6878308 : CollatzResearch.WordTrace tailWord_6878308 prefixEnd_6878308 3531878093665779822017243 := by
  unfold tailWord_6878308
  simp only [CollatzResearch.WordTrace]
  refine ⟨125436251382536156163577789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167248335176714874884770385 125436251382536156163577789)
  ·
    refine ⟨47038594268451058561341671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125436251382536156163577789 47038594268451058561341671)
    ·
      refine ⟨70557891402676587842012507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47038594268451058561341671 70557891402676587842012507)
      ·
        refine ⟨105836837104014881763018761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70557891402676587842012507 105836837104014881763018761)
        ·
          refine ⟨79377627828011161322264071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105836837104014881763018761 79377627828011161322264071)
          ·
            refine ⟨119066441742016741983396107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79377627828011161322264071 119066441742016741983396107)
            ·
              refine ⟨178599662613025112975094161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119066441742016741983396107 178599662613025112975094161)
              ·
                refine ⟨133949746959768834731320621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178599662613025112975094161 133949746959768834731320621)
                ·
                  refine ⟨50231155109913313024245233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133949746959768834731320621 50231155109913313024245233)
                  ·
                    refine ⟨37673366332434984768183925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50231155109913313024245233 37673366332434984768183925)
                    ·
                      refine ⟨3531878093665779822017243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37673366332434984768183925 3531878093665779822017243)
                      ·
                        rfl

theorem cell23_6878308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_6878308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878308 prefixEnd_6878308 := by exact prefixLift 6878308
  have htrace : WordTrace (prefixWord ++ tailWord_6878308) baseStart_6878308 baseEnd_6878308 := by
    simpa [prefixWord, tailWord_6878308, baseEnd_6878308] using wordTrace_append hprefix tailTrace_6878308
  have hstable : (prefixWord ++ tailWord_6878308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878308).length < 2 ^ (prefixWord ++ tailWord_6878308).sum := by decide
  have hdescent : baseEnd_6878308 < baseStart_6878308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878348 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6878348 : Nat := 118140960795 + 6878348 * 2 ^ 59
def prefixEnd_6878348 : Nat := 4983230072969 + 3 ^ 40 * 6878348 * 2
def baseEnd_6878348 : Nat := 3531898632891959665517059

theorem tailTrace_6878348 : CollatzResearch.WordTrace tailWord_6878348 prefixEnd_6878348 3531898632891959665517059 := by
  unfold tailWord_6878348
  simp only [CollatzResearch.WordTrace]
  refine ⟨125436980842463699579305849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167249307789951599439074465 125436980842463699579305849)
  ·
    refine ⟨94077735631847774684479387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125436980842463699579305849 94077735631847774684479387)
    ·
      refine ⟨141116603447771662026719081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94077735631847774684479387 141116603447771662026719081)
      ·
        refine ⟨105837452585828746520039311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141116603447771662026719081 105837452585828746520039311)
        ·
          refine ⟨158756178878743119780058967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105837452585828746520039311 158756178878743119780058967)
          ·
            refine ⟨238134268318114679670088451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158756178878743119780058967 238134268318114679670088451)
            ·
              refine ⟨357201402477172019505132677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238134268318114679670088451 357201402477172019505132677)
              ·
                refine ⟨66975262964469753657212377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357201402477172019505132677 66975262964469753657212377)
                ·
                  refine ⟨50231447223352315242909283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66975262964469753657212377 50231447223352315242909283)
                  ·
                    refine ⟨75347170835028472864363925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50231447223352315242909283 75347170835028472864363925)
                    ·
                      refine ⟨3531898632891959665517059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75347170835028472864363925 3531898632891959665517059)
                      ·
                        rfl

theorem cell23_6878348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6878348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878348 prefixEnd_6878348 := by exact prefixLift 6878348
  have htrace : WordTrace (prefixWord ++ tailWord_6878348) baseStart_6878348 baseEnd_6878348 := by
    simpa [prefixWord, tailWord_6878348, baseEnd_6878348] using wordTrace_append hprefix tailTrace_6878348
  have hstable : (prefixWord ++ tailWord_6878348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878348).length < 2 ^ (prefixWord ++ tailWord_6878348).sum := by decide
  have hdescent : baseEnd_6878348 < baseStart_6878348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878372 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 2, 2, 3]
def baseStart_6878372 : Nat := 118140960795 + 6878372 * 2 ^ 59
def prefixEnd_6878372 : Nat := 4983230072969 + 3 ^ 40 * 6878372 * 2
def baseEnd_6878372 : Nat := 3531910956427667571616949

theorem tailTrace_6878372 : CollatzResearch.WordTrace tailWord_6878372 prefixEnd_6878372 3531910956427667571616949 := by
  unfold tailWord_6878372
  simp only [CollatzResearch.WordTrace]
  refine ⟨125437418518420225628742685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167249891357893634171656913 125437418518420225628742685)
  ·
    refine ⟨47039031944407584610778507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125437418518420225628742685 47039031944407584610778507)
    ·
      refine ⟨70558547916611376916167761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47039031944407584610778507 70558547916611376916167761)
      ·
        refine ⟨52918910937458532687125821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70558547916611376916167761 52918910937458532687125821)
        ·
          refine ⟨19844591601546949757672183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52918910937458532687125821 19844591601546949757672183)
          ·
            refine ⟨29766887402320424636508275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19844591601546949757672183 29766887402320424636508275)
            ·
              refine ⟨44650331103480636954762413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29766887402320424636508275 44650331103480636954762413)
              ·
                refine ⟨16743874163805238858035905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44650331103480636954762413 16743874163805238858035905)
                ·
                  refine ⟨12557905622853929143526929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16743874163805238858035905 12557905622853929143526929)
                  ·
                    refine ⟨9418429217140446857645197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12557905622853929143526929 9418429217140446857645197)
                    ·
                      refine ⟨3531910956427667571616949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9418429217140446857645197 3531910956427667571616949)
                      ·
                        rfl

theorem cell23_6878372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_6878372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878372 prefixEnd_6878372 := by exact prefixLift 6878372
  have htrace : WordTrace (prefixWord ++ tailWord_6878372) baseStart_6878372 baseEnd_6878372 := by
    simpa [prefixWord, tailWord_6878372, baseEnd_6878372] using wordTrace_append hprefix tailTrace_6878372
  have hstable : (prefixWord ++ tailWord_6878372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878372).length < 2 ^ (prefixWord ++ tailWord_6878372).sum := by decide
  have hdescent : baseEnd_6878372 < baseStart_6878372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878396 : List Nat := [2, 2, 2, 3, 2, 1, 4, 2, 1, 4]
def baseStart_6878396 : Nat := 118140960795 + 6878396 * 2 ^ 59
def prefixEnd_6878396 : Nat := 4983230072969 + 3 ^ 40 * 6878396 * 2
def baseEnd_6878396 : Nat := 1177307759987791825905613

theorem tailTrace_6878396 : CollatzResearch.WordTrace tailWord_6878396 prefixEnd_6878396 1177307759987791825905613 := by
  unfold tailWord_6878396
  simp only [CollatzResearch.WordTrace]
  refine ⟨125437856194376751678179521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167250474925835668904239361 125437856194376751678179521)
  ·
    refine ⟨94078392145782563758634641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125437856194376751678179521 94078392145782563758634641)
    ·
      refine ⟨70558794109336922818975981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94078392145782563758634641 70558794109336922818975981)
      ·
        refine ⟨26459547791001346057115993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70558794109336922818975981 26459547791001346057115993)
        ·
          refine ⟨19844660843251009542836995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26459547791001346057115993 19844660843251009542836995)
          ·
            refine ⟨29766991264876514314255493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19844660843251009542836995 29766991264876514314255493)
            ·
              refine ⟨5581310862164346433922905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29766991264876514314255493 5581310862164346433922905)
              ·
                refine ⟨4185983146623259825442179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581310862164346433922905 4185983146623259825442179)
                ·
                  refine ⟨6278974719934889738163269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4185983146623259825442179 6278974719934889738163269)
                  ·
                    refine ⟨1177307759987791825905613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6278974719934889738163269 1177307759987791825905613)
                    ·
                      rfl

theorem cell23_6878396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_6878396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878396 prefixEnd_6878396 := by exact prefixLift 6878396
  have htrace : WordTrace (prefixWord ++ tailWord_6878396) baseStart_6878396 baseEnd_6878396 := by
    simpa [prefixWord, tailWord_6878396, baseEnd_6878396] using wordTrace_append hprefix tailTrace_6878396
  have hstable : (prefixWord ++ tailWord_6878396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878396).length < 2 ^ (prefixWord ++ tailWord_6878396).sum := by decide
  have hdescent : baseEnd_6878396 < baseStart_6878396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878439 : List Nat := [1, 1, 5, 3, 2, 1, 1, 3, 1, 5]
def baseStart_6878439 : Nat := 118140960795 + 6878439 * 2 ^ 59
def prefixEnd_6878439 : Nat := 4983230072969 + 3 ^ 40 * 6878439 * 2
def baseEnd_6878439 : Nat := 1177315119877172936493047

theorem tailTrace_6878439 : CollatzResearch.WordTrace tailWord_6878439 prefixEnd_6878439 1177315119877172936493047 := by
  unfold tailWord_6878439
  simp only [CollatzResearch.WordTrace]
  refine ⟨250877280727597721700174371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167251520485065147800116247 250877280727597721700174371)
  ·
    refine ⟨376315921091396582550261557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250877280727597721700174371 376315921091396582550261557)
    ·
      refine ⟨35279617602318429614087021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 376315921091396582550261557 35279617602318429614087021)
      ·
        refine ⟨13229856600869411105282633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35279617602318429614087021 13229856600869411105282633)
        ·
          refine ⟨9922392450652058328961975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13229856600869411105282633 9922392450652058328961975)
          ·
            refine ⟨14883588675978087493442963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922392450652058328961975 14883588675978087493442963)
            ·
              refine ⟨22325383013967131240164445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14883588675978087493442963 22325383013967131240164445)
              ·
                refine ⟨8372018630237674215061667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22325383013967131240164445 8372018630237674215061667)
                ·
                  refine ⟨12558027945356511322592501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372018630237674215061667 12558027945356511322592501)
                  ·
                    refine ⟨1177315119877172936493047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12558027945356511322592501 1177315119877172936493047)
                    ·
                      rfl

theorem cell23_6878439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_6878439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878439 prefixEnd_6878439 := by exact prefixLift 6878439
  have htrace : WordTrace (prefixWord ++ tailWord_6878439) baseStart_6878439 baseEnd_6878439 := by
    simpa [prefixWord, tailWord_6878439, baseEnd_6878439] using wordTrace_append hprefix tailTrace_6878439
  have hstable : (prefixWord ++ tailWord_6878439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878439).length < 2 ^ (prefixWord ++ tailWord_6878439).sum := by decide
  have hdescent : baseEnd_6878439 < baseStart_6878439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878462 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6878462 : Nat := 118140960795 + 6878462 * 2 ^ 59
def prefixEnd_6878462 : Nat := 4983230072969 + 3 ^ 40 * 6878462 * 2
def baseEnd_6878462 : Nat := 3531957169686572219491535

theorem tailTrace_6878462 : CollatzResearch.WordTrace tailWord_6878462 prefixEnd_6878462 3531957169686572219491535 := by
  unfold tailWord_6878462
  simp only [CollatzResearch.WordTrace]
  refine ⟨31359764950814299578532705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167252079737676264418841093 31359764950814299578532705)
  ·
    refine ⟨23519823713110724683899529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31359764950814299578532705 23519823713110724683899529)
    ·
      refine ⟨17639867784833043512924647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23519823713110724683899529 17639867784833043512924647)
      ·
        refine ⟨26459801677249565269386971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17639867784833043512924647 26459801677249565269386971)
        ·
          refine ⟨39689702515874347904080457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26459801677249565269386971 39689702515874347904080457)
          ·
            refine ⟨29767276886905760928060343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39689702515874347904080457 29767276886905760928060343)
            ·
              refine ⟨44650915330358641392090515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29767276886905760928060343 44650915330358641392090515)
              ·
                refine ⟨66976372995537962088135773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44650915330358641392090515 66976372995537962088135773)
                ·
                  refine ⟨25116139873326735783050915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66976372995537962088135773 25116139873326735783050915)
                  ·
                    refine ⟨37674209809990103674576373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25116139873326735783050915 37674209809990103674576373)
                    ·
                      refine ⟨3531957169686572219491535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37674209809990103674576373 3531957169686572219491535)
                      ·
                        rfl

theorem cell23_6878462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6878462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878462 prefixEnd_6878462 := by exact prefixLift 6878462
  have htrace : WordTrace (prefixWord ++ tailWord_6878462) baseStart_6878462 baseEnd_6878462 := by
    simpa [prefixWord, tailWord_6878462, baseEnd_6878462] using wordTrace_append hprefix tailTrace_6878462
  have hstable : (prefixWord ++ tailWord_6878462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878462).length < 2 ^ (prefixWord ++ tailWord_6878462).sum := by decide
  have hdescent : baseEnd_6878462 < baseStart_6878462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878469 : List Nat := [1, 3, 1, 1, 2, 1, 7, 1, 2, 4]
def baseStart_6878469 : Nat := 118140960795 + 6878469 * 2 ^ 59
def prefixEnd_6878469 : Nat := 4983230072969 + 3 ^ 40 * 6878469 * 2
def baseEnd_6878469 : Nat := 1177320254683717897368001

theorem tailTrace_6878469 : CollatzResearch.WordTrace tailWord_6878469 prefixEnd_6878469 1177320254683717897368001 := by
  unfold tailWord_6878469
  simp only [CollatzResearch.WordTrace]
  refine ⟨250878374917489036823766461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167252249944992691215844307 250878374917489036823766461)
  ·
    refine ⟨94079390594058388808912423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250878374917489036823766461 94079390594058388808912423)
    ·
      refine ⟨141119085891087583213368635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94079390594058388808912423 141119085891087583213368635)
      ·
        refine ⟨211678628836631374820052953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141119085891087583213368635 211678628836631374820052953)
        ·
          refine ⟨158758971627473531115039715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211678628836631374820052953 158758971627473531115039715)
          ·
            refine ⟨238138457441210296672559573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158758971627473531115039715 238138457441210296672559573)
            ·
              refine ⟨5581370096278366328263115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238138457441210296672559573 5581370096278366328263115)
              ·
                refine ⟨8372055144417549492394673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581370096278366328263115 8372055144417549492394673)
                ·
                  refine ⟨6279041358313162119296005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8372055144417549492394673 6279041358313162119296005)
                  ·
                    refine ⟨1177320254683717897368001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6279041358313162119296005 1177320254683717897368001)
                    ·
                      rfl

theorem cell23_6878469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_6878469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878469 prefixEnd_6878469 := by exact prefixLift 6878469
  have htrace : WordTrace (prefixWord ++ tailWord_6878469) baseStart_6878469 baseEnd_6878469 := by
    simpa [prefixWord, tailWord_6878469, baseEnd_6878469] using wordTrace_append hprefix tailTrace_6878469
  have hstable : (prefixWord ++ tailWord_6878469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878469).length < 2 ^ (prefixWord ++ tailWord_6878469).sum := by decide
  have hdescent : baseEnd_6878469 < baseStart_6878469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878472 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_6878472 : Nat := 118140960795 + 6878472 * 2 ^ 59
def prefixEnd_6878472 : Nat := 4983230072969 + 3 ^ 40 * 6878472 * 2
def baseEnd_6878472 : Nat := 3531962304493117180366489

theorem tailTrace_6878472 : CollatzResearch.WordTrace tailWord_6878472 prefixEnd_6878472 3531962304493117180366489 := by
  unfold tailWord_6878472
  simp only [CollatzResearch.WordTrace]
  refine ⟨125439242168239084168062835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167252322890985445557417113 125439242168239084168062835)
  ·
    refine ⟨188158863252358626252094253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125439242168239084168062835 188158863252358626252094253)
    ·
      refine ⟨70559573719634484844535345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188158863252358626252094253 70559573719634484844535345)
      ·
        refine ⟨52919680289725863633401509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70559573719634484844535345 52919680289725863633401509)
        ·
          refine ⟨9922440054323599431262783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52919680289725863633401509 9922440054323599431262783)
          ·
            refine ⟨14883660081485399146894175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922440054323599431262783 14883660081485399146894175)
            ·
              refine ⟨22325490122228098720341263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14883660081485399146894175 22325490122228098720341263)
              ·
                refine ⟨33488235183342148080511895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22325490122228098720341263 33488235183342148080511895)
                ·
                  refine ⟨50232352775013222120767843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33488235183342148080511895 50232352775013222120767843)
                  ·
                    refine ⟨75348529162519833181151765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50232352775013222120767843 75348529162519833181151765)
                    ·
                      refine ⟨3531962304493117180366489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75348529162519833181151765 3531962304493117180366489)
                      ·
                        rfl

theorem cell23_6878472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_6878472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878472 prefixEnd_6878472 := by exact prefixLift 6878472
  have htrace : WordTrace (prefixWord ++ tailWord_6878472) baseStart_6878472 baseEnd_6878472 := by
    simpa [prefixWord, tailWord_6878472, baseEnd_6878472] using wordTrace_append hprefix tailTrace_6878472
  have hstable : (prefixWord ++ tailWord_6878472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878472).length < 2 ^ (prefixWord ++ tailWord_6878472).sum := by decide
  have hdescent : baseEnd_6878472 < baseStart_6878472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878492 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6878492 : Nat := 118140960795 + 6878492 * 2 ^ 59
def prefixEnd_6878492 : Nat := 4983230072969 + 3 ^ 40 * 6878492 * 2
def baseEnd_6878492 : Nat := 3531972574106207102116397

theorem tailTrace_6878492 : CollatzResearch.WordTrace tailWord_6878492 prefixEnd_6878492 3531972574106207102116397 := by
  unfold tailWord_6878492
  simp only [CollatzResearch.WordTrace]
  refine ⟨125439606898202855875926865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167252809197603807834569153 125439606898202855875926865)
  ·
    refine ⟨94079705173652141906945149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125439606898202855875926865 94079705173652141906945149)
    ·
      refine ⟨35279889440119553215104431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94079705173652141906945149 35279889440119553215104431)
      ·
        refine ⟨52919834160179329822656647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35279889440119553215104431 52919834160179329822656647)
        ·
          refine ⟨79379751240268994733984971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52919834160179329822656647 79379751240268994733984971)
          ·
            refine ⟨119069626860403492100977457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79379751240268994733984971 119069626860403492100977457)
            ·
              refine ⟨89302220145302619075733093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119069626860403492100977457 89302220145302619075733093)
              ·
                refine ⟨16744166277244241076699955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89302220145302619075733093 16744166277244241076699955)
                ·
                  refine ⟨25116249415866361615049933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16744166277244241076699955 25116249415866361615049933)
                  ·
                    refine ⟨9418593530949885605643725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25116249415866361615049933 9418593530949885605643725)
                    ·
                      refine ⟨3531972574106207102116397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9418593530949885605643725 3531972574106207102116397)
                      ·
                        rfl

theorem cell23_6878492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6878492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878492 prefixEnd_6878492 := by exact prefixLift 6878492
  have htrace : WordTrace (prefixWord ++ tailWord_6878492) baseStart_6878492 baseEnd_6878492 := by
    simpa [prefixWord, tailWord_6878492, baseEnd_6878492] using wordTrace_append hprefix tailTrace_6878492
  have hstable : (prefixWord ++ tailWord_6878492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878492).length < 2 ^ (prefixWord ++ tailWord_6878492).sum := by decide
  have hdescent : baseEnd_6878492 < baseStart_6878492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878526 : List Nat := [4, 2, 1, 2, 1, 1, 3, 3, 2, 1, 3]
def baseStart_6878526 : Nat := 118140960795 + 6878526 * 2 ^ 59
def prefixEnd_6878526 : Nat := 4983230072969 + 3 ^ 40 * 6878526 * 2
def baseEnd_6878526 : Nat := 3531990032448459969091241

theorem tailTrace_6878526 : CollatzResearch.WordTrace tailWord_6878526 prefixEnd_6878526 3531990032448459969091241 := by
  unfold tailWord_6878526
  simp only [CollatzResearch.WordTrace]
  refine ⟨31360056734785316944823929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167253635918855023705727621 31360056734785316944823929)
  ·
    refine ⟨23520042551088987708617947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31360056734785316944823929 23520042551088987708617947)
    ·
      refine ⟨35280063826633481562926921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23520042551088987708617947 35280063826633481562926921)
      ·
        refine ⟨26460047869975111172195191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35280063826633481562926921 26460047869975111172195191)
        ·
          refine ⟨39690071804962666758292787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26460047869975111172195191 39690071804962666758292787)
          ·
            refine ⟨59535107707444000137439181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39690071804962666758292787 59535107707444000137439181)
            ·
              refine ⟨22325665390291500051539693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59535107707444000137439181 22325665390291500051539693)
              ·
                refine ⟨8372124521359312519327385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22325665390291500051539693 8372124521359312519327385)
                ·
                  refine ⟨6279093391019484389495539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8372124521359312519327385 6279093391019484389495539)
                  ·
                    refine ⟨9418640086529226584243309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6279093391019484389495539 9418640086529226584243309)
                    ·
                      refine ⟨3531990032448459969091241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9418640086529226584243309 3531990032448459969091241)
                      ·
                        rfl

theorem cell23_6878526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_6878526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878526 prefixEnd_6878526 := by exact prefixLift 6878526
  have htrace : WordTrace (prefixWord ++ tailWord_6878526) baseStart_6878526 baseEnd_6878526 := by
    simpa [prefixWord, tailWord_6878526, baseEnd_6878526] using wordTrace_append hprefix tailTrace_6878526
  have hstable : (prefixWord ++ tailWord_6878526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878526).length < 2 ^ (prefixWord ++ tailWord_6878526).sum := by decide
  have hdescent : baseEnd_6878526 < baseStart_6878526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878549 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6878549 : Nat := 118140960795 + 6878549 * 2 ^ 59
def prefixEnd_6878549 : Nat := 4983230072969 + 3 ^ 40 * 6878549 * 2
def baseEnd_6878549 : Nat := 3532001842503513379103635

theorem tailTrace_6878549 : CollatzResearch.WordTrace tailWord_6878549 prefixEnd_6878549 3532001842503513379103635 := by
  unfold tailWord_6878549
  simp only [CollatzResearch.WordTrace]
  refine ⟨250881292757199210486678701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167254195171466140324452467 250881292757199210486678701)
  ·
    refine ⟨94080484783949703932504513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250881292757199210486678701 94080484783949703932504513)
    ·
      refine ⟨70560363587962277949378385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94080484783949703932504513 70560363587962277949378385)
      ·
        refine ⟨52920272690971708462033789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70560363587962277949378385 52920272690971708462033789)
        ·
          refine ⟨19845102259114390673262671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52920272690971708462033789 19845102259114390673262671)
          ·
            refine ⟨29767653388671586009894007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19845102259114390673262671 29767653388671586009894007)
            ·
              refine ⟨44651480083007379014841011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29767653388671586009894007 44651480083007379014841011)
              ·
                refine ⟨66977220124511068522261517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44651480083007379014841011 66977220124511068522261517)
                ·
                  refine ⟨25116457546691650695848069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66977220124511068522261517 25116457546691650695848069)
                  ·
                    refine ⟨4709335790004684505471513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25116457546691650695848069 4709335790004684505471513)
                    ·
                      refine ⟨3532001842503513379103635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709335790004684505471513 3532001842503513379103635)
                      ·
                        rfl

theorem cell23_6878549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6878549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878549 prefixEnd_6878549 := by exact prefixLift 6878549
  have htrace : WordTrace (prefixWord ++ tailWord_6878549) baseStart_6878549 baseEnd_6878549 := by
    simpa [prefixWord, tailWord_6878549, baseEnd_6878549] using wordTrace_append hprefix tailTrace_6878549
  have hstable : (prefixWord ++ tailWord_6878549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878549).length < 2 ^ (prefixWord ++ tailWord_6878549).sum := by decide
  have hdescent : baseEnd_6878549 < baseStart_6878549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878672 : List Nat := [2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_6878672 : Nat := 118140960795 + 6878672 * 2 ^ 59
def prefixEnd_6878672 : Nat := 4983230072969 + 3 ^ 40 * 6878672 * 2
def baseEnd_6878672 : Nat := 3532065000624016397865569

theorem tailTrace_6878672 : CollatzResearch.WordTrace tailWord_6878672 prefixEnd_6878672 3532065000624016397865569 := by
  unfold tailWord_6878672
  simp only [CollatzResearch.WordTrace]
  refine ⟨125442889467876801246703135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167257185957169068328937513 125442889467876801246703135)
  ·
    refine ⟨188164334201815201870054703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125442889467876801246703135 188164334201815201870054703)
    ·
      refine ⟨282246501302722802805082055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188164334201815201870054703 282246501302722802805082055)
      ·
        refine ⟨423369751954084204207623083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282246501302722802805082055 423369751954084204207623083)
        ·
          refine ⟨635054627931126306311434625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423369751954084204207623083 635054627931126306311434625)
          ·
            refine ⟨476290970948344729733575969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635054627931126306311434625 476290970948344729733575969)
            ·
              refine ⟨357218228211258547300181977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476290970948344729733575969 357218228211258547300181977)
              ·
                refine ⟨267913671158443910475136483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357218228211258547300181977 267913671158443910475136483)
                ·
                  refine ⟨401870506737665865712704725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267913671158443910475136483 401870506737665865712704725)
                  ·
                    refine ⟨9418840001664043727641517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 401870506737665865712704725 9418840001664043727641517)
                    ·
                      refine ⟨3532065000624016397865569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9418840001664043727641517 3532065000624016397865569)
                      ·
                        rfl

theorem cell23_6878672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_6878672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878672 prefixEnd_6878672 := by exact prefixLift 6878672
  have htrace : WordTrace (prefixWord ++ tailWord_6878672) baseStart_6878672 baseEnd_6878672 := by
    simpa [prefixWord, tailWord_6878672, baseEnd_6878672] using wordTrace_append hprefix tailTrace_6878672
  have hstable : (prefixWord ++ tailWord_6878672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878672).length < 2 ^ (prefixWord ++ tailWord_6878672).sum := by decide
  have hdescent : baseEnd_6878672 < baseStart_6878672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878699 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 1, 5, 2]
def baseStart_6878699 : Nat := 118140960795 + 6878699 * 2 ^ 59
def prefixEnd_6878699 : Nat := 4983230072969 + 3 ^ 40 * 6878699 * 2
def baseEnd_6878699 : Nat := 3532078864601687792227945

theorem tailTrace_6878699 : CollatzResearch.WordTrace tailWord_6878699 prefixEnd_6878699 3532078864601687792227945 := by
  unfold tailWord_6878699
  simp only [CollatzResearch.WordTrace]
  refine ⟨250886763706655786104639151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167257842471103857403092767 250886763706655786104639151)
  ·
    refine ⟨376330145559983679156958727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250886763706655786104639151 376330145559983679156958727)
    ·
      refine ⟨564495218339975518735438091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376330145559983679156958727 564495218339975518735438091)
      ·
        refine ⟨846742827509963278103157137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564495218339975518735438091 846742827509963278103157137)
        ·
          refine ⟨635057120632472458577367853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846742827509963278103157137 635057120632472458577367853)
          ·
            refine ⟨238146420237177171966512945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 635057120632472458577367853 238146420237177171966512945)
            ·
              refine ⟨178609815177882878974884709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238146420237177171966512945 178609815177882878974884709)
              ·
                refine ⟨33489340345853039807790883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178609815177882878974884709 33489340345853039807790883)
                ·
                  refine ⟨50234010518779559711686325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33489340345853039807790883 50234010518779559711686325)
                  ·
                    refine ⟨4709438486135583722970593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50234010518779559711686325 4709438486135583722970593)
                    ·
                      refine ⟨3532078864601687792227945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709438486135583722970593 3532078864601687792227945)
                      ·
                        rfl

theorem cell23_6878699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 5, 2].length) (baseStart_6878699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878699 prefixEnd_6878699 := by exact prefixLift 6878699
  have htrace : WordTrace (prefixWord ++ tailWord_6878699) baseStart_6878699 baseEnd_6878699 := by
    simpa [prefixWord, tailWord_6878699, baseEnd_6878699] using wordTrace_append hprefix tailTrace_6878699
  have hstable : (prefixWord ++ tailWord_6878699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878699).length < 2 ^ (prefixWord ++ tailWord_6878699).sum := by decide
  have hdescent : baseEnd_6878699 < baseStart_6878699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878716 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_6878716 : Nat := 118140960795 + 6878716 * 2 ^ 59
def prefixEnd_6878716 : Nat := 4983230072969 + 3 ^ 40 * 6878716 * 2
def baseEnd_6878716 : Nat := 3532087593772814225715367

theorem tailTrace_6878716 : CollatzResearch.WordTrace tailWord_6878716 prefixEnd_6878716 3532087593772814225715367 := by
  unfold tailWord_6878716
  simp only [CollatzResearch.WordTrace]
  refine ⟨125443691873797099004004001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167258255831729465338672001 125443691873797099004004001)
  ·
    refine ⟨94082768905347824253003001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125443691873797099004004001 94082768905347824253003001)
    ·
      refine ⟨70562076679010868189752251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94082768905347824253003001 70562076679010868189752251)
      ·
        refine ⟨105843115018516302284628377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70562076679010868189752251 105843115018516302284628377)
        ·
          refine ⟨79382336263887226713471283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105843115018516302284628377 79382336263887226713471283)
          ·
            refine ⟨119073504395830840070206925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79382336263887226713471283 119073504395830840070206925)
            ·
              refine ⟨44652564148436565026327597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119073504395830840070206925 44652564148436565026327597)
              ·
                refine ⟨16744711555663711884872849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44652564148436565026327597 16744711555663711884872849)
                ·
                  refine ⟨12558533666747783913654637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16744711555663711884872849 12558533666747783913654637)
                  ·
                    refine ⟨4709450125030418967620489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12558533666747783913654637 4709450125030418967620489)
                    ·
                      refine ⟨3532087593772814225715367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709450125030418967620489 3532087593772814225715367)
                      ·
                        rfl

theorem cell23_6878716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_6878716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878716 prefixEnd_6878716 := by exact prefixLift 6878716
  have htrace : WordTrace (prefixWord ++ tailWord_6878716) baseStart_6878716 baseEnd_6878716 := by
    simpa [prefixWord, tailWord_6878716, baseEnd_6878716] using wordTrace_append hprefix tailTrace_6878716
  have hstable : (prefixWord ++ tailWord_6878716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878716).length < 2 ^ (prefixWord ++ tailWord_6878716).sum := by decide
  have hdescent : baseEnd_6878716 < baseStart_6878716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878749 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6878749 : Nat := 118140960795 + 6878749 * 2 ^ 59
def prefixEnd_6878749 : Nat := 4983230072969 + 3 ^ 40 * 6878749 * 2
def baseEnd_6878749 : Nat := 3532104538634412596602715

theorem tailTrace_6878749 : CollatzResearch.WordTrace tailWord_6878749 prefixEnd_6878749 3532104538634412596602715 := by
  unfold tailWord_6878749
  simp only [CollatzResearch.WordTrace]
  refine ⟨250888587356474644643959301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167259058237649763095972867 250888587356474644643959301)
  ·
    refine ⟨47041610129338995870742369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250888587356474644643959301 47041610129338995870742369)
    ·
      refine ⟨35281207597004246903056777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47041610129338995870742369 35281207597004246903056777)
      ·
        refine ⟨26460905697753185177292583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35281207597004246903056777 26460905697753185177292583)
        ·
          refine ⟨39691358546629777765938875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26460905697753185177292583 39691358546629777765938875)
          ·
            refine ⟨59537037819944666648908313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39691358546629777765938875 59537037819944666648908313)
            ·
              refine ⟨44652778364958499986681235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59537037819944666648908313 44652778364958499986681235)
              ·
                refine ⟨66979167547437749980021853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44652778364958499986681235 66979167547437749980021853)
                ·
                  refine ⟨25117187830289156242508195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66979167547437749980021853 25117187830289156242508195)
                  ·
                    refine ⟨37675781745433734363762293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25117187830289156242508195 37675781745433734363762293)
                    ·
                      refine ⟨3532104538634412596602715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37675781745433734363762293 3532104538634412596602715)
                      ·
                        rfl

theorem cell23_6878749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6878749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878749 prefixEnd_6878749 := by exact prefixLift 6878749
  have htrace : WordTrace (prefixWord ++ tailWord_6878749) baseStart_6878749 baseEnd_6878749 := by
    simpa [prefixWord, tailWord_6878749, baseEnd_6878749] using wordTrace_append hprefix tailTrace_6878749
  have hstable : (prefixWord ++ tailWord_6878749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878749).length < 2 ^ (prefixWord ++ tailWord_6878749).sum := by decide
  have hdescent : baseEnd_6878749 < baseStart_6878749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878780 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_6878780 : Nat := 118140960795 + 6878780 * 2 ^ 59
def prefixEnd_6878780 : Nat := 4983230072969 + 3 ^ 40 * 6878780 * 2
def baseEnd_6878780 : Nat := 3532120456534701975315073

theorem tailTrace_6878780 : CollatzResearch.WordTrace tailWord_6878780 prefixEnd_6878780 3532120456534701975315073 := by
  unfold tailWord_6878780
  simp only [CollatzResearch.WordTrace]
  refine ⟨125444859009681168469168897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167259812012908224625558529 125444859009681168469168897)
  ·
    refine ⟨94083644257260876351876673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125444859009681168469168897 94083644257260876351876673)
    ·
      refine ⟨70562733192945657263907505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94083644257260876351876673 70562733192945657263907505)
      ·
        refine ⟨52922049894709242947930629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70562733192945657263907505 52922049894709242947930629)
        ·
          refine ⟨9922884355257983052736993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52922049894709242947930629 9922884355257983052736993)
          ·
            refine ⟨7442163266443487289552745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9922884355257983052736993 7442163266443487289552745)
            ·
              refine ⟨5581622449832615467164559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7442163266443487289552745 5581622449832615467164559)
              ·
                refine ⟨8372433674748923200746839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581622449832615467164559 8372433674748923200746839)
                ·
                  refine ⟨12558650512123384801120259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372433674748923200746839 12558650512123384801120259)
                  ·
                    refine ⟨18837975768185077201680389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12558650512123384801120259 18837975768185077201680389)
                    ·
                      refine ⟨3532120456534701975315073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18837975768185077201680389 3532120456534701975315073)
                      ·
                        rfl

theorem cell23_6878780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_6878780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878780 prefixEnd_6878780 := by exact prefixLift 6878780
  have htrace : WordTrace (prefixWord ++ tailWord_6878780) baseStart_6878780 baseEnd_6878780 := by
    simpa [prefixWord, tailWord_6878780, baseEnd_6878780] using wordTrace_append hprefix tailTrace_6878780
  have hstable : (prefixWord ++ tailWord_6878780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878780).length < 2 ^ (prefixWord ++ tailWord_6878780).sum := by decide
  have hdescent : baseEnd_6878780 < baseStart_6878780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878783 : List Nat := [1, 1, 2, 2, 3, 3, 4, 1, 1, 2, 3]
def baseStart_6878783 : Nat := 118140960795 + 6878783 * 2 ^ 59
def prefixEnd_6878783 : Nat := 4983230072969 + 3 ^ 40 * 6878783 * 2
def baseEnd_6878783 : Nat := 3532121996976665463577559

theorem tailTrace_6878783 : CollatzResearch.WordTrace tailWord_6878783 prefixEnd_6878783 3532121996976665463577559 := by
  unfold tailWord_6878783
  simp only [CollatzResearch.WordTrace]
  refine ⟨250889827438351468450697003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167259884958900978967131335 250889827438351468450697003)
  ·
    refine ⟨376334741157527202676045505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250889827438351468450697003 376334741157527202676045505)
    ·
      refine ⟨282251055868145402007034129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376334741157527202676045505 282251055868145402007034129)
      ·
        refine ⟨211688291901109051505275597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282251055868145402007034129 211688291901109051505275597)
        ·
          refine ⟨79383109462915894314478349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211688291901109051505275597 79383109462915894314478349)
          ·
            refine ⟨29768666048593460367929381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79383109462915894314478349 29768666048593460367929381)
            ·
              refine ⟨5581624884111273818986759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29768666048593460367929381 5581624884111273818986759)
              ·
                refine ⟨8372437326166910728480139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5581624884111273818986759 8372437326166910728480139)
                ·
                  refine ⟨12558655989250366092720209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372437326166910728480139 12558655989250366092720209)
                  ·
                    refine ⟨9418991991937774569540157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12558655989250366092720209 9418991991937774569540157)
                    ·
                      refine ⟨3532121996976665463577559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9418991991937774569540157 3532121996976665463577559)
                      ·
                        rfl

theorem cell23_6878783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_6878783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878783 prefixEnd_6878783 := by exact prefixLift 6878783
  have htrace : WordTrace (prefixWord ++ tailWord_6878783) baseStart_6878783 baseEnd_6878783 := by
    simpa [prefixWord, tailWord_6878783, baseEnd_6878783] using wordTrace_append hprefix tailTrace_6878783
  have hstable : (prefixWord ++ tailWord_6878783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878783).length < 2 ^ (prefixWord ++ tailWord_6878783).sum := by decide
  have hdescent : baseEnd_6878783 < baseStart_6878783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878790 : List Nat := [6, 1, 1, 1, 3, 1, 1, 1, 4, 4]
def baseStart_6878790 : Nat := 118140960795 + 6878790 * 2 ^ 59
def prefixEnd_6878790 : Nat := 4983230072969 + 3 ^ 40 * 6878790 * 2
def baseEnd_6878790 : Nat := 1177375197113748978730009

theorem tailTrace_6878790 : CollatzResearch.WordTrace tailWord_6878790 prefixEnd_6878790 1177375197113748978730009 := by
  unfold tailWord_6878790
  simp only [CollatzResearch.WordTrace]
  refine ⟨7840315085916440895193807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167260055166217405764134549 7840315085916440895193807)
  ·
    refine ⟨11760472628874661342790711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7840315085916440895193807 11760472628874661342790711)
    ·
      refine ⟨17640708943311992014186067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11760472628874661342790711 17640708943311992014186067)
      ·
        refine ⟨26461063414967988021279101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17640708943311992014186067 26461063414967988021279101)
        ·
          refine ⟨9922898780612995507979663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26461063414967988021279101 9922898780612995507979663)
          ·
            refine ⟨14884348170919493261969495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922898780612995507979663 14884348170919493261969495)
            ·
              refine ⟨22326522256379239892954243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14884348170919493261969495 22326522256379239892954243)
              ·
                refine ⟨33489783384568859839431365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22326522256379239892954243 33489783384568859839431365)
                ·
                  refine ⟨6279334384606661219893381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33489783384568859839431365 6279334384606661219893381)
                  ·
                    refine ⟨1177375197113748978730009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6279334384606661219893381 1177375197113748978730009)
                    ·
                      rfl

theorem cell23_6878790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_6878790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878790 prefixEnd_6878790 := by exact prefixLift 6878790
  have htrace : WordTrace (prefixWord ++ tailWord_6878790) baseStart_6878790 baseEnd_6878790 := by
    simpa [prefixWord, tailWord_6878790, baseEnd_6878790] using wordTrace_append hprefix tailTrace_6878790
  have hstable : (prefixWord ++ tailWord_6878790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878790).length < 2 ^ (prefixWord ++ tailWord_6878790).sum := by decide
  have hdescent : baseEnd_6878790 < baseStart_6878790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878797 : List Nat := [1, 6, 1, 1, 3, 1, 2, 1, 3, 2, 2]
def baseStart_6878797 : Nat := 118140960795 + 6878797 * 2 ^ 59
def prefixEnd_6878797 : Nat := 4983230072969 + 3 ^ 40 * 6878797 * 2
def baseEnd_6878797 : Nat := 3532129185705828408802495

theorem tailTrace_6878797 : CollatzResearch.WordTrace tailWord_6878797 prefixEnd_6878797 3532129185705828408802495 := by
  unfold tailWord_6878797
  simp only [CollatzResearch.WordTrace]
  refine ⟨250890338060300748841706645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167260225373533832561137763 250890338060300748841706645)
  ·
    refine ⟨11760484596576597601954999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250890338060300748841706645 11760484596576597601954999)
    ·
      refine ⟨17640726894864896402932499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11760484596576597601954999 17640726894864896402932499)
      ·
        refine ⟨26461090342297344604398749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17640726894864896402932499 26461090342297344604398749)
        ·
          refine ⟨9922908878361504226649531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26461090342297344604398749 9922908878361504226649531)
          ·
            refine ⟨14884363317542256339974297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922908878361504226649531 14884363317542256339974297)
            ·
              refine ⟨11163272488156692254980723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14884363317542256339974297 11163272488156692254980723)
              ·
                refine ⟨16744908732235038382471085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163272488156692254980723 16744908732235038382471085)
                ·
                  refine ⟨6279340774588139393426657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16744908732235038382471085 6279340774588139393426657)
                  ·
                    refine ⟨4709505580941104545069993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279340774588139393426657 4709505580941104545069993)
                    ·
                      refine ⟨3532129185705828408802495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709505580941104545069993 3532129185705828408802495)
                      ·
                        rfl

theorem cell23_6878797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_6878797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878797 prefixEnd_6878797 := by exact prefixLift 6878797
  have htrace : WordTrace (prefixWord ++ tailWord_6878797) baseStart_6878797 baseEnd_6878797 := by
    simpa [prefixWord, tailWord_6878797, baseEnd_6878797] using wordTrace_append hprefix tailTrace_6878797
  have hstable : (prefixWord ++ tailWord_6878797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878797).length < 2 ^ (prefixWord ++ tailWord_6878797).sum := by decide
  have hdescent : baseEnd_6878797 < baseStart_6878797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878823 : List Nat := [1, 1, 5, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_6878823 : Nat := 118140960795 + 6878823 * 2 ^ 59
def prefixEnd_6878823 : Nat := 4983230072969 + 3 ^ 40 * 6878823 * 2
def baseEnd_6878823 : Nat := 3532142536202845307077375

theorem tailTrace_6878823 : CollatzResearch.WordTrace tailWord_6878823 prefixEnd_6878823 3532142536202845307077375 := by
  unfold tailWord_6878823
  simp only [CollatzResearch.WordTrace]
  refine ⟨250891286358206555282153123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167260857572137703521435415 250891286358206555282153123)
  ·
    refine ⟨376336929537309832923229685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250891286358206555282153123 376336929537309832923229685)
    ·
      refine ⟨35281587144122796836552783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 376336929537309832923229685 35281587144122796836552783)
      ·
        refine ⟨52922380716184195254829175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35281587144122796836552783 52922380716184195254829175)
        ·
          refine ⟨79383571074276292882243763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52922380716184195254829175 79383571074276292882243763)
          ·
            refine ⟨119075356611414439323365645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79383571074276292882243763 119075356611414439323365645)
            ·
              refine ⟨44653258729280414746262117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119075356611414439323365645 44653258729280414746262117)
              ·
                refine ⟨8372486011740077764924147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44653258729280414746262117 8372486011740077764924147)
                ·
                  refine ⟨12558729017610116647386221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372486011740077764924147 12558729017610116647386221)
                  ·
                    refine ⟨4709523381603793742769833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12558729017610116647386221 4709523381603793742769833)
                    ·
                      refine ⟨3532142536202845307077375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709523381603793742769833 3532142536202845307077375)
                      ·
                        rfl

theorem cell23_6878823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_6878823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878823 prefixEnd_6878823 := by exact prefixLift 6878823
  have htrace : WordTrace (prefixWord ++ tailWord_6878823) baseStart_6878823 baseEnd_6878823 := by
    simpa [prefixWord, tailWord_6878823, baseEnd_6878823] using wordTrace_append hprefix tailTrace_6878823
  have hstable : (prefixWord ++ tailWord_6878823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878823).length < 2 ^ (prefixWord ++ tailWord_6878823).sum := by decide
  have hdescent : baseEnd_6878823 < baseStart_6878823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878839 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_6878839 : Nat := 118140960795 + 6878839 * 2 ^ 59
def prefixEnd_6878839 : Nat := 4983230072969 + 3 ^ 40 * 6878839 * 2
def baseEnd_6878839 : Nat := 3532150751893317244477301

theorem tailTrace_6878839 : CollatzResearch.WordTrace tailWord_6878839 prefixEnd_6878839 3532150751893317244477301 := by
  unfold tailWord_6878839
  simp only [CollatzResearch.WordTrace]
  refine ⟨250891869926148590014735571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167261246617432393343157047 250891869926148590014735571)
  ·
    refine ⟨376337804889222885022103357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250891869926148590014735571 376337804889222885022103357)
    ·
      refine ⟨141126676833458581883288759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376337804889222885022103357 141126676833458581883288759)
      ·
        refine ⟨211690015250187872824933139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141126676833458581883288759 211690015250187872824933139)
        ·
          refine ⟨317535022875281809237399709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211690015250187872824933139 317535022875281809237399709)
          ·
            refine ⟨119075633578230678464024891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317535022875281809237399709 119075633578230678464024891)
            ·
              refine ⟨178613450367346017696037337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119075633578230678464024891 178613450367346017696037337)
              ·
                refine ⟨133960087775509513272028003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178613450367346017696037337 133960087775509513272028003)
                ·
                  refine ⟨200940131663264269908042005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133960087775509513272028003 200940131663264269908042005)
                  ·
                    refine ⟨9419068671715512651939469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 200940131663264269908042005 9419068671715512651939469)
                    ·
                      refine ⟨3532150751893317244477301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9419068671715512651939469 3532150751893317244477301)
                      ·
                        rfl

theorem cell23_6878839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_6878839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878839 prefixEnd_6878839 := by exact prefixLift 6878839
  have htrace : WordTrace (prefixWord ++ tailWord_6878839) baseStart_6878839 baseEnd_6878839 := by
    simpa [prefixWord, tailWord_6878839, baseEnd_6878839] using wordTrace_append hprefix tailTrace_6878839
  have hstable : (prefixWord ++ tailWord_6878839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878839).length < 2 ^ (prefixWord ++ tailWord_6878839).sum := by decide
  have hdescent : baseEnd_6878839 < baseStart_6878839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878853 : List Nat := [1, 3, 1, 1, 4, 1, 1, 3, 4, 2, 2]
def baseStart_6878853 : Nat := 118140960795 + 6878853 * 2 ^ 59
def prefixEnd_6878853 : Nat := 4983230072969 + 3 ^ 40 * 6878853 * 2
def baseEnd_6878853 : Nat := 3532157940622480189702237

theorem tailTrace_6878853 : CollatzResearch.WordTrace tailWord_6878853 prefixEnd_6878853 3532157940622480189702237 := by
  unfold tailWord_6878853
  simp only [CollatzResearch.WordTrace]
  refine ⟨250892380548097870405745213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167261587032065246937163475 250892380548097870405745213)
  ·
    refine ⟨94084642705536701402154455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250892380548097870405745213 94084642705536701402154455)
    ·
      refine ⟨141126964058305052103231683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94084642705536701402154455 141126964058305052103231683)
      ·
        refine ⟨211690446087457578154847525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141126964058305052103231683 211690446087457578154847525)
        ·
          refine ⟨39691958641398295904033911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211690446087457578154847525 39691958641398295904033911)
          ·
            refine ⟨59537937962097443856050867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39691958641398295904033911 59537937962097443856050867)
            ·
              refine ⟨89306906943146165784076301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59537937962097443856050867 89306906943146165784076301)
              ·
                refine ⟨33490090103679812169028613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89306906943146165784076301 33490090103679812169028613)
                ·
                  refine ⟨6279391894439964781692865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33490090103679812169028613 6279391894439964781692865)
                  ·
                    refine ⟨4709543920829973586269649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279391894439964781692865 4709543920829973586269649)
                    ·
                      refine ⟨3532157940622480189702237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709543920829973586269649 3532157940622480189702237)
                      ·
                        rfl

theorem cell23_6878853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_6878853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878853 prefixEnd_6878853 := by exact prefixLift 6878853
  have htrace : WordTrace (prefixWord ++ tailWord_6878853) baseStart_6878853 baseEnd_6878853 := by
    simpa [prefixWord, tailWord_6878853, baseEnd_6878853] using wordTrace_append hprefix tailTrace_6878853
  have hstable : (prefixWord ++ tailWord_6878853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878853).length < 2 ^ (prefixWord ++ tailWord_6878853).sum := by decide
  have hdescent : baseEnd_6878853 < baseStart_6878853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878893 : List Nat := [1, 5, 2, 1, 1, 1, 2, 5, 5]
def baseStart_6878893 : Nat := 118140960795 + 6878893 * 2 ^ 59
def prefixEnd_6878893 : Nat := 4983230072969 + 3 ^ 40 * 6878893 * 2
def baseEnd_6878893 : Nat := 392464275538740003689117

theorem tailTrace_6878893 : CollatzResearch.WordTrace tailWord_6878893 prefixEnd_6878893 392464275538740003689117 := by
  unfold tailWord_6878893
  simp only [CollatzResearch.WordTrace]
  refine ⟨250893839467952957237201333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167262559645301971491467555 250893839467952957237201333)
  ·
    refine ⟨23521297450120589740987625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250893839467952957237201333 23521297450120589740987625)
    ·
      refine ⟨17640973087590442305740719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23521297450120589740987625 17640973087590442305740719)
      ·
        refine ⟨26461459631385663458611079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17640973087590442305740719 26461459631385663458611079)
        ·
          refine ⟨39692189447078495187916619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461459631385663458611079 39692189447078495187916619)
          ·
            refine ⟨59538284170617742781874929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39692189447078495187916619 59538284170617742781874929)
            ·
              refine ⟨44653713127963307086406197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59538284170617742781874929 44653713127963307086406197)
              ·
                refine ⟨4186285605746560039350581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44653713127963307086406197 4186285605746560039350581)
                ·
                  refine ⟨392464275538740003689117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186285605746560039350581 392464275538740003689117)
                  ·
                    rfl

theorem cell23_6878893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_6878893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878893 prefixEnd_6878893 := by exact prefixLift 6878893
  have htrace : WordTrace (prefixWord ++ tailWord_6878893) baseStart_6878893 baseEnd_6878893 := by
    simpa [prefixWord, tailWord_6878893, baseEnd_6878893] using wordTrace_append hprefix tailTrace_6878893
  have hstable : (prefixWord ++ tailWord_6878893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878893).length < 2 ^ (prefixWord ++ tailWord_6878893).sum := by decide
  have hdescent : baseEnd_6878893 < baseStart_6878893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878899 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5]
def baseStart_6878899 : Nat := 118140960795 + 6878899 * 2 ^ 59
def prefixEnd_6878899 : Nat := 4983230072969 + 3 ^ 40 * 6878899 * 2
def baseEnd_6878899 : Nat := 3532181560732587009727025

theorem tailTrace_6878899 : CollatzResearch.WordTrace tailWord_6878899 prefixEnd_6878899 3532181560732587009727025 := by
  unfold tailWord_6878899
  simp only [CollatzResearch.WordTrace]
  refine ⟨250894058305931220261919751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167262705537287480174613167 250894058305931220261919751)
  ·
    refine ⟨376341087458896830392879627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250894058305931220261919751 376341087458896830392879627)
    ·
      refine ⟨564511631188345245589319441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376341087458896830392879627 564511631188345245589319441)
      ·
        refine ⟨423383723391258934191989581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564511631188345245589319441 423383723391258934191989581)
        ·
          refine ⟨158768896271722100321996093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423383723391258934191989581 158768896271722100321996093)
          ·
            refine ⟨59538336101895787620748535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158768896271722100321996093 59538336101895787620748535)
            ·
              refine ⟨89307504152843681431122803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59538336101895787620748535 89307504152843681431122803)
              ·
                refine ⟨133961256229265522146684205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89307504152843681431122803 133961256229265522146684205)
                ·
                  refine ⟨50235471085974570805006577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133961256229265522146684205 50235471085974570805006577)
                  ·
                    refine ⟨37676603314480928103754933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50235471085974570805006577 37676603314480928103754933)
                    ·
                      refine ⟨3532181560732587009727025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37676603314480928103754933 3532181560732587009727025)
                      ·
                        rfl

theorem cell23_6878899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 5].length) (baseStart_6878899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878899 prefixEnd_6878899 := by exact prefixLift 6878899
  have htrace : WordTrace (prefixWord ++ tailWord_6878899) baseStart_6878899 baseEnd_6878899 := by
    simpa [prefixWord, tailWord_6878899, baseEnd_6878899] using wordTrace_append hprefix tailTrace_6878899
  have hstable : (prefixWord ++ tailWord_6878899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878899).length < 2 ^ (prefixWord ++ tailWord_6878899).sum := by decide
  have hdescent : baseEnd_6878899 < baseStart_6878899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878906 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 2, 5]
def baseStart_6878906 : Nat := 118140960795 + 6878906 * 2 ^ 59
def prefixEnd_6878906 : Nat := 4983230072969 + 3 ^ 40 * 6878906 * 2
def baseEnd_6878906 : Nat := 1177395051699056160779831

theorem tailTrace_6878906 : CollatzResearch.WordTrace tailWord_6878906 prefixEnd_6878906 1177395051699056160779831 := by
  unfold tailWord_6878906
  simp only [CollatzResearch.WordTrace]
  refine ⟨62723578404226465114356143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167262875744603906971616381 62723578404226465114356143)
  ·
    refine ⟨94085367606339697671534215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62723578404226465114356143 94085367606339697671534215)
    ·
      refine ⟨141128051409509546507301323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94085367606339697671534215 141128051409509546507301323)
      ·
        refine ⟨211692077114264319760951985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141128051409509546507301323 211692077114264319760951985)
        ·
          refine ⟨158769057835698239820713989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211692077114264319760951985 158769057835698239820713989)
          ·
            refine ⟨29769198344193419966383873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158769057835698239820713989 29769198344193419966383873)
            ·
              refine ⟨22326898758145064974787905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29769198344193419966383873 22326898758145064974787905)
              ·
                refine ⟨16745174068608798731090929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22326898758145064974787905 16745174068608798731090929)
                ·
                  refine ⟨12558880551456599048318197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16745174068608798731090929 12558880551456599048318197)
                  ·
                    refine ⟨1177395051699056160779831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12558880551456599048318197 1177395051699056160779831)
                    ·
                      rfl

theorem cell23_6878906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 2, 5].length) (baseStart_6878906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878906 prefixEnd_6878906 := by exact prefixLift 6878906
  have htrace : WordTrace (prefixWord ++ tailWord_6878906) baseStart_6878906 baseEnd_6878906 := by
    simpa [prefixWord, tailWord_6878906, baseEnd_6878906] using wordTrace_append hprefix tailTrace_6878906
  have hstable : (prefixWord ++ tailWord_6878906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878906).length < 2 ^ (prefixWord ++ tailWord_6878906).sum := by decide
  have hdescent : baseEnd_6878906 < baseStart_6878906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878910 : List Nat := [4, 2, 1, 1, 2, 2, 4, 2, 5]
def baseStart_6878910 : Nat := 118140960795 + 6878910 * 2 ^ 59
def prefixEnd_6878910 : Nat := 4983230072969 + 3 ^ 40 * 6878910 * 2
def baseEnd_6878910 : Nat := 392465245446642940743275

theorem tailTrace_6878910 : CollatzResearch.WordTrace tailWord_6878910 prefixEnd_6878910 392465245446642940743275 := by
  unfold tailWord_6878910
  simp only [CollatzResearch.WordTrace]
  refine ⟨31361807438611421142571273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167262973005927579427046789 31361807438611421142571273)
  ·
    refine ⟨23521355578958565856928455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31361807438611421142571273 23521355578958565856928455)
    ·
      refine ⟨35282033368437848785392683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23521355578958565856928455 35282033368437848785392683)
      ·
        refine ⟨52923050052656773178089025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35282033368437848785392683 52923050052656773178089025)
        ·
          refine ⟨39692287539492579883566769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52923050052656773178089025 39692287539492579883566769)
          ·
            refine ⟨29769215654619434912675077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39692287539492579883566769 29769215654619434912675077)
            ·
              refine ⟨5581727935241144046126577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29769215654619434912675077 5581727935241144046126577)
              ·
                refine ⟨4186295951430858034594933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5581727935241144046126577 4186295951430858034594933)
                ·
                  refine ⟨392465245446642940743275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186295951430858034594933 392465245446642940743275)
                  ·
                    rfl

theorem cell23_6878910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_6878910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878910 prefixEnd_6878910 := by exact prefixLift 6878910
  have htrace : WordTrace (prefixWord ++ tailWord_6878910) baseStart_6878910 baseEnd_6878910 := by
    simpa [prefixWord, tailWord_6878910, baseEnd_6878910] using wordTrace_append hprefix tailTrace_6878910
  have hstable : (prefixWord ++ tailWord_6878910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878910).length < 2 ^ (prefixWord ++ tailWord_6878910).sum := by decide
  have hdescent : baseEnd_6878910 < baseStart_6878910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878916 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_6878916 : Nat := 118140960795 + 6878916 * 2 ^ 59
def prefixEnd_6878916 : Nat := 4983230072969 + 3 ^ 40 * 6878916 * 2
def baseEnd_6878916 : Nat := 3532190289903713443214447

theorem tailTrace_6878916 : CollatzResearch.WordTrace tailWord_6878916 prefixEnd_6878916 3532190289903713443214447 := by
  unfold tailWord_6878916
  simp only [CollatzResearch.WordTrace]
  refine ⟨125447339173434816082644301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167263118897913088110192401 125447339173434816082644301)
  ·
    refine ⟨47042752190038056030991613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125447339173434816082644301 47042752190038056030991613)
    ·
      refine ⟨17641032071264271011621855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47042752190038056030991613 17641032071264271011621855)
      ·
        refine ⟨26461548106896406517432783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17641032071264271011621855 26461548106896406517432783)
        ·
          refine ⟨39692322160344609776149175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26461548106896406517432783 39692322160344609776149175)
          ·
            refine ⟨59538483240516914664223763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39692322160344609776149175 59538483240516914664223763)
            ·
              refine ⟨89307724860775371996335645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59538483240516914664223763 89307724860775371996335645)
              ·
                refine ⟨33490396822790764498625867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89307724860775371996335645 33490396822790764498625867)
                ·
                  refine ⟨50235595234186146747938801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33490396822790764498625867 50235595234186146747938801)
                  ·
                    refine ⟨37676696425639610060954101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50235595234186146747938801 37676696425639610060954101)
                    ·
                      refine ⟨3532190289903713443214447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37676696425639610060954101 3532190289903713443214447)
                      ·
                        rfl

theorem cell23_6878916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_6878916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878916 prefixEnd_6878916 := by exact prefixLift 6878916
  have htrace : WordTrace (prefixWord ++ tailWord_6878916) baseStart_6878916 baseEnd_6878916 := by
    simpa [prefixWord, tailWord_6878916, baseEnd_6878916] using wordTrace_append hprefix tailTrace_6878916
  have hstable : (prefixWord ++ tailWord_6878916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878916).length < 2 ^ (prefixWord ++ tailWord_6878916).sum := by decide
  have hdescent : baseEnd_6878916 < baseStart_6878916 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6878926 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_6878926 : Nat := 118140960795 + 6878926 * 2 ^ 59
def prefixEnd_6878926 : Nat := 4983230072969 + 3 ^ 40 * 6878926 * 2
def baseEnd_6878926 : Nat := 3532195424710258404089401

theorem tailTrace_6878926 : CollatzResearch.WordTrace tailWord_6878926 prefixEnd_6878926 3532195424710258404089401 := by
  unfold tailWord_6878926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31361880384604175484144079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167263362051222269248768421 31361880384604175484144079)
  ·
    refine ⟨47042820576906263226216119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31361880384604175484144079 47042820576906263226216119)
    ·
      refine ⟨70564230865359394839324179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47042820576906263226216119 70564230865359394839324179)
      ·
        refine ⟨105846346298039092258986269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70564230865359394839324179 105846346298039092258986269)
        ·
          refine ⟨39692379861764659597119851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105846346298039092258986269 39692379861764659597119851)
          ·
            refine ⟨59538569792646989395679777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39692379861764659597119851 59538569792646989395679777)
            ·
              refine ⟨44653927344485242046759833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59538569792646989395679777 44653927344485242046759833)
              ·
                refine ⟨33490445508363931535069875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44653927344485242046759833 33490445508363931535069875)
                ·
                  refine ⟨50235668262545897302604813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33490445508363931535069875 50235668262545897302604813)
                  ·
                    refine ⟨18838375598454711488476805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50235668262545897302604813 18838375598454711488476805)
                    ·
                      refine ⟨3532195424710258404089401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18838375598454711488476805 3532195424710258404089401)
                      ·
                        rfl

theorem cell23_6878926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_6878926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6878926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6878926 prefixEnd_6878926 := by exact prefixLift 6878926
  have htrace : WordTrace (prefixWord ++ tailWord_6878926) baseStart_6878926 baseEnd_6878926 := by
    simpa [prefixWord, tailWord_6878926, baseEnd_6878926] using wordTrace_append hprefix tailTrace_6878926
  have hstable : (prefixWord ++ tailWord_6878926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6878926).length < 2 ^ (prefixWord ++ tailWord_6878926).sum := by decide
  have hdescent : baseEnd_6878926 < baseStart_6878926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6878926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879013 : List Nat := [1, 3, 1, 2, 3, 2, 2, 3, 1, 5]
def baseStart_6879013 : Nat := 118140960795 + 6879013 * 2 ^ 59
def prefixEnd_6879013 : Nat := 4983230072969 + 3 ^ 40 * 6879013 * 2
def baseEnd_6879013 : Nat := 1177413365842399854567167

theorem tailTrace_6879013 : CollatzResearch.WordTrace tailWord_6879013 prefixEnd_6879013 1177413365842399854567167 := by
  unfold tailWord_6879013
  simp only [CollatzResearch.WordTrace]
  refine ⟨250898216227518217731569693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167265477485012145154379795 250898216227518217731569693)
  ·
    refine ⟨94086831085319331649338635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250898216227518217731569693 94086831085319331649338635)
    ·
      refine ⟨141130246627978997474007953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94086831085319331649338635 141130246627978997474007953)
      ·
        refine ⟨105847684970984248105505965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141130246627978997474007953 105847684970984248105505965)
        ·
          refine ⟨39692881864119093039564737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105847684970984248105505965 39692881864119093039564737)
          ·
            refine ⟨29769661398089319779673553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39692881864119093039564737 29769661398089319779673553)
            ·
              refine ⟨22327246048566989834755165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29769661398089319779673553 22327246048566989834755165)
              ·
                refine ⟨8372717268212621188033187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22327246048566989834755165 8372717268212621188033187)
                ·
                  refine ⟨12559075902318931782049781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372717268212621188033187 12559075902318931782049781)
                  ·
                    refine ⟨1177413365842399854567167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12559075902318931782049781 1177413365842399854567167)
                    ·
                      rfl

theorem cell23_6879013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_6879013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879013 prefixEnd_6879013 := by exact prefixLift 6879013
  have htrace : WordTrace (prefixWord ++ tailWord_6879013) baseStart_6879013 baseEnd_6879013 := by
    simpa [prefixWord, tailWord_6879013, baseEnd_6879013] using wordTrace_append hprefix tailTrace_6879013
  have hstable : (prefixWord ++ tailWord_6879013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879013).length < 2 ^ (prefixWord ++ tailWord_6879013).sum := by decide
  have hdescent : baseEnd_6879013 < baseStart_6879013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879020 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 2, 3, 2]
def baseStart_6879020 : Nat := 118140960795 + 6879020 * 2 ^ 59
def prefixEnd_6879020 : Nat := 4983230072969 + 3 ^ 40 * 6879020 * 2
def baseEnd_6879020 : Nat := 3532243691891781036313969

theorem tailTrace_6879020 : CollatzResearch.WordTrace tailWord_6879020 prefixEnd_6879020 3532243691891781036313969 := by
  unfold tailWord_6879020
  simp only [CollatzResearch.WordTrace]
  refine ⟨125449235769246428963537257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167265647692328571951383009 125449235769246428963537257)
  ·
    refine ⟨94086926826934821722652943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125449235769246428963537257 94086926826934821722652943)
    ·
      refine ⟨141130390240402232583979415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94086926826934821722652943 141130390240402232583979415)
      ·
        refine ⟨211695585360603348875969123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141130390240402232583979415 211695585360603348875969123)
        ·
          refine ⟨317543378040905023313953685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211695585360603348875969123 317543378040905023313953685)
          ·
            refine ⟨14884845845667422967841579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317543378040905023313953685 14884845845667422967841579)
            ·
              refine ⟨22327268768501134451762369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14884845845667422967841579 22327268768501134451762369)
              ·
                refine ⟨16745451576375850838821777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22327268768501134451762369 16745451576375850838821777)
                ·
                  refine ⟨12559088682281888129116333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16745451576375850838821777 12559088682281888129116333)
                  ·
                    refine ⟨4709658255855708048418625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12559088682281888129116333 4709658255855708048418625)
                    ·
                      refine ⟨3532243691891781036313969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709658255855708048418625 3532243691891781036313969)
                      ·
                        rfl

theorem cell23_6879020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_6879020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879020 prefixEnd_6879020 := by exact prefixLift 6879020
  have htrace : WordTrace (prefixWord ++ tailWord_6879020) baseStart_6879020 baseEnd_6879020 := by
    simpa [prefixWord, tailWord_6879020, baseEnd_6879020] using wordTrace_append hprefix tailTrace_6879020
  have hstable : (prefixWord ++ tailWord_6879020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879020).length < 2 ^ (prefixWord ++ tailWord_6879020).sum := by decide
  have hdescent : baseEnd_6879020 < baseStart_6879020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879027 : List Nat := [1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 3]
def baseStart_6879027 : Nat := 118140960795 + 6879027 * 2 ^ 59
def prefixEnd_6879027 : Nat := 4983230072969 + 3 ^ 40 * 6879027 * 2
def baseEnd_6879027 : Nat := 3532247286256362508926437

theorem tailTrace_6879027 : CollatzResearch.WordTrace tailWord_6879027 prefixEnd_6879027 3532247286256362508926437 := by
  unfold tailWord_6879027
  simp only [CollatzResearch.WordTrace]
  refine ⟨250898726849467498122579335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167265817899644998748386223 250898726849467498122579335)
  ·
    refine ⟨376348090274201247183869003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250898726849467498122579335 376348090274201247183869003)
    ·
      refine ⟨564522135411301870775803505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376348090274201247183869003 564522135411301870775803505)
      ·
        refine ⟨423391601558476403081852629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564522135411301870775803505 423391601558476403081852629)
        ·
          refine ⟨9923240661526790697230921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 423391601558476403081852629 9923240661526790697230921)
          ·
            refine ⟨7442430496145093022923191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9923240661526790697230921 7442430496145093022923191)
            ·
              refine ⟨11163645744217639534384787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442430496145093022923191 11163645744217639534384787)
              ·
                refine ⟨16745468616326459301577181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163645744217639534384787 16745468616326459301577181)
                ·
                  refine ⟨6279550731122422238091443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16745468616326459301577181 6279550731122422238091443)
                  ·
                    refine ⟨9419326096683633357137165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6279550731122422238091443 9419326096683633357137165)
                    ·
                      refine ⟨3532247286256362508926437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9419326096683633357137165 3532247286256362508926437)
                      ·
                        rfl

theorem cell23_6879027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 3].length) (baseStart_6879027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879027 prefixEnd_6879027 := by exact prefixLift 6879027
  have htrace : WordTrace (prefixWord ++ tailWord_6879027) baseStart_6879027 baseEnd_6879027 := by
    simpa [prefixWord, tailWord_6879027, baseEnd_6879027] using wordTrace_append hprefix tailTrace_6879027
  have hstable : (prefixWord ++ tailWord_6879027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879027).length < 2 ^ (prefixWord ++ tailWord_6879027).sum := by decide
  have hdescent : baseEnd_6879027 < baseStart_6879027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879050 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2]
def baseStart_6879050 : Nat := 118140960795 + 6879050 * 2 ^ 59
def prefixEnd_6879050 : Nat := 4983230072969 + 3 ^ 40 * 6879050 * 2
def baseEnd_6879050 : Nat := 3532259096311415918938831

theorem tailTrace_6879050 : CollatzResearch.WordTrace tailWord_6879050 prefixEnd_6879050 3532259096311415918938831 := by
  unfold tailWord_6879050
  simp only [CollatzResearch.WordTrace]
  refine ⟨62724891432096043262666651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167266377152256115367111069 62724891432096043262666651)
  ·
    refine ⟨94087337148144064893999977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62724891432096043262666651 94087337148144064893999977)
    ·
      refine ⟨70565502861108048670499983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94087337148144064893999977 70565502861108048670499983)
      ·
        refine ⟨105848254291662073005749975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70565502861108048670499983 105848254291662073005749975)
        ·
          refine ⟨158772381437493109508624963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105848254291662073005749975 158772381437493109508624963)
          ·
            refine ⟨238158572156239664262937445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158772381437493109508624963 238158572156239664262937445)
            ·
              refine ⟨44654732279294937049300771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238158572156239664262937445 44654732279294937049300771)
              ·
                refine ⟨66982098418942405573951157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44654732279294937049300771 66982098418942405573951157)
                ·
                  refine ⟨6279571726775850522557921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66982098418942405573951157 6279571726775850522557921)
                  ·
                    refine ⟨4709678795081887891918441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279571726775850522557921 4709678795081887891918441)
                    ·
                      refine ⟨3532259096311415918938831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709678795081887891918441 3532259096311415918938831)
                      ·
                        rfl

theorem cell23_6879050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 5, 2, 2].length) (baseStart_6879050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879050 prefixEnd_6879050 := by exact prefixLift 6879050
  have htrace : WordTrace (prefixWord ++ tailWord_6879050) baseStart_6879050 baseEnd_6879050 := by
    simpa [prefixWord, tailWord_6879050, baseEnd_6879050] using wordTrace_append hprefix tailTrace_6879050
  have hstable : (prefixWord ++ tailWord_6879050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879050).length < 2 ^ (prefixWord ++ tailWord_6879050).sum := by decide
  have hdescent : baseEnd_6879050 < baseStart_6879050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879084 : List Nat := [2, 2, 1, 1, 4, 3, 1, 4, 1, 2, 2]
def baseStart_6879084 : Nat := 118140960795 + 6879084 * 2 ^ 59
def prefixEnd_6879084 : Nat := 4983230072969 + 3 ^ 40 * 6879084 * 2
def baseEnd_6879084 : Nat := 3532276554653668785913675

theorem tailTrace_6879084 : CollatzResearch.WordTrace tailWord_6879084 prefixEnd_6879084 3532276554653668785913675 := by
  unfold tailWord_6879084
  simp only [CollatzResearch.WordTrace]
  refine ⟨125450402905130498428702153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167267203873507331238269537 125450402905130498428702153)
  ·
    refine ⟨94087802178847873821526615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125450402905130498428702153 94087802178847873821526615)
    ·
      refine ⟨141131703268271810732289923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94087802178847873821526615 141131703268271810732289923)
      ·
        refine ⟨211697554902407716098434885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141131703268271810732289923 211697554902407716098434885)
        ·
          refine ⟨39693291544201446768456541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211697554902407716098434885 39693291544201446768456541)
          ·
            refine ⟨14884984329075542538171203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39693291544201446768456541 14884984329075542538171203)
            ·
              refine ⟨22327476493613313807256805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14884984329075542538171203 22327476493613313807256805)
              ·
                refine ⟨4186401842552496338860651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22327476493613313807256805 4186401842552496338860651)
                ·
                  refine ⟨6279602763828744508290977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186401842552496338860651 6279602763828744508290977)
                  ·
                    refine ⟨4709702072871558381218233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279602763828744508290977 4709702072871558381218233)
                    ·
                      refine ⟨3532276554653668785913675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709702072871558381218233 3532276554653668785913675)
                      ·
                        rfl

theorem cell23_6879084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_6879084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879084 prefixEnd_6879084 := by exact prefixLift 6879084
  have htrace : WordTrace (prefixWord ++ tailWord_6879084) baseStart_6879084 baseEnd_6879084 := by
    simpa [prefixWord, tailWord_6879084, baseEnd_6879084] using wordTrace_append hprefix tailTrace_6879084
  have hstable : (prefixWord ++ tailWord_6879084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879084).length < 2 ^ (prefixWord ++ tailWord_6879084).sum := by decide
  have hdescent : baseEnd_6879084 < baseStart_6879084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879116 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 3, 8]
def baseStart_6879116 : Nat := 118140960795 + 6879116 * 2 ^ 59
def prefixEnd_6879116 : Nat := 4983230072969 + 3 ^ 40 * 6879116 * 2
def baseEnd_6879116 : Nat := 1177430995344870886904509

theorem tailTrace_6879116 : CollatzResearch.WordTrace tailWord_6879116 prefixEnd_6879116 1177430995344870886904509 := by
  unfold tailWord_6879116
  simp only [CollatzResearch.WordTrace]
  refine ⟨125450986473072533161284601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167267981964096710881712801 125450986473072533161284601)
  ·
    refine ⟨94088239854804399870963451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125450986473072533161284601 94088239854804399870963451)
    ·
      refine ⟨141132359782206599806445177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94088239854804399870963451 141132359782206599806445177)
      ·
        refine ⟨105849269836654949854833883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141132359782206599806445177 105849269836654949854833883)
        ·
          refine ⟨158773904754982424782250825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105849269836654949854833883 158773904754982424782250825)
          ·
            refine ⟨119080428566236818586688119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158773904754982424782250825 119080428566236818586688119)
            ·
              refine ⟨178620642849355227880032179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119080428566236818586688119 178620642849355227880032179)
              ·
                refine ⟨267930964274032841820048269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178620642849355227880032179 267930964274032841820048269)
                ·
                  refine ⟨100474111602762315682518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267930964274032841820048269 100474111602762315682518101)
                  ·
                    refine ⟨1177430995344870886904509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100474111602762315682518101 1177430995344870886904509)
                    ·
                      rfl

theorem cell23_6879116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_6879116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879116 prefixEnd_6879116 := by exact prefixLift 6879116
  have htrace : WordTrace (prefixWord ++ tailWord_6879116) baseStart_6879116 baseEnd_6879116 := by
    simpa [prefixWord, tailWord_6879116, baseEnd_6879116] using wordTrace_append hprefix tailTrace_6879116
  have hstable : (prefixWord ++ tailWord_6879116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879116).length < 2 ^ (prefixWord ++ tailWord_6879116).sum := by decide
  have hdescent : baseEnd_6879116 < baseStart_6879116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879118 : List Nat := [4, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_6879118 : Nat := 118140960795 + 6879118 * 2 ^ 59
def prefixEnd_6879118 : Nat := 4983230072969 + 3 ^ 40 * 6879118 * 2
def baseEnd_6879118 : Nat := 3532294012995921652888519

theorem tailTrace_6879118 : CollatzResearch.WordTrace tailWord_6879118 prefixEnd_6879118 3532294012995921652888519 := by
  unfold tailWord_6879118
  simp only [CollatzResearch.WordTrace]
  refine ⟨31362755736517227583017751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167268030594758547109428005 31362755736517227583017751)
  ·
    refine ⟨47044133604775841374526627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31362755736517227583017751 47044133604775841374526627)
    ·
      refine ⟨70566200407163762061789941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47044133604775841374526627 70566200407163762061789941)
      ·
        refine ⟨6615581288171602693292807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70566200407163762061789941 6615581288171602693292807)
        ·
          refine ⟨9923371932257404039939211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615581288171602693292807 9923371932257404039939211)
          ·
            refine ⟨14885057898386106059908817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9923371932257404039939211 14885057898386106059908817)
            ·
              refine ⟨11163793423789579544931613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14885057898386106059908817 11163793423789579544931613)
              ·
                refine ⟨4186422533921092329349355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11163793423789579544931613 4186422533921092329349355)
                ·
                  refine ⟨6279633800881638494024033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186422533921092329349355 6279633800881638494024033)
                  ·
                    refine ⟨4709725350661228870518025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279633800881638494024033 4709725350661228870518025)
                    ·
                      refine ⟨3532294012995921652888519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709725350661228870518025 3532294012995921652888519)
                      ·
                        rfl

theorem cell23_6879118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_6879118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879118 prefixEnd_6879118 := by exact prefixLift 6879118
  have htrace : WordTrace (prefixWord ++ tailWord_6879118) baseStart_6879118 baseEnd_6879118 := by
    simpa [prefixWord, tailWord_6879118, baseEnd_6879118] using wordTrace_append hprefix tailTrace_6879118
  have hstable : (prefixWord ++ tailWord_6879118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879118).length < 2 ^ (prefixWord ++ tailWord_6879118).sum := by decide
  have hdescent : baseEnd_6879118 < baseStart_6879118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879123 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 2, 8, 2]
def baseStart_6879123 : Nat := 118140960795 + 6879123 * 2 ^ 59
def prefixEnd_6879123 : Nat := 4983230072969 + 3 ^ 40 * 6879123 * 2
def baseEnd_6879123 : Nat := 3532296580399194133325995

theorem tailTrace_6879123 : CollatzResearch.WordTrace tailWord_6879123 prefixEnd_6879123 3532296580399194133325995 := by
  unfold tailWord_6879123
  simp only [CollatzResearch.WordTrace]
  refine ⟨250902228257119706518074023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167268152171413137678716015 250902228257119706518074023)
  ·
    refine ⟨376353342385679559777111035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250902228257119706518074023 376353342385679559777111035)
    ·
      refine ⟨564530013578519339665666553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376353342385679559777111035 564530013578519339665666553)
      ·
        refine ⟨423397510183889504749249915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564530013578519339665666553 423397510183889504749249915)
        ·
          refine ⟨635096265275834257123874873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423397510183889504749249915 635096265275834257123874873)
          ·
            refine ⟨476322198956875692842906155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635096265275834257123874873 476322198956875692842906155)
            ·
              refine ⟨714483298435313539264359233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476322198956875692842906155 714483298435313539264359233)
              ·
                refine ⟨535862473826485154448269425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714483298435313539264359233 535862473826485154448269425)
                ·
                  refine ⟨401896855369863865836202069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535862473826485154448269425 401896855369863865836202069)
                  ·
                    refine ⟨4709728773865592177767993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 401896855369863865836202069 4709728773865592177767993)
                    ·
                      refine ⟨3532296580399194133325995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709728773865592177767993 3532296580399194133325995)
                      ·
                        rfl

theorem cell23_6879123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 8, 2].length) (baseStart_6879123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879123 prefixEnd_6879123 := by exact prefixLift 6879123
  have htrace : WordTrace (prefixWord ++ tailWord_6879123) baseStart_6879123 baseEnd_6879123 := by
    simpa [prefixWord, tailWord_6879123, baseEnd_6879123] using wordTrace_append hprefix tailTrace_6879123
  have hstable : (prefixWord ++ tailWord_6879123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879123).length < 2 ^ (prefixWord ++ tailWord_6879123).sum := by decide
  have hdescent : baseEnd_6879123 < baseStart_6879123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879127 : List Nat := [1, 1, 3, 3, 1, 4, 1, 3, 1, 3, 2]
def baseStart_6879127 : Nat := 118140960795 + 6879127 * 2 ^ 59
def prefixEnd_6879127 : Nat := 4983230072969 + 3 ^ 40 * 6879127 * 2
def baseEnd_6879127 : Nat := 3532298634321812117675977

theorem tailTrace_6879127 : CollatzResearch.WordTrace tailWord_6879127 prefixEnd_6879127 3532298634321812117675977 := by
  unfold tailWord_6879127
  simp only [CollatzResearch.WordTrace]
  refine ⟨250902374149105215201219635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167268249432736810134146423 250902374149105215201219635)
  ·
    refine ⟨376353561223657822801829453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250902374149105215201219635 376353561223657822801829453)
    ·
      refine ⟨141132585458871683550686045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376353561223657822801829453 141132585458871683550686045)
      ·
        refine ⟨52924719547076881331507267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141132585458871683550686045 52924719547076881331507267)
        ·
          refine ⟨79387079320615321997260901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52924719547076881331507267 79387079320615321997260901)
          ·
            refine ⟨14885077372615372874486419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79387079320615321997260901 14885077372615372874486419)
            ·
              refine ⟨22327616058923059311729629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14885077372615372874486419 22327616058923059311729629)
              ·
                refine ⟨8372856022096147241898611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22327616058923059311729629 8372856022096147241898611)
                ·
                  refine ⟨12559284033144220862847917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372856022096147241898611 12559284033144220862847917)
                  ·
                    refine ⟨4709731512429082823567969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12559284033144220862847917 4709731512429082823567969)
                    ·
                      refine ⟨3532298634321812117675977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709731512429082823567969 3532298634321812117675977)
                      ·
                        rfl

theorem cell23_6879127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_6879127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879127 prefixEnd_6879127 := by exact prefixLift 6879127
  have htrace : WordTrace (prefixWord ++ tailWord_6879127) baseStart_6879127 baseEnd_6879127 := by
    simpa [prefixWord, tailWord_6879127, baseEnd_6879127] using wordTrace_append hprefix tailTrace_6879127
  have hstable : (prefixWord ++ tailWord_6879127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879127).length < 2 ^ (prefixWord ++ tailWord_6879127).sum := by decide
  have hdescent : baseEnd_6879127 < baseStart_6879127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879133 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 2, 6]
def baseStart_6879133 : Nat := 118140960795 + 6879133 * 2 ^ 59
def prefixEnd_6879133 : Nat := 4983230072969 + 3 ^ 40 * 6879133 * 2
def baseEnd_6879133 : Nat := 1177433905068579698066983

theorem tailTrace_6879133 : CollatzResearch.WordTrace tailWord_6879133 prefixEnd_6879133 1177433905068579698066983 := by
  unfold tailWord_6879133
  simp only [CollatzResearch.WordTrace]
  refine ⟨250902592987083478225938053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167268395324722318817292035 250902592987083478225938053)
  ·
    refine ⟨47044236185078152167363385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250902592987083478225938053 47044236185078152167363385)
    ·
      refine ⟨35283177138808614125522539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47044236185078152167363385 35283177138808614125522539)
      ·
        refine ⟨52924765708212921188283809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35283177138808614125522539 52924765708212921188283809)
        ·
          refine ⟨39693574281159690891212857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52924765708212921188283809 39693574281159690891212857)
          ·
            refine ⟨29770180710869768168409643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39693574281159690891212857 29770180710869768168409643)
            ·
              refine ⟨44655271066304652252614465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29770180710869768168409643 44655271066304652252614465)
              ·
                refine ⟨33491453299728489189460849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44655271066304652252614465 33491453299728489189460849)
                ·
                  refine ⟨25118589974796366892095637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33491453299728489189460849 25118589974796366892095637)
                  ·
                    refine ⟨1177433905068579698066983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25118589974796366892095637 1177433905068579698066983)
                    ·
                      rfl

theorem cell23_6879133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_6879133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879133 prefixEnd_6879133 := by exact prefixLift 6879133
  have htrace : WordTrace (prefixWord ++ tailWord_6879133) baseStart_6879133 baseEnd_6879133 := by
    simpa [prefixWord, tailWord_6879133, baseEnd_6879133] using wordTrace_append hprefix tailTrace_6879133
  have hstable : (prefixWord ++ tailWord_6879133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879133).length < 2 ^ (prefixWord ++ tailWord_6879133).sum := by decide
  have hdescent : baseEnd_6879133 < baseStart_6879133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879157 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_6879157 : Nat := 118140960795 + 6879157 * 2 ^ 59
def prefixEnd_6879157 : Nat := 4983230072969 + 3 ^ 40 * 6879157 * 2
def baseEnd_6879157 : Nat := 3532314038741447000300839

theorem tailTrace_6879157 : CollatzResearch.WordTrace tailWord_6879157 prefixEnd_6879157 3532314038741447000300839 := by
  unfold tailWord_6879157
  simp only [CollatzResearch.WordTrace]
  refine ⟨250903468338996530324811725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167268978892664353549874483 250903468338996530324811725)
  ·
    refine ⟨94088800627123698871804397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250903468338996530324811725 94088800627123698871804397)
    ·
      refine ⟨35283300235171387076926649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94088800627123698871804397 35283300235171387076926649)
      ·
        refine ⟨26462475176378540307694987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35283300235171387076926649 26462475176378540307694987)
        ·
          refine ⟨39693712764567810461542481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26462475176378540307694987 39693712764567810461542481)
          ·
            refine ⟨29770284573425857846156861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39693712764567810461542481 29770284573425857846156861)
            ·
              refine ⟨11163856715034696692308823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29770284573425857846156861 11163856715034696692308823)
              ·
                refine ⟨16745785072552045038463235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163856715034696692308823 16745785072552045038463235)
                ·
                  refine ⟨25118677608828067557694853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16745785072552045038463235 25118677608828067557694853)
                  ·
                    refine ⟨4709752051655262667067785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25118677608828067557694853 4709752051655262667067785)
                    ·
                      refine ⟨3532314038741447000300839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709752051655262667067785 3532314038741447000300839)
                      ·
                        rfl

theorem cell23_6879157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_6879157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879157 prefixEnd_6879157 := by exact prefixLift 6879157
  have htrace : WordTrace (prefixWord ++ tailWord_6879157) baseStart_6879157 baseEnd_6879157 := by
    simpa [prefixWord, tailWord_6879157, baseEnd_6879157] using wordTrace_append hprefix tailTrace_6879157
  have hstable : (prefixWord ++ tailWord_6879157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879157).length < 2 ^ (prefixWord ++ tailWord_6879157).sum := by decide
  have hdescent : baseEnd_6879157 < baseStart_6879157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879173 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_6879173 : Nat := 118140960795 + 6879173 * 2 ^ 59
def prefixEnd_6879173 : Nat := 4983230072969 + 3 ^ 40 * 6879173 * 2
def baseEnd_6879173 : Nat := 3532322254431918937700765

theorem tailTrace_6879173 : CollatzResearch.WordTrace tailWord_6879173 prefixEnd_6879173 3532322254431918937700765 := by
  unfold tailWord_6879173
  simp only [CollatzResearch.WordTrace]
  refine ⟨250904051906938565057394173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167269367937959043371596115 250904051906938565057394173)
  ·
    refine ⟨94089019465101961896522815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250904051906938565057394173 94089019465101961896522815)
    ·
      refine ⟨141133529197652942844784223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94089019465101961896522815 141133529197652942844784223)
      ·
        refine ⟨211700293796479414267176335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141133529197652942844784223 211700293796479414267176335)
        ·
          refine ⟨317550440694719121400764503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211700293796479414267176335 317550440694719121400764503)
          ·
            refine ⟨476325661042078682101146755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317550440694719121400764503 476325661042078682101146755)
            ·
              refine ⟨714488491563118023151720133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476325661042078682101146755 714488491563118023151720133)
              ·
                refine ⟨133966592168084629340947525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714488491563118023151720133 133966592168084629340947525)
                ·
                  refine ⟨25118736031515868001427661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133966592168084629340947525 25118736031515868001427661)
                  ·
                    refine ⟨9419526011818450500535373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25118736031515868001427661 9419526011818450500535373)
                    ·
                      refine ⟨3532322254431918937700765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9419526011818450500535373 3532322254431918937700765)
                      ·
                        rfl

theorem cell23_6879173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_6879173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879173 prefixEnd_6879173 := by exact prefixLift 6879173
  have htrace : WordTrace (prefixWord ++ tailWord_6879173) baseStart_6879173 baseEnd_6879173 := by
    simpa [prefixWord, tailWord_6879173, baseEnd_6879173] using wordTrace_append hprefix tailTrace_6879173
  have hstable : (prefixWord ++ tailWord_6879173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879173).length < 2 ^ (prefixWord ++ tailWord_6879173).sum := by decide
  have hdescent : baseEnd_6879173 < baseStart_6879173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879197 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 7]
def baseStart_6879197 : Nat := 118140960795 + 6879197 * 2 ^ 59
def prefixEnd_6879197 : Nat := 4983230072969 + 3 ^ 40 * 6879197 * 2
def baseEnd_6879197 : Nat := 392481619774180760422295

theorem tailTrace_6879197 : CollatzResearch.WordTrace tailWord_6879197 prefixEnd_6879197 392481619774180760422295 := by
  unfold tailWord_6879197
  simp only [CollatzResearch.WordTrace]
  refine ⟨250904927258851617156267845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167269951505901078104178563 250904927258851617156267845)
  ·
    refine ⟨47044673861034678216800221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250904927258851617156267845 47044673861034678216800221)
    ·
      refine ⟨17641752697888004331300083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47044673861034678216800221 17641752697888004331300083)
      ·
        refine ⟨26462629046832006496950125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17641752697888004331300083 26462629046832006496950125)
        ·
          refine ⟨9923485892562002436356297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26462629046832006496950125 9923485892562002436356297)
          ·
            refine ⟨7442614419421501827267223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9923485892562002436356297 7442614419421501827267223)
            ·
              refine ⟨11163921629132252740900835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442614419421501827267223 11163921629132252740900835)
              ·
                refine ⟨16745882443698379111351253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11163921629132252740900835 16745882443698379111351253)
                ·
                  refine ⟨392481619774180760422295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16745882443698379111351253 392481619774180760422295)
                  ·
                    rfl

theorem cell23_6879197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_6879197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879197 prefixEnd_6879197 := by exact prefixLift 6879197
  have htrace : WordTrace (prefixWord ++ tailWord_6879197) baseStart_6879197 baseEnd_6879197 := by
    simpa [prefixWord, tailWord_6879197, baseEnd_6879197] using wordTrace_append hprefix tailTrace_6879197
  have hstable : (prefixWord ++ tailWord_6879197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879197).length < 2 ^ (prefixWord ++ tailWord_6879197).sum := by decide
  have hdescent : baseEnd_6879197 < baseStart_6879197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879203 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6879203 : Nat := 118140960795 + 6879203 * 2 ^ 59
def prefixEnd_6879203 : Nat := 4983230072969 + 3 ^ 40 * 6879203 * 2
def baseEnd_6879203 : Nat := 3532337658851553820325627

theorem tailTrace_6879203 : CollatzResearch.WordTrace tailWord_6879203 prefixEnd_6879203 3532337658851553820325627 := by
  unfold tailWord_6879203
  simp only [CollatzResearch.WordTrace]
  refine ⟨250905146096829880180986263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167270097397886586787324175 250905146096829880180986263)
  ·
    refine ⟨376357719145244820271479395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250905146096829880180986263 376357719145244820271479395)
    ·
      refine ⟨564536578717867230407219093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376357719145244820271479395 564536578717867230407219093)
      ·
        refine ⟨26462652127400026425338395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 564536578717867230407219093 26462652127400026425338395)
        ·
          refine ⟨39693978191100039638007593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26462652127400026425338395 39693978191100039638007593)
          ·
            refine ⟨29770483643325029728505695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39693978191100039638007593 29770483643325029728505695)
            ·
              refine ⟨44655725464987544592758543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29770483643325029728505695 44655725464987544592758543)
              ·
                refine ⟨66983588197481316889137815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44655725464987544592758543 66983588197481316889137815)
                ·
                  refine ⟨100475382296221975333706723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66983588197481316889137815 100475382296221975333706723)
                  ·
                    refine ⟨150713073444332963000560085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100475382296221975333706723 150713073444332963000560085)
                    ·
                      refine ⟨3532337658851553820325627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150713073444332963000560085 3532337658851553820325627)
                      ·
                        rfl

theorem cell23_6879203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6879203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879203 prefixEnd_6879203 := by exact prefixLift 6879203
  have htrace : WordTrace (prefixWord ++ tailWord_6879203) baseStart_6879203 baseEnd_6879203 := by
    simpa [prefixWord, tailWord_6879203, baseEnd_6879203] using wordTrace_append hprefix tailTrace_6879203
  have hstable : (prefixWord ++ tailWord_6879203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879203).length < 2 ^ (prefixWord ++ tailWord_6879203).sum := by decide
  have hdescent : baseEnd_6879203 < baseStart_6879203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879243 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6]
def baseStart_6879243 : Nat := 118140960795 + 6879243 * 2 ^ 59
def prefixEnd_6879243 : Nat := 4983230072969 + 3 ^ 40 * 6879243 * 2
def baseEnd_6879243 : Nat := 3532358198077733663825443

theorem tailTrace_6879243 : CollatzResearch.WordTrace tailWord_6879243 prefixEnd_6879243 3532358198077733663825443 := by
  unfold tailWord_6879243
  simp only [CollatzResearch.WordTrace]
  refine ⟨250906605016684967012442383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167271070011123311341628255 250906605016684967012442383)
  ·
    refine ⟨376359907525027450518663575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250906605016684967012442383 376359907525027450518663575)
    ·
      refine ⟨564539861287541175777995363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376359907525027450518663575 564539861287541175777995363)
      ·
        refine ⟨846809791931311763666993045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564539861287541175777995363 846809791931311763666993045)
        ·
          refine ⟨39694208996780238921890299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 846809791931311763666993045 39694208996780238921890299)
          ·
            refine ⟨59541313495170358382835449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39694208996780238921890299 59541313495170358382835449)
            ·
              refine ⟨44655985121377768787126587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59541313495170358382835449 44655985121377768787126587)
              ·
                refine ⟨66983977682066653180689881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44655985121377768787126587 66983977682066653180689881)
                ·
                  refine ⟨50237983261549989885517411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66983977682066653180689881 50237983261549989885517411)
                  ·
                    refine ⟨75356974892324984828276117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50237983261549989885517411 75356974892324984828276117)
                    ·
                      refine ⟨3532358198077733663825443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75356974892324984828276117 3532358198077733663825443)
                      ·
                        rfl

theorem cell23_6879243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 1, 6].length) (baseStart_6879243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879243 prefixEnd_6879243 := by exact prefixLift 6879243
  have htrace : WordTrace (prefixWord ++ tailWord_6879243) baseStart_6879243 baseEnd_6879243 := by
    simpa [prefixWord, tailWord_6879243, baseEnd_6879243] using wordTrace_append hprefix tailTrace_6879243
  have hstable : (prefixWord ++ tailWord_6879243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879243).length < 2 ^ (prefixWord ++ tailWord_6879243).sum := by decide
  have hdescent : baseEnd_6879243 < baseStart_6879243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879284 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_6879284 : Nat := 118140960795 + 6879284 * 2 ^ 59
def prefixEnd_6879284 : Nat := 4983230072969 + 3 ^ 40 * 6879284 * 2
def baseEnd_6879284 : Nat := 3532379250784568003412755

theorem tailTrace_6879284 : CollatzResearch.WordTrace tailWord_6879284 prefixEnd_6879284 3532379250784568003412755 := by
  unfold tailWord_6879284
  simp only [CollatzResearch.WordTrace]
  refine ⟨125454050204768215507342453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167272066939690954009789937 125454050204768215507342453)
  ·
    refine ⟨11761317206697020203813355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125454050204768215507342453 11761317206697020203813355)
    ·
      refine ⟨17641975810045530305720033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11761317206697020203813355 17641975810045530305720033)
      ·
        refine ⟨13231481857534147729290025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17641975810045530305720033 13231481857534147729290025)
        ·
          refine ⟨9923611393150610796967519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13231481857534147729290025 9923611393150610796967519)
          ·
            refine ⟨14885417089725916195451279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9923611393150610796967519 14885417089725916195451279)
            ·
              refine ⟨22328125634588874293176919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14885417089725916195451279 22328125634588874293176919)
              ·
                refine ⟨33492188451883311439765379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22328125634588874293176919 33492188451883311439765379)
                ·
                  refine ⟨50238282677824967159648069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33492188451883311439765379 50238282677824967159648069)
                  ·
                    refine ⟨9419678002092181342434013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50238282677824967159648069 9419678002092181342434013)
                    ·
                      refine ⟨3532379250784568003412755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9419678002092181342434013 3532379250784568003412755)
                      ·
                        rfl

theorem cell23_6879284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_6879284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879284 prefixEnd_6879284 := by exact prefixLift 6879284
  have htrace : WordTrace (prefixWord ++ tailWord_6879284) baseStart_6879284 baseEnd_6879284 := by
    simpa [prefixWord, tailWord_6879284, baseEnd_6879284] using wordTrace_append hprefix tailTrace_6879284
  have hstable : (prefixWord ++ tailWord_6879284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879284).length < 2 ^ (prefixWord ++ tailWord_6879284).sum := by decide
  have hdescent : baseEnd_6879284 < baseStart_6879284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879337 : List Nat := [1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 4]
def baseStart_6879337 : Nat := 118140960795 + 6879337 * 2 ^ 59
def prefixEnd_6879337 : Nat := 4983230072969 + 3 ^ 40 * 6879337 * 2
def baseEnd_6879337 : Nat := 3532406465259256296050011

theorem tailTrace_6879337 : CollatzResearch.WordTrace tailWord_6879337 prefixEnd_6879337 3532406465259256296050011 := by
  unfold tailWord_6879337
  simp only [CollatzResearch.WordTrace]
  refine ⟨250910033478344421066364265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167273355652229614044242843 250910033478344421066364265)
  ·
    refine ⟨188182525108758315799773199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250910033478344421066364265 188182525108758315799773199)
    ·
      refine ⟨282273787663137473699659799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188182525108758315799773199 282273787663137473699659799)
      ·
        refine ⟨423410681494706210549489699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282273787663137473699659799 423410681494706210549489699)
        ·
          refine ⟨635116022242059315824234549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423410681494706210549489699 635116022242059315824234549)
          ·
            refine ⟨59542127085193060858521989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 635116022242059315824234549 59542127085193060858521989)
            ·
              refine ⟨11164148828473698910972873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59542127085193060858521989 11164148828473698910972873)
              ·
                refine ⟨8373111621355274183229655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164148828473698910972873 8373111621355274183229655)
                ·
                  refine ⟨12559667432032911274844483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8373111621355274183229655 12559667432032911274844483)
                  ·
                    refine ⟨18839501148049366912266725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12559667432032911274844483 18839501148049366912266725)
                    ·
                      refine ⟨3532406465259256296050011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18839501148049366912266725 3532406465259256296050011)
                      ·
                        rfl

theorem cell23_6879337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 2, 1, 1, 4].length) (baseStart_6879337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879337 prefixEnd_6879337 := by exact prefixLift 6879337
  have htrace : WordTrace (prefixWord ++ tailWord_6879337) baseStart_6879337 baseEnd_6879337 := by
    simpa [prefixWord, tailWord_6879337, baseEnd_6879337] using wordTrace_append hprefix tailTrace_6879337
  have hstable : (prefixWord ++ tailWord_6879337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879337).length < 2 ^ (prefixWord ++ tailWord_6879337).sum := by decide
  have hdescent : baseEnd_6879337 < baseStart_6879337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879357 : List Nat := [1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_6879357 : Nat := 118140960795 + 6879357 * 2 ^ 59
def prefixEnd_6879357 : Nat := 4983230072969 + 3 ^ 40 * 6879357 * 2
def baseEnd_6879357 : Nat := 3532416734872346217799919

theorem tailTrace_6879357 : CollatzResearch.WordTrace tailWord_6879357 prefixEnd_6879357 3532416734872346217799919 := by
  unfold tailWord_6879357
  simp only [CollatzResearch.WordTrace]
  refine ⟨250910762938271964482092325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167273841958847976321394883 250910762938271964482092325)
  ·
    refine ⟨47045768050925993340392311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250910762938271964482092325 47045768050925993340392311)
    ·
      refine ⟨70568652076388990010588467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47045768050925993340392311 70568652076388990010588467)
      ·
        refine ⟨105852978114583485015882701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70568652076388990010588467 105852978114583485015882701)
        ·
          refine ⟨39694866792968806880956013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105852978114583485015882701 39694866792968806880956013)
          ·
            refine ⟨14885575047363302580358505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39694866792968806880956013 14885575047363302580358505)
            ·
              refine ⟨11164181285522476935268879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14885575047363302580358505 11164181285522476935268879)
              ·
                refine ⟨16746271928283715402903319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164181285522476935268879 16746271928283715402903319)
                ·
                  refine ⟨25119407892425573104354979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16746271928283715402903319 25119407892425573104354979)
                  ·
                    refine ⟨37679111838638359656532469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25119407892425573104354979 37679111838638359656532469)
                    ·
                      refine ⟨3532416734872346217799919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37679111838638359656532469 3532416734872346217799919)
                      ·
                        rfl

theorem cell23_6879357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_6879357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879357 prefixEnd_6879357 := by exact prefixLift 6879357
  have htrace : WordTrace (prefixWord ++ tailWord_6879357) baseStart_6879357 baseEnd_6879357 := by
    simpa [prefixWord, tailWord_6879357, baseEnd_6879357] using wordTrace_append hprefix tailTrace_6879357
  have hstable : (prefixWord ++ tailWord_6879357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879357).length < 2 ^ (prefixWord ++ tailWord_6879357).sum := by decide
  have hdescent : baseEnd_6879357 < baseStart_6879357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879391 : List Nat := [1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6879391 : Nat := 118140960795 + 6879391 * 2 ^ 59
def prefixEnd_6879391 : Nat := 4983230072969 + 3 ^ 40 * 6879391 * 2
def baseEnd_6879391 : Nat := 3532434193214599084774763

theorem tailTrace_6879391 : CollatzResearch.WordTrace tailWord_6879391 prefixEnd_6879391 3532434193214599084774763 := by
  unfold tailWord_6879391
  simp only [CollatzResearch.WordTrace]
  refine ⟨250912003020148788288830027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167274668680099192192553351 250912003020148788288830027)
  ·
    refine ⟨376368004530223182433245041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250912003020148788288830027 376368004530223182433245041)
    ·
      refine ⟨282276003397667386824933781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376368004530223182433245041 282276003397667386824933781)
      ·
        refine ⟨13231687659265658757418771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 282276003397667386824933781 13231687659265658757418771)
        ·
          refine ⟨19847531488898488136128157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13231687659265658757418771 19847531488898488136128157)
          ·
            refine ⟨7442824308336933051048059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19847531488898488136128157 7442824308336933051048059)
            ·
              refine ⟨11164236462505399576572089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442824308336933051048059 11164236462505399576572089)
              ·
                refine ⟨8373177346879049682429067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164236462505399576572089 8373177346879049682429067)
                ·
                  refine ⟨12559766020318574523643601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8373177346879049682429067 12559766020318574523643601)
                  ·
                    refine ⟨9419824515238930892732701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12559766020318574523643601 9419824515238930892732701)
                    ·
                      refine ⟨3532434193214599084774763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9419824515238930892732701 3532434193214599084774763)
                      ·
                        rfl

theorem cell23_6879391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6879391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879391 prefixEnd_6879391 := by exact prefixLift 6879391
  have htrace : WordTrace (prefixWord ++ tailWord_6879391) baseStart_6879391 baseEnd_6879391 := by
    simpa [prefixWord, tailWord_6879391, baseEnd_6879391] using wordTrace_append hprefix tailTrace_6879391
  have hstable : (prefixWord ++ tailWord_6879391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879391).length < 2 ^ (prefixWord ++ tailWord_6879391).sum := by decide
  have hdescent : baseEnd_6879391 < baseStart_6879391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879422 : List Nat := [4, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2]
def baseStart_6879422 : Nat := 118140960795 + 6879422 * 2 ^ 59
def prefixEnd_6879422 : Nat := 4983230072969 + 3 ^ 40 * 6879422 * 2
def baseEnd_6879422 : Nat := 3532450111114888463487121

theorem tailTrace_6879422 : CollatzResearch.WordTrace tailWord_6879422 prefixEnd_6879422 3532450111114888463487121 := by
  unfold tailWord_6879422
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364141710379560072901065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167275422455357653722139013 31364141710379560072901065)
  ·
    refine ⟨23523106282784670054675799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31364141710379560072901065 23523106282784670054675799)
    ·
      refine ⟨35284659424177005082013699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23523106282784670054675799 35284659424177005082013699)
      ·
        refine ⟨52926989136265507623020549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35284659424177005082013699 52926989136265507623020549)
        ·
          refine ⟨9923810463049782679316353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52926989136265507623020549 9923810463049782679316353)
          ·
            refine ⟨7442857847287337009487265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9923810463049782679316353 7442857847287337009487265)
            ·
              refine ⟨5582143385465502757115449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7442857847287337009487265 5582143385465502757115449)
              ·
                refine ⟨4186607539099127067836587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5582143385465502757115449 4186607539099127067836587)
                ·
                  refine ⟨6279911308648690601754881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186607539099127067836587 6279911308648690601754881)
                  ·
                    refine ⟨4709933481486517951316161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279911308648690601754881 4709933481486517951316161)
                    ·
                      refine ⟨3532450111114888463487121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709933481486517951316161 3532450111114888463487121)
                      ·
                        rfl

theorem cell23_6879422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_6879422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879422 prefixEnd_6879422 := by exact prefixLift 6879422
  have htrace : WordTrace (prefixWord ++ tailWord_6879422) baseStart_6879422 baseEnd_6879422 := by
    simpa [prefixWord, tailWord_6879422, baseEnd_6879422] using wordTrace_append hprefix tailTrace_6879422
  have hstable : (prefixWord ++ tailWord_6879422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879422).length < 2 ^ (prefixWord ++ tailWord_6879422).sum := by decide
  have hdescent : baseEnd_6879422 < baseStart_6879422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879450 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 9]
def baseStart_6879450 : Nat := 118140960795 + 6879450 * 2 ^ 59
def prefixEnd_6879450 : Nat := 4983230072969 + 3 ^ 40 * 6879450 * 2
def baseEnd_6879450 : Nat := 392496054285912705992999

theorem tailTrace_6879450 : CollatzResearch.WordTrace tailWord_6879450 prefixEnd_6879450 392496054285912705992999 := by
  unfold tailWord_6879450
  simp only [CollatzResearch.WordTrace]
  refine ⟨62728538731733760341306951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167276103284623360910151869 62728538731733760341306951)
  ·
    refine ⟨94092808097600640511960427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62728538731733760341306951 94092808097600640511960427)
    ·
      refine ⟨141139212146400960767940641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94092808097600640511960427 141139212146400960767940641)
      ·
        refine ⟨105854409109800720575955481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141139212146400960767940641 105854409109800720575955481)
        ·
          refine ⟨79390806832350540431966611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105854409109800720575955481 79390806832350540431966611)
          ·
            refine ⟨119086210248525810647949917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79390806832350540431966611 119086210248525810647949917)
            ·
              refine ⟨44657328843197178992981219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119086210248525810647949917 44657328843197178992981219)
              ·
                refine ⟨66985993264795768489471829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44657328843197178992981219 66985993264795768489471829)
                ·
                  refine ⟨392496054285912705992999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 66985993264795768489471829 392496054285912705992999)
                  ·
                    rfl

theorem cell23_6879450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 9].length) (baseStart_6879450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879450 prefixEnd_6879450 := by exact prefixLift 6879450
  have htrace : WordTrace (prefixWord ++ tailWord_6879450) baseStart_6879450 baseEnd_6879450 := by
    simpa [prefixWord, tailWord_6879450, baseEnd_6879450] using wordTrace_append hprefix tailTrace_6879450
  have hstable : (prefixWord ++ tailWord_6879450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879450).length < 2 ^ (prefixWord ++ tailWord_6879450).sum := by decide
  have hdescent : baseEnd_6879450 < baseStart_6879450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879460 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 1, 2, 7]
def baseStart_6879460 : Nat := 118140960795 + 6879460 * 2 ^ 59
def prefixEnd_6879460 : Nat := 4983230072969 + 3 ^ 40 * 6879460 * 2
def baseEnd_6879460 : Nat := 3532469623379759314811945

theorem tailTrace_6879460 : CollatzResearch.WordTrace tailWord_6879460 prefixEnd_6879460 3532469623379759314811945 := by
  unfold tailWord_6879460
  simp only [CollatzResearch.WordTrace]
  refine ⟨125457259828449406536545917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167276346437932542048727889 125457259828449406536545917)
  ·
    refine ⟨47046472435668527451204719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125457259828449406536545917 47046472435668527451204719)
    ·
      refine ⟨70569708653502791176807079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47046472435668527451204719 70569708653502791176807079)
      ·
        refine ⟨105854562980254186765210619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70569708653502791176807079 105854562980254186765210619)
        ·
          refine ⟨158781844470381280147815929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105854562980254186765210619 158781844470381280147815929)
          ·
            refine ⟨119086383352785960110861947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158781844470381280147815929 119086383352785960110861947)
            ·
              refine ⟨178629575029178940166292921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119086383352785960110861947 178629575029178940166292921)
              ·
                refine ⟨133972181271884205124719691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178629575029178940166292921 133972181271884205124719691)
                ·
                  refine ⟨200958271907826307687079537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133972181271884205124719691 200958271907826307687079537)
                  ·
                    refine ⟨150718703930869730765309653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 200958271907826307687079537 150718703930869730765309653)
                    ·
                      refine ⟨3532469623379759314811945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150718703930869730765309653 3532469623379759314811945)
                      ·
                        rfl

theorem cell23_6879460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_6879460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879460 prefixEnd_6879460 := by exact prefixLift 6879460
  have htrace : WordTrace (prefixWord ++ tailWord_6879460) baseStart_6879460 baseEnd_6879460 := by
    simpa [prefixWord, tailWord_6879460, baseEnd_6879460] using wordTrace_append hprefix tailTrace_6879460
  have hstable : (prefixWord ++ tailWord_6879460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879460).length < 2 ^ (prefixWord ++ tailWord_6879460).sum := by decide
  have hdescent : baseEnd_6879460 < baseStart_6879460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879478 : List Nat := [5, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2]
def baseStart_6879478 : Nat := 118140960795 + 6879478 * 2 ^ 59
def prefixEnd_6879478 : Nat := 4983230072969 + 3 ^ 40 * 6879478 * 2
def baseEnd_6879478 : Nat := 3532478866031540244386863

theorem tailTrace_6879478 : CollatzResearch.WordTrace tailWord_6879478 prefixEnd_6879478 3532478866031540244386863 := by
  unfold tailWord_6879478
  simp only [CollatzResearch.WordTrace]
  refine ⟨15682198510677100134202943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167276784113889068098164725 15682198510677100134202943)
  ·
    refine ⟨23523297766015650201304415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15682198510677100134202943 23523297766015650201304415)
    ·
      refine ⟨35284946649023475301956623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23523297766015650201304415 35284946649023475301956623)
      ·
        refine ⟨52927419973535212952934935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35284946649023475301956623 52927419973535212952934935)
        ·
          refine ⟨79391129960302819429402403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52927419973535212952934935 79391129960302819429402403)
          ·
            refine ⟨119086694940454229144103605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79391129960302819429402403 119086694940454229144103605)
            ·
              refine ⟨11164377650667583982259713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119086694940454229144103605 11164377650667583982259713)
              ·
                refine ⟨8373283238000687986694785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164377650667583982259713 8373283238000687986694785)
                ·
                  refine ⟨6279962428500515990021089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373283238000687986694785 6279962428500515990021089)
                  ·
                    refine ⟨4709971821375386992515817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6279962428500515990021089 4709971821375386992515817)
                    ·
                      refine ⟨3532478866031540244386863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709971821375386992515817 3532478866031540244386863)
                      ·
                        rfl

theorem cell23_6879478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_6879478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879478 prefixEnd_6879478 := by exact prefixLift 6879478
  have htrace : WordTrace (prefixWord ++ tailWord_6879478) baseStart_6879478 baseEnd_6879478 := by
    simpa [prefixWord, tailWord_6879478, baseEnd_6879478] using wordTrace_append hprefix tailTrace_6879478
  have hstable : (prefixWord ++ tailWord_6879478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879478).length < 2 ^ (prefixWord ++ tailWord_6879478).sum := by decide
  have hdescent : baseEnd_6879478 < baseStart_6879478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879484 : List Nat := [2, 2, 2, 1, 4, 1, 2, 4, 5]
def baseStart_6879484 : Nat := 118140960795 + 6879484 * 2 ^ 59
def prefixEnd_6879484 : Nat := 4983230072969 + 3 ^ 40 * 6879484 * 2
def baseEnd_6879484 : Nat := 392497994101718580101315

theorem tailTrace_6879484 : CollatzResearch.WordTrace tailWord_6879484 prefixEnd_6879484 392497994101718580101315 := by
  unfold tailWord_6879484
  simp only [CollatzResearch.WordTrace]
  refine ⟨125457697504405932585982753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167276930005874576781310337 125457697504405932585982753)
  ·
    refine ⟨94093273128304449439487065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125457697504405932585982753 94093273128304449439487065)
    ·
      refine ⟨70569954846228337079615299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94093273128304449439487065 70569954846228337079615299)
      ·
        refine ⟨105854932269342505619422949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70569954846228337079615299 105854932269342505619422949)
        ·
          refine ⟨19847799800501719803641803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105854932269342505619422949 19847799800501719803641803)
          ·
            refine ⟨29771699700752579705462705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19847799800501719803641803 29771699700752579705462705)
            ·
              refine ⟨22328774775564434779097029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29771699700752579705462705 22328774775564434779097029)
              ·
                refine ⟨4186645270418331521080693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22328774775564434779097029 4186645270418331521080693)
                ·
                  refine ⟨392497994101718580101315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186645270418331521080693 392497994101718580101315)
                  ·
                    rfl

theorem cell23_6879484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 5].length) (baseStart_6879484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879484 prefixEnd_6879484 := by exact prefixLift 6879484
  have htrace : WordTrace (prefixWord ++ tailWord_6879484) baseStart_6879484 baseEnd_6879484 := by
    simpa [prefixWord, tailWord_6879484, baseEnd_6879484] using wordTrace_append hprefix tailTrace_6879484
  have hstable : (prefixWord ++ tailWord_6879484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879484).length < 2 ^ (prefixWord ++ tailWord_6879484).sum := by decide
  have hdescent : baseEnd_6879484 < baseStart_6879484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879495 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6879495 : Nat := 118140960795 + 6879495 * 2 ^ 59
def prefixEnd_6879495 : Nat := 4983230072969 + 3 ^ 40 * 6879495 * 2
def baseEnd_6879495 : Nat := 3532487595202666677874285

theorem tailTrace_6879495 : CollatzResearch.WordTrace tailWord_6879495 prefixEnd_6879495 3532487595202666677874285 := by
  unfold tailWord_6879495
  simp only [CollatzResearch.WordTrace]
  refine ⟨250915796211772014050615939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167277197474514676033743959 250915796211772014050615939)
  ·
    refine ⟨376373694317658021075923909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250915796211772014050615939 376373694317658021075923909)
    ·
      refine ⟨70570067684560878951735733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376373694317658021075923909 70570067684560878951735733)
      ·
        refine ⟨6615943845427582401725225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70570067684560878951735733 6615943845427582401725225)
        ·
          refine ⟨4961957884070686801293919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615943845427582401725225 4961957884070686801293919)
          ·
            refine ⟨7442936826106030201940879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4961957884070686801293919 7442936826106030201940879)
            ·
              refine ⟨11164405239159045302911319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442936826106030201940879 11164405239159045302911319)
              ·
                refine ⟨16746607858738567954366979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164405239159045302911319 16746607858738567954366979)
                ·
                  refine ⟨25119911788107851931550469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16746607858738567954366979 25119911788107851931550469)
                  ·
                    refine ⟨4709983460270222237165713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25119911788107851931550469 4709983460270222237165713)
                    ·
                      refine ⟨3532487595202666677874285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4709983460270222237165713 3532487595202666677874285)
                      ·
                        rfl

theorem cell23_6879495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6879495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879495 prefixEnd_6879495 := by exact prefixLift 6879495
  have htrace : WordTrace (prefixWord ++ tailWord_6879495) baseStart_6879495 baseEnd_6879495 := by
    simpa [prefixWord, tailWord_6879495, baseEnd_6879495] using wordTrace_append hprefix tailTrace_6879495
  have hstable : (prefixWord ++ tailWord_6879495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879495).length < 2 ^ (prefixWord ++ tailWord_6879495).sum := by decide
  have hdescent : baseEnd_6879495 < baseStart_6879495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879518 : List Nat := [4, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_6879518 : Nat := 118140960795 + 6879518 * 2 ^ 59
def prefixEnd_6879518 : Nat := 4983230072969 + 3 ^ 40 * 6879518 * 2
def baseEnd_6879518 : Nat := 392499933917524454209631

theorem tailTrace_6879518 : CollatzResearch.WordTrace tailWord_6879518 prefixEnd_6879518 392499933917524454209631 := by
  unfold tailWord_6879518
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364579386336086122337901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167277756727125792652468805 31364579386336086122337901)
  ·
    refine ⟨11761717269876032295876713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31364579386336086122337901 11761717269876032295876713)
    ·
      refine ⟨8821287952407024221907535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11761717269876032295876713 8821287952407024221907535)
      ·
        refine ⟨13231931928610536332861303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821287952407024221907535 13231931928610536332861303)
        ·
          refine ⟨19847897892915804499291955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13231931928610536332861303 19847897892915804499291955)
          ·
            refine ⟨29771846839373706748937933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19847897892915804499291955 29771846839373706748937933)
            ·
              refine ⟨11164442564765140030851725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29771846839373706748937933 11164442564765140030851725)
              ·
                refine ⟨4186665961786927511569397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11164442564765140030851725 4186665961786927511569397)
                ·
                  refine ⟨392499933917524454209631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4186665961786927511569397 392499933917524454209631)
                  ·
                    rfl

theorem cell23_6879518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_6879518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879518 prefixEnd_6879518 := by exact prefixLift 6879518
  have htrace : WordTrace (prefixWord ++ tailWord_6879518) baseStart_6879518 baseEnd_6879518 := by
    simpa [prefixWord, tailWord_6879518, baseEnd_6879518] using wordTrace_append hprefix tailTrace_6879518
  have hstable : (prefixWord ++ tailWord_6879518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879518).length < 2 ^ (prefixWord ++ tailWord_6879518).sum := by decide
  have hdescent : baseEnd_6879518 < baseStart_6879518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879544 : List Nat := [2, 1, 2, 1, 3, 1, 5, 1, 3, 4]
def baseStart_6879544 : Nat := 118140960795 + 6879544 * 2 ^ 59
def prefixEnd_6879544 : Nat := 4983230072969 + 3 ^ 40 * 6879544 * 2
def baseEnd_6879544 : Nat := 1177504251918245662053853

theorem tailTrace_6879544 : CollatzResearch.WordTrace tailWord_6879544 prefixEnd_6879544 1177504251918245662053853 := by
  unfold tailWord_6879544
  simp only [CollatzResearch.WordTrace]
  refine ⟨125458791694297247709574843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167278388925729663612766457 125458791694297247709574843)
  ·
    refine ⟨188188187541445871564362265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125458791694297247709574843 188188187541445871564362265)
    ·
      refine ⟨141141140656084403673271699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188188187541445871564362265 141141140656084403673271699)
      ·
        refine ⟨211711710984126605509907549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141141140656084403673271699 211711710984126605509907549)
        ·
          refine ⟨79391891619047477066215331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211711710984126605509907549 79391891619047477066215331)
          ·
            refine ⟨119087837428571215599322997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79391891619047477066215331 119087837428571215599322997)
            ·
              refine ⟨11164484758928551462436531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119087837428571215599322997 11164484758928551462436531)
              ·
                refine ⟨16746727138392827193654797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164484758928551462436531 16746727138392827193654797)
                ·
                  refine ⟨6280022676897310197620549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16746727138392827193654797 6280022676897310197620549)
                  ·
                    refine ⟨1177504251918245662053853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280022676897310197620549 1177504251918245662053853)
                    ·
                      rfl

theorem cell23_6879544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 4].length) (baseStart_6879544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879544 prefixEnd_6879544 := by exact prefixLift 6879544
  have htrace : WordTrace (prefixWord ++ tailWord_6879544) baseStart_6879544 baseEnd_6879544 := by
    simpa [prefixWord, tailWord_6879544, baseEnd_6879544] using wordTrace_append hprefix tailTrace_6879544
  have hstable : (prefixWord ++ tailWord_6879544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879544).length < 2 ^ (prefixWord ++ tailWord_6879544).sum := by decide
  have hdescent : baseEnd_6879544 < baseStart_6879544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879624 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6879624 : Nat := 118140960795 + 6879624 * 2 ^ 59
def prefixEnd_6879624 : Nat := 4983230072969 + 3 ^ 40 * 6879624 * 2
def baseEnd_6879624 : Nat := 3532553834207096673161191

theorem tailTrace_6879624 : CollatzResearch.WordTrace tailWord_6879624 prefixEnd_6879624 3532553834207096673161191 := by
  unfold tailWord_6879624
  simp only [CollatzResearch.WordTrace]
  refine ⟨125460250614152334541030963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167280334152203112721374617 125460250614152334541030963)
  ·
    refine ⟨188190375921228501811546445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125460250614152334541030963 188190375921228501811546445)
    ·
      refine ⟨70571390970460688179329917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188190375921228501811546445 70571390970460688179329917)
      ·
        refine ⟨26464271613922758067248719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70571390970460688179329917 26464271613922758067248719)
        ·
          refine ⟨39696407420884137100873079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26464271613922758067248719 39696407420884137100873079)
          ·
            refine ⟨59544611131326205651309619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39696407420884137100873079 59544611131326205651309619)
            ·
              refine ⟨89316916696989308476964429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59544611131326205651309619 89316916696989308476964429)
              ·
                refine ⟨33493843761370990678861661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89316916696989308476964429 33493843761370990678861661)
                ·
                  refine ⟨12560191410514121504573123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33493843761370990678861661 12560191410514121504573123)
                  ·
                    refine ⟨18840287115771182256859685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12560191410514121504573123 18840287115771182256859685)
                    ·
                      refine ⟨3532553834207096673161191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18840287115771182256859685 3532553834207096673161191)
                      ·
                        rfl

theorem cell23_6879624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6879624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879624 prefixEnd_6879624 := by exact prefixLift 6879624
  have htrace : WordTrace (prefixWord ++ tailWord_6879624) baseStart_6879624 baseEnd_6879624 := by
    simpa [prefixWord, tailWord_6879624, baseEnd_6879624] using wordTrace_append hprefix tailTrace_6879624
  have hstable : (prefixWord ++ tailWord_6879624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879624).length < 2 ^ (prefixWord ++ tailWord_6879624).sum := by decide
  have hdescent : baseEnd_6879624 < baseStart_6879624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879628 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 2, 3, 2]
def baseStart_6879628 : Nat := 118140960795 + 6879628 * 2 ^ 59
def prefixEnd_6879628 : Nat := 4983230072969 + 3 ^ 40 * 6879628 * 2
def baseEnd_6879628 : Nat := 3532555888129714657511173

theorem tailTrace_6879628 : CollatzResearch.WordTrace tailWord_6879628 prefixEnd_6879628 3532555888129714657511173 := by
  unfold tailWord_6879628
  simp only [CollatzResearch.WordTrace]
  refine ⟨125460323560145088882603769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167280431413526785176805025 125460323560145088882603769)
  ·
    refine ⟨94095242670108816661952827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125460323560145088882603769 94095242670108816661952827)
    ·
      refine ⟨141142864005163224992929241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94095242670108816661952827 141142864005163224992929241)
      ·
        refine ⟨105857148003872418744696931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141142864005163224992929241 105857148003872418744696931)
        ·
          refine ⟨158785722005808628117045397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105857148003872418744696931 158785722005808628117045397)
          ·
            refine ⟨7443080719022279442986503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158785722005808628117045397 7443080719022279442986503)
            ·
              refine ⟨11164621078533419164479755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443080719022279442986503 11164621078533419164479755)
              ·
                refine ⟨16746931617800128746719633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164621078533419164479755 16746931617800128746719633)
                ·
                  refine ⟨12560198713350096560039725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16746931617800128746719633 12560198713350096560039725)
                  ·
                    refine ⟨4710074517506286210014897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12560198713350096560039725 4710074517506286210014897)
                    ·
                      refine ⟨3532555888129714657511173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710074517506286210014897 3532555888129714657511173)
                      ·
                        rfl

theorem cell23_6879628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_6879628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879628 prefixEnd_6879628 := by exact prefixLift 6879628
  have htrace : WordTrace (prefixWord ++ tailWord_6879628) baseStart_6879628 baseEnd_6879628 := by
    simpa [prefixWord, tailWord_6879628, baseEnd_6879628] using wordTrace_append hprefix tailTrace_6879628
  have hstable : (prefixWord ++ tailWord_6879628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879628).length < 2 ^ (prefixWord ++ tailWord_6879628).sum := by decide
  have hdescent : baseEnd_6879628 < baseStart_6879628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879637 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6879637 : Nat := 118140960795 + 6879637 * 2 ^ 59
def prefixEnd_6879637 : Nat := 4983230072969 + 3 ^ 40 * 6879637 * 2
def baseEnd_6879637 : Nat := 3532560509455605122298631

theorem tailTrace_6879637 : CollatzResearch.WordTrace tailWord_6879637 prefixEnd_6879637 3532560509455605122298631 := by
  unfold tailWord_6879637
  simp only [CollatzResearch.WordTrace]
  refine ⟨250920975377257572302285165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167280650251505048201523443 250920975377257572302285165)
  ·
    refine ⟨94095365766471589613356937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250920975377257572302285165 94095365766471589613356937)
    ·
      refine ⟨70571524324853692210017703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94095365766471589613356937 70571524324853692210017703)
      ·
        refine ⟨105857286487280538315026555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70571524324853692210017703 105857286487280538315026555)
        ·
          refine ⟨158785929730920807472539833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105857286487280538315026555 158785929730920807472539833)
          ·
            refine ⟨119089447298190605604404875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158785929730920807472539833 119089447298190605604404875)
            ·
              refine ⟨178634170947285908406607313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119089447298190605604404875 178634170947285908406607313)
              ·
                refine ⟨133975628210464431304955485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178634170947285908406607313 133975628210464431304955485)
                ·
                  refine ⟨50240860578924161739358307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133975628210464431304955485 50240860578924161739358307)
                  ·
                    refine ⟨75361290868386242609037461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50240860578924161739358307 75361290868386242609037461)
                    ·
                      refine ⟨3532560509455605122298631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75361290868386242609037461 3532560509455605122298631)
                      ·
                        rfl

theorem cell23_6879637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6879637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879637 prefixEnd_6879637 := by exact prefixLift 6879637
  have htrace : WordTrace (prefixWord ++ tailWord_6879637) baseStart_6879637 baseEnd_6879637 := by
    simpa [prefixWord, tailWord_6879637, baseEnd_6879637] using wordTrace_append hprefix tailTrace_6879637
  have hstable : (prefixWord ++ tailWord_6879637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879637).length < 2 ^ (prefixWord ++ tailWord_6879637).sum := by decide
  have hdescent : baseEnd_6879637 < baseStart_6879637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879641 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 5, 2, 2]
def baseStart_6879641 : Nat := 118140960795 + 6879641 * 2 ^ 59
def prefixEnd_6879641 : Nat := 4983230072969 + 3 ^ 40 * 6879641 * 2
def baseEnd_6879641 : Nat := 3532562563378223106648613

theorem tailTrace_6879641 : CollatzResearch.WordTrace tailWord_6879641 prefixEnd_6879641 3532562563378223106648613 := by
  unfold tailWord_6879641
  simp only [CollatzResearch.WordTrace]
  refine ⟨250921121269243080985430777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167280747512828720656953851 250921121269243080985430777)
  ·
    refine ⟨188190840951932310739073083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250921121269243080985430777 188190840951932310739073083)
    ·
      refine ⟨282286261427898466108609625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188190840951932310739073083 282286261427898466108609625)
      ·
        refine ⟨211714696070923849581457219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282286261427898466108609625 211714696070923849581457219)
        ·
          refine ⟨317572044106385774372185829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211714696070923849581457219 317572044106385774372185829)
          ·
            refine ⟨59544758269947332694784843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317572044106385774372185829 59544758269947332694784843)
            ·
              refine ⟨89317137404920999042177265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59544758269947332694784843 89317137404920999042177265)
              ·
                refine ⟨66987853053690749281632949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89317137404920999042177265 66987853053690749281632949)
                ·
                  refine ⟨6280111223783507745153089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66987853053690749281632949 6280111223783507745153089)
                  ·
                    refine ⟨4710083417837630808864817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6280111223783507745153089 4710083417837630808864817)
                    ·
                      refine ⟨3532562563378223106648613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710083417837630808864817 3532562563378223106648613)
                      ·
                        rfl

theorem cell23_6879641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 2, 2].length) (baseStart_6879641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879641 prefixEnd_6879641 := by exact prefixLift 6879641
  have htrace : WordTrace (prefixWord ++ tailWord_6879641) baseStart_6879641 baseEnd_6879641 := by
    simpa [prefixWord, tailWord_6879641, baseEnd_6879641] using wordTrace_append hprefix tailTrace_6879641
  have hstable : (prefixWord ++ tailWord_6879641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879641).length < 2 ^ (prefixWord ++ tailWord_6879641).sum := by decide
  have hdescent : baseEnd_6879641 < baseStart_6879641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879647 : List Nat := [1, 1, 2, 5, 1, 1, 12]
def baseStart_6879647 : Nat := 118140960795 + 6879647 * 2 ^ 59
def prefixEnd_6879647 : Nat := 4983230072969 + 3 ^ 40 * 6879647 * 2
def baseEnd_6879647 : Nat := 43611921534100618310785

theorem tailTrace_6879647 : CollatzResearch.WordTrace tailWord_6879647 prefixEnd_6879647 43611921534100618310785 := by
  unfold tailWord_6879647
  simp only [CollatzResearch.WordTrace]
  refine ⟨250921340107221344010149195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167280893404814229340099463 250921340107221344010149195)
  ·
    refine ⟨376382010160832016015223793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250921340107221344010149195 376382010160832016015223793)
    ·
      refine ⟨282286507620624012011417845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376382010160832016015223793 282286507620624012011417845)
      ·
        refine ⟨26464360089433501126070423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 282286507620624012011417845 26464360089433501126070423)
        ·
          refine ⟨39696540134150251689105635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26464360089433501126070423 39696540134150251689105635)
          ·
            refine ⟨59544810201225377533658453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39696540134150251689105635 59544810201225377533658453)
            ·
              refine ⟨43611921534100618310785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 59544810201225377533658453 43611921534100618310785)
              ·
                rfl

theorem cell23_6879647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 12].length) (baseStart_6879647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879647 prefixEnd_6879647 := by exact prefixLift 6879647
  have htrace : WordTrace (prefixWord ++ tailWord_6879647) baseStart_6879647 baseEnd_6879647 := by
    simpa [prefixWord, tailWord_6879647, baseEnd_6879647] using wordTrace_append hprefix tailTrace_6879647
  have hstable : (prefixWord ++ tailWord_6879647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879647).length < 2 ^ (prefixWord ++ tailWord_6879647).sum := by decide
  have hdescent : baseEnd_6879647 < baseStart_6879647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879651 : List Nat := [1, 1, 1, 4, 1, 4, 3, 2, 2, 4]
def baseStart_6879651 : Nat := 118140960795 + 6879651 * 2 ^ 59
def prefixEnd_6879651 : Nat := 4983230072969 + 3 ^ 40 * 6879651 * 2
def baseEnd_6879651 : Nat := 1177522566061589355841189

theorem tailTrace_6879651 : CollatzResearch.WordTrace tailWord_6879651 prefixEnd_6879651 1177522566061589355841189 := by
  unfold tailWord_6879651
  simp only [CollatzResearch.WordTrace]
  refine ⟨250921485999206852693294807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167280990666137901795529871 250921485999206852693294807)
  ·
    refine ⟨376382228998810279039942211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250921485999206852693294807 376382228998810279039942211)
    ·
      refine ⟨564573343498215418559913317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376382228998810279039942211 564573343498215418559913317)
      ·
        refine ⟨105857501905915390979983747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 564573343498215418559913317 105857501905915390979983747)
        ·
          refine ⟨158786252858873086469975621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105857501905915390979983747 158786252858873086469975621)
          ·
            refine ⟨29772422411038703713120429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158786252858873086469975621 29772422411038703713120429)
            ·
              refine ⟨11164658404139513892420161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29772422411038703713120429 11164658404139513892420161)
              ·
                refine ⟨8373493803104635419315121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164658404139513892420161 8373493803104635419315121)
                ·
                  refine ⟨6280120352328476564486341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373493803104635419315121 6280120352328476564486341)
                  ·
                    refine ⟨1177522566061589355841189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280120352328476564486341 1177522566061589355841189)
                    ·
                      rfl

theorem cell23_6879651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 4].length) (baseStart_6879651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879651 prefixEnd_6879651 := by exact prefixLift 6879651
  have htrace : WordTrace (prefixWord ++ tailWord_6879651) baseStart_6879651 baseEnd_6879651 := by
    simpa [prefixWord, tailWord_6879651, baseEnd_6879651] using wordTrace_append hprefix tailTrace_6879651
  have hstable : (prefixWord ++ tailWord_6879651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879651).length < 2 ^ (prefixWord ++ tailWord_6879651).sum := by decide
  have hdescent : baseEnd_6879651 < baseStart_6879651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879671 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_6879671 : Nat := 118140960795 + 6879671 * 2 ^ 59
def prefixEnd_6879671 : Nat := 4983230072969 + 3 ^ 40 * 6879671 * 2
def baseEnd_6879671 : Nat := 3532577967797857989273475

theorem tailTrace_6879671 : CollatzResearch.WordTrace tailWord_6879671 prefixEnd_6879671 3532577967797857989273475 := by
  unfold tailWord_6879671
  simp only [CollatzResearch.WordTrace]
  refine ⟨250922215459134396109022867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167281476972756264072681911 250922215459134396109022867)
  ·
    refine ⟨376383323188701594163534301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250922215459134396109022867 376383323188701594163534301)
    ·
      refine ⟨141143746195763097811325363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376383323188701594163534301 141143746195763097811325363)
      ·
        refine ⟨211715619293644646716988045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141143746195763097811325363 211715619293644646716988045)
        ·
          refine ⟨79393357235116742518870517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211715619293644646716988045 79393357235116742518870517)
          ·
            refine ⟨7443127240792194611144111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79393357235116742518870517 7443127240792194611144111)
            ·
              refine ⟨11164690861188291916716167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443127240792194611144111 11164690861188291916716167)
              ·
                refine ⟨16747036291782437875074251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11164690861188291916716167 16747036291782437875074251)
                ·
                  refine ⟨25120554437673656812611377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16747036291782437875074251 25120554437673656812611377)
                  ·
                    refine ⟨18840415828255242609458533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25120554437673656812611377 18840415828255242609458533)
                    ·
                      refine ⟨3532577967797857989273475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18840415828255242609458533 3532577967797857989273475)
                      ·
                        rfl

theorem cell23_6879671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_6879671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879671 prefixEnd_6879671 := by exact prefixLift 6879671
  have htrace : WordTrace (prefixWord ++ tailWord_6879671) baseStart_6879671 baseEnd_6879671 := by
    simpa [prefixWord, tailWord_6879671, baseEnd_6879671] using wordTrace_append hprefix tailTrace_6879671
  have hstable : (prefixWord ++ tailWord_6879671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879671).length < 2 ^ (prefixWord ++ tailWord_6879671).sum := by decide
  have hdescent : baseEnd_6879671 < baseStart_6879671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879697 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_6879697 : Nat := 118140960795 + 6879697 * 2 ^ 59
def prefixEnd_6879697 : Nat := 4983230072969 + 3 ^ 40 * 6879697 * 2
def baseEnd_6879697 : Nat := 3532591318294874887548355

theorem tailTrace_6879697 : CollatzResearch.WordTrace tailWord_6879697 prefixEnd_6879697 3532591318294874887548355 := by
  unfold tailWord_6879697
  simp only [CollatzResearch.WordTrace]
  refine ⟨250923163757040202549469345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167282109171360135032979563 250923163757040202549469345)
  ·
    refine ⟨188192372817780151912102009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250923163757040202549469345 188192372817780151912102009)
    ·
      refine ⟨141144279613335113934076507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188192372817780151912102009 141144279613335113934076507)
      ·
        refine ⟨211716419420002670901114761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141144279613335113934076507 211716419420002670901114761)
        ·
          refine ⟨158787314565002003175836071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211716419420002670901114761 158787314565002003175836071)
          ·
            refine ⟨238180971847503004763754107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158787314565002003175836071 238180971847503004763754107)
            ·
              refine ⟨357271457771254507145631161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238180971847503004763754107 357271457771254507145631161)
              ·
                refine ⟨267953593328440880359223371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357271457771254507145631161 267953593328440880359223371)
                ·
                  refine ⟨401930389992661320538835057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 267953593328440880359223371 401930389992661320538835057)
                  ·
                    refine ⟨301447792494495990404126293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 401930389992661320538835057 301447792494495990404126293)
                    ·
                      refine ⟨3532591318294874887548355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 301447792494495990404126293 3532591318294874887548355)
                      ·
                        rfl

theorem cell23_6879697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_6879697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879697 prefixEnd_6879697 := by exact prefixLift 6879697
  have htrace : WordTrace (prefixWord ++ tailWord_6879697) baseStart_6879697 baseEnd_6879697 := by
    simpa [prefixWord, tailWord_6879697, baseEnd_6879697] using wordTrace_append hprefix tailTrace_6879697
  have hstable : (prefixWord ++ tailWord_6879697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879697).length < 2 ^ (prefixWord ++ tailWord_6879697).sum := by decide
  have hdescent : baseEnd_6879697 < baseStart_6879697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879698 : List Nat := [3, 2, 2, 4, 2, 1, 9]
def baseStart_6879698 : Nat := 118140960795 + 6879698 * 2 ^ 59
def prefixEnd_6879698 : Nat := 4983230072969 + 3 ^ 40 * 6879698 * 2
def baseEnd_6879698 : Nat := 43612244836734930662171

theorem tailTrace_6879698 : CollatzResearch.WordTrace tailWord_6879698 prefixEnd_6879698 43612244836734930662171 := by
  unfold tailWord_6879698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62730800057509144930063937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167282133486691053146837165 62730800057509144930063937)
  ·
    refine ⟨47048100043131858697547953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62730800057509144930063937 47048100043131858697547953)
    ·
      refine ⟨35286075032348894023160965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47048100043131858697547953 35286075032348894023160965)
      ·
        refine ⟨6616139068565417629342681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35286075032348894023160965 6616139068565417629342681)
        ·
          refine ⟨4962104301424063222007011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6616139068565417629342681 4962104301424063222007011)
          ·
            refine ⟨7443156452136094833010517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962104301424063222007011 7443156452136094833010517)
            ·
              refine ⟨43612244836734930662171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7443156452136094833010517 43612244836734930662171)
              ·
                rfl

theorem cell23_6879698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 9].length) (baseStart_6879698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879698 prefixEnd_6879698 := by exact prefixLift 6879698
  have htrace : WordTrace (prefixWord ++ tailWord_6879698) baseStart_6879698 baseEnd_6879698 := by
    simpa [prefixWord, tailWord_6879698, baseEnd_6879698] using wordTrace_append hprefix tailTrace_6879698
  have hstable : (prefixWord ++ tailWord_6879698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879698).length < 2 ^ (prefixWord ++ tailWord_6879698).sum := by decide
  have hdescent : baseEnd_6879698 < baseStart_6879698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879725 : List Nat := [1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 3]
def baseStart_6879725 : Nat := 118140960795 + 6879725 * 2 ^ 59
def prefixEnd_6879725 : Nat := 4983230072969 + 3 ^ 40 * 6879725 * 2
def baseEnd_6879725 : Nat := 3532605695753200777998227

theorem tailTrace_6879725 : CollatzResearch.WordTrace tailWord_6879725 prefixEnd_6879725 3532605695753200777998227 := by
  unfold tailWord_6879725
  simp only [CollatzResearch.WordTrace]
  refine ⟨250924185000938763331488629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167282790000625842220992419 250924185000938763331488629)
  ·
    refine ⟨23524142343838009062327059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250924185000938763331488629 23524142343838009062327059)
    ·
      refine ⟨35286213515757013593490589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23524142343838009062327059 35286213515757013593490589)
      ·
        refine ⟨13232330068408880097558971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35286213515757013593490589 13232330068408880097558971)
        ·
          refine ⟨19848495102613320146338457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232330068408880097558971 19848495102613320146338457)
          ·
            refine ⟨14886371326959990109753843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19848495102613320146338457 14886371326959990109753843)
            ·
              refine ⟨22329556990439985164630765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14886371326959990109753843 22329556990439985164630765)
              ·
                refine ⟨8373583871414994436736537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22329556990439985164630765 8373583871414994436736537)
                ·
                  refine ⟨6280187903561245827552403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373583871414994436736537 6280187903561245827552403)
                  ·
                    refine ⟨9420281855341868741328605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280187903561245827552403 9420281855341868741328605)
                    ·
                      refine ⟨3532605695753200777998227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9420281855341868741328605 3532605695753200777998227)
                      ·
                        rfl

theorem cell23_6879725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_6879725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879725 prefixEnd_6879725 := by exact prefixLift 6879725
  have htrace : WordTrace (prefixWord ++ tailWord_6879725) baseStart_6879725 baseEnd_6879725 := by
    simpa [prefixWord, tailWord_6879725, baseEnd_6879725] using wordTrace_append hprefix tailTrace_6879725
  have hstable : (prefixWord ++ tailWord_6879725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879725).length < 2 ^ (prefixWord ++ tailWord_6879725).sum := by decide
  have hdescent : baseEnd_6879725 < baseStart_6879725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879731 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 1, 4, 2]
def baseStart_6879731 : Nat := 118140960795 + 6879731 * 2 ^ 59
def prefixEnd_6879731 : Nat := 4983230072969 + 3 ^ 40 * 6879731 * 2
def baseEnd_6879731 : Nat := 3532608776637127754523199

theorem tailTrace_6879731 : CollatzResearch.WordTrace tailWord_6879731 prefixEnd_6879731 3532608776637127754523199 := by
  unfold tailWord_6879731
  simp only [CollatzResearch.WordTrace]
  refine ⟨250924403838917026356207047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167282935892611350904138031 250924403838917026356207047)
  ·
    refine ⟨376386605758375539534310571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250924403838917026356207047 376386605758375539534310571)
    ·
      refine ⟨564579908637563309301465857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376386605758375539534310571 564579908637563309301465857)
      ·
        refine ⟨423434931478172481976099393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564579908637563309301465857 423434931478172481976099393)
        ·
          refine ⟨317576198608629361482074545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423434931478172481976099393 317576198608629361482074545)
          ·
            refine ⟨238182148956472021111555909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317576198608629361482074545 238182148956472021111555909)
            ·
              refine ⟨44659152929338503958416733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238182148956472021111555909 44659152929338503958416733)
              ·
                refine ⟨16747182348501938984406275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44659152929338503958416733 16747182348501938984406275)
                ·
                  refine ⟨25120773522752908476609413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16747182348501938984406275 25120773522752908476609413)
                  ·
                    refine ⟨4710145035516170339364265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25120773522752908476609413 4710145035516170339364265)
                    ·
                      refine ⟨3532608776637127754523199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710145035516170339364265 3532608776637127754523199)
                      ·
                        rfl

theorem cell23_6879731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 4, 2].length) (baseStart_6879731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879731 prefixEnd_6879731 := by exact prefixLift 6879731
  have htrace : WordTrace (prefixWord ++ tailWord_6879731) baseStart_6879731 baseEnd_6879731 := by
    simpa [prefixWord, tailWord_6879731, baseEnd_6879731] using wordTrace_append hprefix tailTrace_6879731
  have hstable : (prefixWord ++ tailWord_6879731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879731).length < 2 ^ (prefixWord ++ tailWord_6879731).sum := by decide
  have hdescent : baseEnd_6879731 < baseStart_6879731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879748 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6879748 : Nat := 118140960795 + 6879748 * 2 ^ 59
def prefixEnd_6879748 : Nat := 4983230072969 + 3 ^ 40 * 6879748 * 2
def baseEnd_6879748 : Nat := 3532617505808254188010621

theorem tailTrace_6879748 : CollatzResearch.WordTrace tailWord_6879748 prefixEnd_6879748 3532617505808254188010621 := by
  unfold tailWord_6879748
  simp only [CollatzResearch.WordTrace]
  refine ⟨125462511939927719129787949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167283349253236958839717265 125462511939927719129787949)
  ·
    refine ⟨47048441977472894673670481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125462511939927719129787949 47048441977472894673670481)
    ·
      refine ⟨35286331483104671005252861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47048441977472894673670481 35286331483104671005252861)
      ·
        refine ⟨13232374306164251626969823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35286331483104671005252861 13232374306164251626969823)
        ·
          refine ⟨19848561459246377440454735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232374306164251626969823 19848561459246377440454735)
          ·
            refine ⟨29772842188869566160682103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19848561459246377440454735 29772842188869566160682103)
            ·
              refine ⟨44659263283304349241023155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29772842188869566160682103 44659263283304349241023155)
              ·
                refine ⟨66988894924956523861534733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44659263283304349241023155 66988894924956523861534733)
                ·
                  refine ⟨25120835596858696448075525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66988894924956523861534733 25120835596858696448075525)
                  ·
                    refine ⟨4710156674411005584014161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25120835596858696448075525 4710156674411005584014161)
                    ·
                      refine ⟨3532617505808254188010621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710156674411005584014161 3532617505808254188010621)
                      ·
                        rfl

theorem cell23_6879748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6879748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879748 prefixEnd_6879748 := by exact prefixLift 6879748
  have htrace : WordTrace (prefixWord ++ tailWord_6879748) baseStart_6879748 baseEnd_6879748 := by
    simpa [prefixWord, tailWord_6879748, baseEnd_6879748] using wordTrace_append hprefix tailTrace_6879748
  have hstable : (prefixWord ++ tailWord_6879748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879748).length < 2 ^ (prefixWord ++ tailWord_6879748).sum := by decide
  have hdescent : baseEnd_6879748 < baseStart_6879748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879765 : List Nat := [1, 3, 2, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_6879765 : Nat := 118140960795 + 6879765 * 2 ^ 59
def prefixEnd_6879765 : Nat := 4983230072969 + 3 ^ 40 * 6879765 * 2
def baseEnd_6879765 : Nat := 3532626234979380621498043

theorem tailTrace_6879765 : CollatzResearch.WordTrace tailWord_6879765 prefixEnd_6879765 3532626234979380621498043 := by
  unfold tailWord_6879765
  simp only [CollatzResearch.WordTrace]
  refine ⟨250925643920793850162944749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167283762613862566775296499 250925643920793850162944749)
  ·
    refine ⟨94097116470297693811104281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250925643920793850162944749 94097116470297693811104281)
    ·
      refine ⟨70572837352723270358328211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94097116470297693811104281 70572837352723270358328211)
      ·
        refine ⟨105859256029084905537492317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70572837352723270358328211 105859256029084905537492317)
        ·
          refine ⟨39697221010906839576559619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105859256029084905537492317 39697221010906839576559619)
          ·
            refine ⟨59545831516360259364839429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39697221010906839576559619 59545831516360259364839429)
            ·
              refine ⟨11164843409317548630907393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59545831516360259364839429 11164843409317548630907393)
              ·
                refine ⟨8373632556988161473180545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11164843409317548630907393 8373632556988161473180545)
                ·
                  refine ⟨6280224417741121104885409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8373632556988161473180545 6280224417741121104885409)
                  ·
                    refine ⟨4710168313305840828664057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6280224417741121104885409 4710168313305840828664057)
                    ·
                      refine ⟨3532626234979380621498043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710168313305840828664057 3532626234979380621498043)
                      ·
                        rfl

theorem cell23_6879765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_6879765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879765 prefixEnd_6879765 := by exact prefixLift 6879765
  have htrace : WordTrace (prefixWord ++ tailWord_6879765) baseStart_6879765 baseEnd_6879765 := by
    simpa [prefixWord, tailWord_6879765, baseEnd_6879765] using wordTrace_append hprefix tailTrace_6879765
  have hstable : (prefixWord ++ tailWord_6879765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879765).length < 2 ^ (prefixWord ++ tailWord_6879765).sum := by decide
  have hdescent : baseEnd_6879765 < baseStart_6879765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879794 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7]
def baseStart_6879794 : Nat := 118140960795 + 6879794 * 2 ^ 59
def prefixEnd_6879794 : Nat := 4983230072969 + 3 ^ 40 * 6879794 * 2
def baseEnd_6879794 : Nat := 3532641125918361008035409

theorem tailTrace_6879794 : CollatzResearch.WordTrace tailWord_6879794 prefixEnd_6879794 3532641125918361008035409 := by
  unfold tailWord_6879794
  simp only [CollatzResearch.WordTrace]
  refine ⟨62731675409422197028937609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167284467758459192077166957 62731675409422197028937609)
  ·
    refine ⟨47048756557066647771703207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62731675409422197028937609 47048756557066647771703207)
    ·
      refine ⟨70573134835599971657554811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47048756557066647771703207 70573134835599971657554811)
      ·
        refine ⟨105859702253399957486332217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70573134835599971657554811 105859702253399957486332217)
        ·
          refine ⟨79394776690049968114749163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105859702253399957486332217 79394776690049968114749163)
          ·
            refine ⟨119092165035074952172123745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79394776690049968114749163 119092165035074952172123745)
            ·
              refine ⟨89319123776306214129092809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119092165035074952172123745 89319123776306214129092809)
              ·
                refine ⟨66989342832229660596819607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89319123776306214129092809 66989342832229660596819607)
                ·
                  refine ⟨100484014248344490895229411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66989342832229660596819607 100484014248344490895229411)
                  ·
                    refine ⟨150726021372516736342844117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100484014248344490895229411 150726021372516736342844117)
                    ·
                      refine ⟨3532641125918361008035409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150726021372516736342844117 3532641125918361008035409)
                      ·
                        rfl

theorem cell23_6879794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_6879794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879794 prefixEnd_6879794 := by exact prefixLift 6879794
  have htrace : WordTrace (prefixWord ++ tailWord_6879794) baseStart_6879794 baseEnd_6879794 := by
    simpa [prefixWord, tailWord_6879794, baseEnd_6879794] using wordTrace_append hprefix tailTrace_6879794
  have hstable : (prefixWord ++ tailWord_6879794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879794).length < 2 ^ (prefixWord ++ tailWord_6879794).sum := by decide
  have hdescent : baseEnd_6879794 < baseStart_6879794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879841 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 3]
def baseStart_6879841 : Nat := 118140960795 + 6879841 * 2 ^ 59
def prefixEnd_6879841 : Nat := 4983230072969 + 3 ^ 40 * 6879841 * 2
def baseEnd_6879841 : Nat := 3532665259509122324147693

theorem tailTrace_6879841 : CollatzResearch.WordTrace tailWord_6879841 prefixEnd_6879841 3532665259509122324147693 := by
  unfold tailWord_6879841
  simp only [CollatzResearch.WordTrace]
  refine ⟨250928415868518515142711377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167285610579012343428474251 250928415868518515142711377)
  ·
    refine ⟨188196311901388886357033533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250928415868518515142711377 188196311901388886357033533)
    ·
      refine ⟨70573616963020832383887575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188196311901388886357033533 70573616963020832383887575)
      ·
        refine ⟨105860425444531248575831363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70573616963020832383887575 105860425444531248575831363)
        ·
          refine ⟨158790638166796872863747045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105860425444531248575831363 158790638166796872863747045)
          ·
            refine ⟨29773244656274413661952571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158790638166796872863747045 29773244656274413661952571)
            ·
              refine ⟨44659866984411620492928857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29773244656274413661952571 44659866984411620492928857)
              ·
                refine ⟨33494900238308715369696643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44659866984411620492928857 33494900238308715369696643)
                ·
                  refine ⟨50242350357463073054544965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33494900238308715369696643 50242350357463073054544965)
                  ·
                    refine ⟨9420440692024326197727181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50242350357463073054544965 9420440692024326197727181)
                    ·
                      refine ⟨3532665259509122324147693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9420440692024326197727181 3532665259509122324147693)
                      ·
                        rfl

theorem cell23_6879841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_6879841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879841 prefixEnd_6879841 := by exact prefixLift 6879841
  have htrace : WordTrace (prefixWord ++ tailWord_6879841) baseStart_6879841 baseEnd_6879841 := by
    simpa [prefixWord, tailWord_6879841, baseEnd_6879841] using wordTrace_append hprefix tailTrace_6879841
  have hstable : (prefixWord ++ tailWord_6879841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879841).length < 2 ^ (prefixWord ++ tailWord_6879841).sum := by decide
  have hdescent : baseEnd_6879841 < baseStart_6879841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879864 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_6879864 : Nat := 118140960795 + 6879864 * 2 ^ 59
def prefixEnd_6879864 : Nat := 4983230072969 + 3 ^ 40 * 6879864 * 2
def baseEnd_6879864 : Nat := 3532677069564175734160087

theorem tailTrace_6879864 : CollatzResearch.WordTrace tailWord_6879864 prefixEnd_6879864 3532677069564175734160087 := by
  unfold tailWord_6879864
  simp only [CollatzResearch.WordTrace]
  refine ⟨125464627373717595035399323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167286169831623460047199097 125464627373717595035399323)
  ·
    refine ⟨188196941060576392553098985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125464627373717595035399323 188196941060576392553098985)
    ·
      refine ⟨141147705795432294414824239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188196941060576392553098985 141147705795432294414824239)
      ·
        refine ⟨211721558693148441622236359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141147705795432294414824239 211721558693148441622236359)
        ·
          refine ⟨317582338039722662433354539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211721558693148441622236359 317582338039722662433354539)
          ·
            refine ⟨476373507059583993650031809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317582338039722662433354539 476373507059583993650031809)
            ·
              refine ⟨357280130294687995237523857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476373507059583993650031809 357280130294687995237523857)
              ·
                refine ⟨267960097721015996428142893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357280130294687995237523857 267960097721015996428142893)
                ·
                  refine ⟨100485036645380998660553585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 267960097721015996428142893 100485036645380998660553585)
                  ·
                    refine ⟨75363777484035748995415189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100485036645380998660553585 75363777484035748995415189)
                    ·
                      refine ⟨3532677069564175734160087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75363777484035748995415189 3532677069564175734160087)
                      ·
                        rfl

theorem cell23_6879864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_6879864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879864 prefixEnd_6879864 := by exact prefixLift 6879864
  have htrace : WordTrace (prefixWord ++ tailWord_6879864) baseStart_6879864 baseEnd_6879864 := by
    simpa [prefixWord, tailWord_6879864, baseEnd_6879864] using wordTrace_append hprefix tailTrace_6879864
  have hstable : (prefixWord ++ tailWord_6879864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879864).length < 2 ^ (prefixWord ++ tailWord_6879864).sum := by decide
  have hdescent : baseEnd_6879864 < baseStart_6879864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879865 : List Nat := [1, 2, 1, 3, 3, 2, 3, 3, 1, 4]
def baseStart_6879865 : Nat := 118140960795 + 6879865 * 2 ^ 59
def prefixEnd_6879865 : Nat := 4983230072969 + 3 ^ 40 * 6879865 * 2
def baseEnd_6879865 : Nat := 1177559194348276743415861

theorem tailTrace_6879865 : CollatzResearch.WordTrace tailWord_6879865 prefixEnd_6879865 1177559194348276743415861 := by
  unfold tailWord_6879865
  simp only [CollatzResearch.WordTrace]
  refine ⟨250929291220431567241585049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167286194146954378161056699 250929291220431567241585049)
  ·
    refine ⟨188196968415323675431188787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250929291220431567241585049 188196968415323675431188787)
    ·
      refine ⟨282295452622985513146783181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188196968415323675431188787 282295452622985513146783181)
      ·
        refine ⟨105860794733619567430043693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282295452622985513146783181 105860794733619567430043693)
        ·
          refine ⟨39697798025107337786266385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105860794733619567430043693 39697798025107337786266385)
          ·
            refine ⟨29773348518830503339699789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39697798025107337786266385 29773348518830503339699789)
            ·
              refine ⟨11165005694561438752387421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29773348518830503339699789 11165005694561438752387421)
              ·
                refine ⟨4186877135460539532145283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11165005694561438752387421 4186877135460539532145283)
                ·
                  refine ⟨6280315703190809298217925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186877135460539532145283 6280315703190809298217925)
                  ·
                    refine ⟨1177559194348276743415861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280315703190809298217925 1177559194348276743415861)
                    ·
                      rfl

theorem cell23_6879865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 4].length) (baseStart_6879865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879865 prefixEnd_6879865 := by exact prefixLift 6879865
  have htrace : WordTrace (prefixWord ++ tailWord_6879865) baseStart_6879865 baseEnd_6879865 := by
    simpa [prefixWord, tailWord_6879865, baseEnd_6879865] using wordTrace_append hprefix tailTrace_6879865
  have hstable : (prefixWord ++ tailWord_6879865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879865).length < 2 ^ (prefixWord ++ tailWord_6879865).sum := by decide
  have hdescent : baseEnd_6879865 < baseStart_6879865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879882 : List Nat := [3, 1, 2, 3, 4, 1, 1, 1, 3, 4]
def baseStart_6879882 : Nat := 118140960795 + 6879882 * 2 ^ 59
def prefixEnd_6879882 : Nat := 4983230072969 + 3 ^ 40 * 6879882 * 2
def baseEnd_6879882 : Nat := 1177562104071985554578335

theorem tailTrace_6879882 : CollatzResearch.WordTrace tailWord_6879882 prefixEnd_6879882 1177562104071985554578335 := by
  unfold tailWord_6879882
  simp only [CollatzResearch.WordTrace]
  refine ⟨62732477815342494786238475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167286607507579986096635933 62732477815342494786238475)
  ·
    refine ⟨94098716723013742179357713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62732477815342494786238475 94098716723013742179357713)
    ·
      refine ⟨70574037542260306634518285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94098716723013742179357713 70574037542260306634518285)
      ·
        refine ⟨26465264078347614987944357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70574037542260306634518285 26465264078347614987944357)
        ·
          refine ⟨4962237014690177810239567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26465264078347614987944357 4962237014690177810239567)
          ·
            refine ⟨7443355522035266715359351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962237014690177810239567 7443355522035266715359351)
            ·
              refine ⟨11165033283052900073039027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443355522035266715359351 11165033283052900073039027)
              ·
                refine ⟨16747549924579350109558541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11165033283052900073039027 16747549924579350109558541)
                ·
                  refine ⟨6280331221717256291084453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16747549924579350109558541 6280331221717256291084453)
                  ·
                    refine ⟨1177562104071985554578335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280331221717256291084453 1177562104071985554578335)
                    ·
                      rfl

theorem cell23_6879882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_6879882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879882 prefixEnd_6879882 := by exact prefixLift 6879882
  have htrace : WordTrace (prefixWord ++ tailWord_6879882) baseStart_6879882 baseEnd_6879882 := by
    simpa [prefixWord, tailWord_6879882, baseEnd_6879882] using wordTrace_append hprefix tailTrace_6879882
  have hstable : (prefixWord ++ tailWord_6879882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879882).length < 2 ^ (prefixWord ++ tailWord_6879882).sum := by decide
  have hdescent : baseEnd_6879882 < baseStart_6879882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879982 : List Nat := [4, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_6879982 : Nat := 118140960795 + 6879982 * 2 ^ 59
def prefixEnd_6879982 : Nat := 4983230072969 + 3 ^ 40 * 6879982 * 2
def baseEnd_6879982 : Nat := 3532737660281406272484545

theorem tailTrace_6879982 : CollatzResearch.WordTrace tailWord_6879982 prefixEnd_6879982 3532737660281406272484545 := by
  unfold tailWord_6879982
  simp only [CollatzResearch.WordTrace]
  refine ⟨31366694820125962027949275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167289039040671797482396133 31366694820125962027949275)
  ·
    refine ⟨47050042230188943041923913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31366694820125962027949275 47050042230188943041923913)
    ·
      refine ⟨35287531672641707281442935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47050042230188943041923913 35287531672641707281442935)
      ·
        refine ⟨52931297508962560922164403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35287531672641707281442935 52931297508962560922164403)
        ·
          refine ⟨79396946263443841383246605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52931297508962560922164403 79396946263443841383246605)
          ·
            refine ⟨29773854848791440518717477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79396946263443841383246605 29773854848791440518717477)
            ·
              refine ⟨5582597784148395097259527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29773854848791440518717477 5582597784148395097259527)
              ·
                refine ⟨8373896676222592645889291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5582597784148395097259527 8373896676222592645889291)
                ·
                  refine ⟨12560845014333888968833937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8373896676222592645889291 12560845014333888968833937)
                  ·
                    refine ⟨9420633760750416726625453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12560845014333888968833937 9420633760750416726625453)
                    ·
                      refine ⟨3532737660281406272484545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9420633760750416726625453 3532737660281406272484545)
                      ·
                        rfl

theorem cell23_6879982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_6879982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879982 prefixEnd_6879982 := by exact prefixLift 6879982
  have htrace : WordTrace (prefixWord ++ tailWord_6879982) baseStart_6879982 baseEnd_6879982 := by
    simpa [prefixWord, tailWord_6879982, baseEnd_6879982] using wordTrace_append hprefix tailTrace_6879982
  have hstable : (prefixWord ++ tailWord_6879982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879982).length < 2 ^ (prefixWord ++ tailWord_6879982).sum := by decide
  have hdescent : baseEnd_6879982 < baseStart_6879982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6879989 : List Nat := [1, 3, 6, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6879989 : Nat := 118140960795 + 6879989 * 2 ^ 59
def prefixEnd_6879989 : Nat := 4983230072969 + 3 ^ 40 * 6879989 * 2
def baseEnd_6879989 : Nat := 1177580418215329248365671

theorem tailTrace_6879989 : CollatzResearch.WordTrace tailWord_6879989 prefixEnd_6879989 1177580418215329248365671 := by
  unfold tailWord_6879989
  simp only [CollatzResearch.WordTrace]
  refine ⟨250933813871982336419099021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167289209247988224279399347 250933813871982336419099021)
  ·
    refine ⟨94100180201993376157162133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250933813871982336419099021 94100180201993376157162133)
    ·
      refine ⟨4410945946968439507366975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94100180201993376157162133 4410945946968439507366975)
      ·
        refine ⟨6616418920452659261050463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410945946968439507366975 6616418920452659261050463)
        ·
          refine ⟨9924628380678988891575695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6616418920452659261050463 9924628380678988891575695)
          ·
            refine ⟨14886942571018483337363543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9924628380678988891575695 14886942571018483337363543)
            ·
              refine ⟨22330413856527725006045315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14886942571018483337363543 22330413856527725006045315)
              ·
                refine ⟨33495620784791587509067973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22330413856527725006045315 33495620784791587509067973)
                ·
                  refine ⟨6280428897148422657950245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33495620784791587509067973 6280428897148422657950245)
                  ·
                    refine ⟨1177580418215329248365671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280428897148422657950245 1177580418215329248365671)
                    ·
                      rfl

theorem cell23_6879989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6879989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6879989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6879989 prefixEnd_6879989 := by exact prefixLift 6879989
  have htrace : WordTrace (prefixWord ++ tailWord_6879989) baseStart_6879989 baseEnd_6879989 := by
    simpa [prefixWord, tailWord_6879989, baseEnd_6879989] using wordTrace_append hprefix tailTrace_6879989
  have hstable : (prefixWord ++ tailWord_6879989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6879989).length < 2 ^ (prefixWord ++ tailWord_6879989).sum := by decide
  have hdescent : baseEnd_6879989 < baseStart_6879989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6879989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880125 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 1, 6, 2]
def baseStart_6880125 : Nat := 118140960795 + 6880125 * 2 ^ 59
def prefixEnd_6880125 : Nat := 4983230072969 + 3 ^ 40 * 6880125 * 2
def baseEnd_6880125 : Nat := 3532811088014999212996387

theorem tailTrace_6880125 : CollatzResearch.WordTrace tailWord_6880125 prefixEnd_6880125 3532811088014999212996387 := by
  unfold tailWord_6880125
  simp only [CollatzResearch.WordTrace]
  refine ⟨250938774199489631646049829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167292516132993087764033219 250938774199489631646049829)
  ·
    refine ⟨47051020162404305933634343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250938774199489631646049829 47051020162404305933634343)
    ·
      refine ⟨70576530243606458900451515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47051020162404305933634343 70576530243606458900451515)
      ·
        refine ⟨105864795365409688350677273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70576530243606458900451515 105864795365409688350677273)
        ·
          refine ⟨79398596524057266263007955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105864795365409688350677273 79398596524057266263007955)
          ·
            refine ⟨119097894786085899394511933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79398596524057266263007955 119097894786085899394511933)
            ·
              refine ⟨44661710544782212272941975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119097894786085899394511933 44661710544782212272941975)
              ·
                refine ⟨66992565817173318409412963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44661710544782212272941975 66992565817173318409412963)
                ·
                  refine ⟨100488848725759977614119445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66992565817173318409412963 100488848725759977614119445)
                  ·
                    refine ⟨4710414784019998950661849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 100488848725759977614119445 4710414784019998950661849)
                    ·
                      refine ⟨3532811088014999212996387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710414784019998950661849 3532811088014999212996387)
                      ·
                        rfl

theorem cell23_6880125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_6880125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880125 prefixEnd_6880125 := by exact prefixLift 6880125
  have htrace : WordTrace (prefixWord ++ tailWord_6880125) baseStart_6880125 baseEnd_6880125 := by
    simpa [prefixWord, tailWord_6880125, baseEnd_6880125] using wordTrace_append hprefix tailTrace_6880125
  have hstable : (prefixWord ++ tailWord_6880125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880125).length < 2 ^ (prefixWord ++ tailWord_6880125).sum := by decide
  have hdescent : baseEnd_6880125 < baseStart_6880125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880135 : List Nat := [1, 1, 4, 2, 3, 1, 1, 1, 5, 4]
def baseStart_6880135 : Nat := 118140960795 + 6880135 * 2 ^ 59
def prefixEnd_6880135 : Nat := 4983230072969 + 3 ^ 40 * 6880135 * 2
def baseEnd_6880135 : Nat := 1177605407607181391290447

theorem tailTrace_6880135 : CollatzResearch.WordTrace tailWord_6880135 prefixEnd_6880135 1177605407607181391290447 := by
  unfold tailWord_6880135
  simp only [CollatzResearch.WordTrace]
  refine ⟨250939138929453403353913859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167292759286302268902609239 250939138929453403353913859)
  ·
    refine ⟨376408708394180105030870789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250939138929453403353913859 376408708394180105030870789)
    ·
      refine ⟨70576632823908769693288273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376408708394180105030870789 70576632823908769693288273)
      ·
        refine ⟨52932474617931577269966205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70576632823908769693288273 52932474617931577269966205)
        ·
          refine ⟨19849677981724341476237327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52932474617931577269966205 19849677981724341476237327)
          ·
            refine ⟨29774516972586512214355991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19849677981724341476237327 29774516972586512214355991)
            ·
              refine ⟨44661775458879768321533987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29774516972586512214355991 44661775458879768321533987)
              ·
                refine ⟨66992663188319652482300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44661775458879768321533987 66992663188319652482300981)
                ·
                  refine ⟨6280562173904967420215717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66992663188319652482300981 6280562173904967420215717)
                  ·
                    refine ⟨1177605407607181391290447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280562173904967420215717 1177605407607181391290447)
                    ·
                      rfl

theorem cell23_6880135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_6880135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880135 prefixEnd_6880135 := by exact prefixLift 6880135
  have htrace : WordTrace (prefixWord ++ tailWord_6880135) baseStart_6880135 baseEnd_6880135 := by
    simpa [prefixWord, tailWord_6880135, baseEnd_6880135] using wordTrace_append hprefix tailTrace_6880135
  have hstable : (prefixWord ++ tailWord_6880135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880135).length < 2 ^ (prefixWord ++ tailWord_6880135).sum := by decide
  have hdescent : baseEnd_6880135 < baseStart_6880135 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880192 : List Nat := [2, 1, 1, 2, 3, 3, 2, 2, 3, 1, 3]
def baseStart_6880192 : Nat := 118140960795 + 6880192 * 2 ^ 59
def prefixEnd_6880192 : Nat := 4983230072969 + 3 ^ 40 * 6880192 * 2
def baseEnd_6880192 : Nat := 3532845491218850450858579

theorem tailTrace_6880192 : CollatzResearch.WordTrace tailWord_6880192 prefixEnd_6880192 3532845491218850450858579 := by
  unfold tailWord_6880192
  simp only [CollatzResearch.WordTrace]
  refine ⟨125470608945123451044369415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167294145260164601392492553 125470608945123451044369415)
  ·
    refine ⟨188205913417685176566554123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125470608945123451044369415 188205913417685176566554123)
    ·
      refine ⟨282308870126527764849831185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188205913417685176566554123 282308870126527764849831185)
      ·
        refine ⟨211731652594895823637373389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282308870126527764849831185 211731652594895823637373389)
        ·
          refine ⟨79399369723085933864015021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211731652594895823637373389 79399369723085933864015021)
          ·
            refine ⟨29774763646157225199005633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79399369723085933864015021 29774763646157225199005633)
            ·
              refine ⟨22331072734617918899254225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29774763646157225199005633 22331072734617918899254225)
              ·
                refine ⟨16748304550963439174440669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22331072734617918899254225 16748304550963439174440669)
                ·
                  refine ⟨6280614206611289690415251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16748304550963439174440669 6280614206611289690415251)
                  ·
                    refine ⟨9420921309916934535622877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280614206611289690415251 9420921309916934535622877)
                    ·
                      refine ⟨3532845491218850450858579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9420921309916934535622877 3532845491218850450858579)
                      ·
                        rfl

theorem cell23_6880192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 2, 3, 1, 3].length) (baseStart_6880192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880192 prefixEnd_6880192 := by exact prefixLift 6880192
  have htrace : WordTrace (prefixWord ++ tailWord_6880192) baseStart_6880192 baseEnd_6880192 := by
    simpa [prefixWord, tailWord_6880192, baseEnd_6880192] using wordTrace_append hprefix tailTrace_6880192
  have hstable : (prefixWord ++ tailWord_6880192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880192).length < 2 ^ (prefixWord ++ tailWord_6880192).sum := by decide
  have hdescent : baseEnd_6880192 < baseStart_6880192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880202 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2]
def baseStart_6880202 : Nat := 118140960795 + 6880202 * 2 ^ 59
def prefixEnd_6880202 : Nat := 4983230072969 + 3 ^ 40 * 6880202 * 2
def baseEnd_6880202 : Nat := 3532850626025395411733533

theorem tailTrace_6880202 : CollatzResearch.WordTrace tailWord_6880202 prefixEnd_6880202 3532850626025395411733533 := by
  unfold tailWord_6880202
  simp only [CollatzResearch.WordTrace]
  refine ⟨62735395655052668449150715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167294388413473782531068573 62735395655052668449150715)
  ·
    refine ⟨94103093482579002673726073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62735395655052668449150715 94103093482579002673726073)
    ·
      refine ⟨70577320111934252005294555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94103093482579002673726073 70577320111934252005294555)
      ·
        refine ⟨105865980167901378007941833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70577320111934252005294555 105865980167901378007941833)
        ·
          refine ⟨79399485125926033505956375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105865980167901378007941833 79399485125926033505956375)
          ·
            refine ⟨119099227688889050258934563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79399485125926033505956375 119099227688889050258934563)
            ·
              refine ⟨178648841533333575388401845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119099227688889050258934563 178648841533333575388401845)
              ·
                refine ⟨16748328893750022692662673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178648841533333575388401845 16748328893750022692662673)
                ·
                  refine ⟨12561246670312517019497005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16748328893750022692662673 12561246670312517019497005)
                  ·
                    refine ⟨4710467501367193882311377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12561246670312517019497005 4710467501367193882311377)
                    ·
                      refine ⟨3532850626025395411733533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710467501367193882311377 3532850626025395411733533)
                      ·
                        rfl

theorem cell23_6880202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 2, 3, 2].length) (baseStart_6880202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880202 prefixEnd_6880202 := by exact prefixLift 6880202
  have htrace : WordTrace (prefixWord ++ tailWord_6880202) baseStart_6880202 baseEnd_6880202 := by
    simpa [prefixWord, tailWord_6880202, baseEnd_6880202] using wordTrace_append hprefix tailTrace_6880202
  have hstable : (prefixWord ++ tailWord_6880202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880202).length < 2 ^ (prefixWord ++ tailWord_6880202).sum := by decide
  have hdescent : baseEnd_6880202 < baseStart_6880202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880208 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 3, 6]
def baseStart_6880208 : Nat := 118140960795 + 6880208 * 2 ^ 59
def prefixEnd_6880208 : Nat := 4983230072969 + 3 ^ 40 * 6880208 * 2
def baseEnd_6880208 : Nat := 1177617902303107462752835

theorem tailTrace_6880208 : CollatzResearch.WordTrace tailWord_6880208 prefixEnd_6880208 1177617902303107462752835 := by
  unfold tailWord_6880208
  simp only [CollatzResearch.WordTrace]
  refine ⟨125470900729094468410660639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167294534305459291214214185 125470900729094468410660639)
  ·
    refine ⟨188206351093641702615990959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125470900729094468410660639 188206351093641702615990959)
    ·
      refine ⟨282309526640462553923986439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188206351093641702615990959 282309526640462553923986439)
      ·
        refine ⟨423464289960693830885979659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282309526640462553923986439 423464289960693830885979659)
        ·
          refine ⟨635196434941040746328969489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423464289960693830885979659 635196434941040746328969489)
          ·
            refine ⟨476397326205780559746727117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635196434941040746328969489 476397326205780559746727117)
            ·
              refine ⟨178648997327167709905022669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 476397326205780559746727117 178648997327167709905022669)
              ·
                refine ⟨66993373997687891214383501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178648997327167709905022669 66993373997687891214383501)
                ·
                  refine ⟨25122515249132959205393813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66993373997687891214383501 25122515249132959205393813)
                  ·
                    refine ⟨1177617902303107462752835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25122515249132959205393813 1177617902303107462752835)
                    ·
                      rfl

theorem cell23_6880208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_6880208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880208 prefixEnd_6880208 := by exact prefixLift 6880208
  have htrace : WordTrace (prefixWord ++ tailWord_6880208) baseStart_6880208 baseEnd_6880208 := by
    simpa [prefixWord, tailWord_6880208, baseEnd_6880208] using wordTrace_append hprefix tailTrace_6880208
  have hstable : (prefixWord ++ tailWord_6880208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880208).length < 2 ^ (prefixWord ++ tailWord_6880208).sum := by decide
  have hdescent : baseEnd_6880208 < baseStart_6880208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880212 : List Nat := [2, 4, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_6880212 : Nat := 118140960795 + 6880212 * 2 ^ 59
def prefixEnd_6880212 : Nat := 4983230072969 + 3 ^ 40 * 6880212 * 2
def baseEnd_6880212 : Nat := 1177618586943980124202829

theorem tailTrace_6880212 : CollatzResearch.WordTrace tailWord_6880212 prefixEnd_6880212 1177618586943980124202829 := by
  unfold tailWord_6880212
  simp only [CollatzResearch.WordTrace]
  refine ⟨125470973675087222752233445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167294631566782963669644593 125470973675087222752233445)
  ·
    refine ⟨23525807564078854266043771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125470973675087222752233445 23525807564078854266043771)
    ·
      refine ⟨35288711346118281399065657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23525807564078854266043771 35288711346118281399065657)
      ·
        refine ⟨26466533509588711049299243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35288711346118281399065657 26466533509588711049299243)
        ·
          refine ⟨39699800264383066573948865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26466533509588711049299243 39699800264383066573948865)
          ·
            refine ⟨29774850198287299930461649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39699800264383066573948865 29774850198287299930461649)
            ·
              refine ⟨22331137648715474947846237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29774850198287299930461649 22331137648715474947846237)
              ·
                refine ⟨8374176618268303105442339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22331137648715474947846237 8374176618268303105442339)
                ·
                  refine ⟨12561264927402454658163509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374176618268303105442339 12561264927402454658163509)
                  ·
                    refine ⟨1177618586943980124202829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12561264927402454658163509 1177618586943980124202829)
                    ·
                      rfl

theorem cell23_6880212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_6880212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880212 prefixEnd_6880212 := by exact prefixLift 6880212
  have htrace : WordTrace (prefixWord ++ tailWord_6880212) baseStart_6880212 baseEnd_6880212 := by
    simpa [prefixWord, tailWord_6880212, baseEnd_6880212] using wordTrace_append hprefix tailTrace_6880212
  have hstable : (prefixWord ++ tailWord_6880212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880212).length < 2 ^ (prefixWord ++ tailWord_6880212).sum := by decide
  have hdescent : baseEnd_6880212 < baseStart_6880212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880226 : List Nat := [3, 3, 3, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6880226 : Nat := 118140960795 + 6880226 * 2 ^ 59
def prefixEnd_6880226 : Nat := 4983230072969 + 3 ^ 40 * 6880226 * 2
def baseEnd_6880226 : Nat := 3532862949561103317833423

theorem tailTrace_6880226 : CollatzResearch.WordTrace tailWord_6880226 prefixEnd_6880226 3532862949561103317833423 := by
  unfold tailWord_6880226
  simp only [CollatzResearch.WordTrace]
  refine ⟨62735614493030931473869133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167294971981415817263651021 62735614493030931473869133)
  ·
    refine ⟨23525855434886599302700925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62735614493030931473869133 23525855434886599302700925)
    ·
      refine ⟨8822195788082474738512847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23525855434886599302700925 8822195788082474738512847)
      ·
        refine ⟨13233293682123712107769271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822195788082474738512847 13233293682123712107769271)
        ·
          refine ⟨19849940523185568161653907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233293682123712107769271 19849940523185568161653907)
          ·
            refine ⟨29774910784778352242480861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19849940523185568161653907 29774910784778352242480861)
            ·
              refine ⟨11165591544291882090930323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29774910784778352242480861 11165591544291882090930323)
              ·
                refine ⟨16748387316437823136395485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11165591544291882090930323 16748387316437823136395485)
                ·
                  refine ⟨6280645243664183676148307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16748387316437823136395485 6280645243664183676148307)
                  ·
                    refine ⟨9420967865496275514222461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280645243664183676148307 9420967865496275514222461)
                    ·
                      refine ⟨3532862949561103317833423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9420967865496275514222461 3532862949561103317833423)
                      ·
                        rfl

theorem cell23_6880226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6880226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880226 prefixEnd_6880226 := by exact prefixLift 6880226
  have htrace : WordTrace (prefixWord ++ tailWord_6880226) baseStart_6880226 baseEnd_6880226 := by
    simpa [prefixWord, tailWord_6880226, baseEnd_6880226] using wordTrace_append hprefix tailTrace_6880226
  have hstable : (prefixWord ++ tailWord_6880226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880226).length < 2 ^ (prefixWord ++ tailWord_6880226).sum := by decide
  have hdescent : baseEnd_6880226 < baseStart_6880226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880252 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_6880252 : Nat := 118140960795 + 6880252 * 2 ^ 59
def prefixEnd_6880252 : Nat := 4983230072969 + 3 ^ 40 * 6880252 * 2
def baseEnd_6880252 : Nat := 3532876300058120216108303

theorem tailTrace_6880252 : CollatzResearch.WordTrace tailWord_6880252 prefixEnd_6880252 3532876300058120216108303 := by
  unfold tailWord_6880252
  simp only [CollatzResearch.WordTrace]
  refine ⟨125471703135014766167961505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167295604180019688223948673 125471703135014766167961505)
  ·
    refine ⟨94103777351261074625971129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125471703135014766167961505 94103777351261074625971129)
    ·
      refine ⟨70577833013445805969478347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94103777351261074625971129 70577833013445805969478347)
      ·
        refine ⟨105866749520168708954217521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70577833013445805969478347 105866749520168708954217521)
        ·
          refine ⟨79400062140126531715663141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105866749520168708954217521 79400062140126531715663141)
          ·
            refine ⟨14887511651273724696686839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79400062140126531715663141 14887511651273724696686839)
            ·
              refine ⟨22331267476910587045030259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14887511651273724696686839 22331267476910587045030259)
              ·
                refine ⟨33496901215365880567545389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22331267476910587045030259 33496901215365880567545389)
                ·
                  refine ⟨12561337955762205212829521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33496901215365880567545389 12561337955762205212829521)
                  ·
                    refine ⟨9421003466821653909622141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12561337955762205212829521 9421003466821653909622141)
                    ·
                      refine ⟨3532876300058120216108303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421003466821653909622141 3532876300058120216108303)
                      ·
                        rfl

theorem cell23_6880252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_6880252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880252 prefixEnd_6880252 := by exact prefixLift 6880252
  have htrace : WordTrace (prefixWord ++ tailWord_6880252) baseStart_6880252 baseEnd_6880252 := by
    simpa [prefixWord, tailWord_6880252, baseEnd_6880252] using wordTrace_append hprefix tailTrace_6880252
  have hstable : (prefixWord ++ tailWord_6880252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880252).length < 2 ^ (prefixWord ++ tailWord_6880252).sum := by decide
  have hdescent : baseEnd_6880252 < baseStart_6880252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880305 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_6880305 : Nat := 118140960795 + 6880305 * 2 ^ 59
def prefixEnd_6880305 : Nat := 4983230072969 + 3 ^ 40 * 6880305 * 2
def baseEnd_6880305 : Nat := 3532903514532808508745559

theorem tailTrace_6880305 : CollatzResearch.WordTrace tailWord_6880305 prefixEnd_6880305 3532903514532808508745559 := by
  unfold tailWord_6880305
  simp only [CollatzResearch.WordTrace]
  refine ⟨250945339338837522387602369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167296892892558348258401579 250945339338837522387602369)
  ·
    refine ⟨188209004504128141790701777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250945339338837522387602369 188209004504128141790701777)
    ·
      refine ⟨141156753378096106343026333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188209004504128141790701777 141156753378096106343026333)
      ·
        refine ⟨52933782516786039878634875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141156753378096106343026333 52933782516786039878634875)
        ·
          refine ⟨79400673775179059817952313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52933782516786039878634875 79400673775179059817952313)
          ·
            refine ⟨59550505331384294863464235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79400673775179059817952313 59550505331384294863464235)
            ·
              refine ⟨89325757997076442295196353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59550505331384294863464235 89325757997076442295196353)
              ·
                refine ⟨66994318497807331721397265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89325757997076442295196353 66994318497807331721397265)
                ·
                  refine ⟨50245738873355498791047949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66994318497807331721397265 50245738873355498791047949)
                  ·
                    refine ⟨18842152077508312046642981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50245738873355498791047949 18842152077508312046642981)
                    ·
                      refine ⟨3532903514532808508745559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18842152077508312046642981 3532903514532808508745559)
                      ·
                        rfl

theorem cell23_6880305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_6880305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880305 prefixEnd_6880305 := by exact prefixLift 6880305
  have htrace : WordTrace (prefixWord ++ tailWord_6880305) baseStart_6880305 baseEnd_6880305 := by
    simpa [prefixWord, tailWord_6880305, baseEnd_6880305] using wordTrace_append hprefix tailTrace_6880305
  have hstable : (prefixWord ++ tailWord_6880305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880305).length < 2 ^ (prefixWord ++ tailWord_6880305).sum := by decide
  have hdescent : baseEnd_6880305 < baseStart_6880305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880309 : List Nat := [1, 3, 3, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_6880309 : Nat := 118140960795 + 6880309 * 2 ^ 59
def prefixEnd_6880309 : Nat := 4983230072969 + 3 ^ 40 * 6880309 * 2
def baseEnd_6880309 : Nat := 3532905568455426493095541

theorem tailTrace_6880309 : CollatzResearch.WordTrace tailWord_6880309 prefixEnd_6880309 3532905568455426493095541 := by
  unfold tailWord_6880309
  simp only [CollatzResearch.WordTrace]
  refine ⟨250945485230823031070747981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167296990153882020713831987 250945485230823031070747981)
  ·
    refine ⟨94104556961558636651530493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250945485230823031070747981 94104556961558636651530493)
    ·
      refine ⟨35289208860584488744323935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94104556961558636651530493 35289208860584488744323935)
      ·
        refine ⟨52933813290876733116485903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35289208860584488744323935 52933813290876733116485903)
        ·
          refine ⟨79400719936315099674728855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52933813290876733116485903 79400719936315099674728855)
          ·
            refine ⟨119101079904472649512093283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79400719936315099674728855 119101079904472649512093283)
            ·
              refine ⟨178651619856708974268139925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119101079904472649512093283 178651619856708974268139925)
              ·
                refine ⟨8374294680783233168819059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 178651619856708974268139925 8374294680783233168819059)
                ·
                  refine ⟨12561442021174849753228589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374294680783233168819059 12561442021174849753228589)
                  ·
                    refine ⟨4710540757940568657460721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12561442021174849753228589 4710540757940568657460721)
                    ·
                      refine ⟨3532905568455426493095541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710540757940568657460721 3532905568455426493095541)
                      ·
                        rfl

theorem cell23_6880309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_6880309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880309 prefixEnd_6880309 := by exact prefixLift 6880309
  have htrace : WordTrace (prefixWord ++ tailWord_6880309) baseStart_6880309 baseEnd_6880309 := by
    simpa [prefixWord, tailWord_6880309, baseEnd_6880309] using wordTrace_append hprefix tailTrace_6880309
  have hstable : (prefixWord ++ tailWord_6880309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880309).length < 2 ^ (prefixWord ++ tailWord_6880309).sum := by decide
  have hdescent : baseEnd_6880309 < baseStart_6880309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880325 : List Nat := [1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_6880325 : Nat := 118140960795 + 6880325 * 2 ^ 59
def prefixEnd_6880325 : Nat := 4983230072969 + 3 ^ 40 * 6880325 * 2
def baseEnd_6880325 : Nat := 3532913784145898430495467

theorem tailTrace_6880325 : CollatzResearch.WordTrace tailWord_6880325 prefixEnd_6880325 3532913784145898430495467 := by
  unfold tailWord_6880325
  simp only [CollatzResearch.WordTrace]
  refine ⟨250946068798765065803330429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167297379199176710535553619 250946068798765065803330429)
  ·
    refine ⟨94104775799536899676248911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250946068798765065803330429 94104775799536899676248911)
    ·
      refine ⟨141157163699305349514373367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94104775799536899676248911 141157163699305349514373367)
      ·
        refine ⟨211735745548958024271560051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141157163699305349514373367 211735745548958024271560051)
        ·
          refine ⟨317603618323437036407340077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211735745548958024271560051 317603618323437036407340077)
          ·
            refine ⟨119101356871288888652752529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317603618323437036407340077 119101356871288888652752529)
            ·
              refine ⟨89326017653466666489564397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119101356871288888652752529 89326017653466666489564397)
              ·
                refine ⟨33497256620049999933586649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89326017653466666489564397 33497256620049999933586649)
                ·
                  refine ⟨25122942465037499950189987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33497256620049999933586649 25122942465037499950189987)
                  ·
                    refine ⟨37684413697556249925284981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25122942465037499950189987 37684413697556249925284981)
                    ·
                      refine ⟨3532913784145898430495467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37684413697556249925284981 3532913784145898430495467)
                      ·
                        rfl

theorem cell23_6880325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_6880325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880325 prefixEnd_6880325 := by exact prefixLift 6880325
  have htrace : WordTrace (prefixWord ++ tailWord_6880325) baseStart_6880325 baseEnd_6880325 := by
    simpa [prefixWord, tailWord_6880325, baseEnd_6880325] using wordTrace_append hprefix tailTrace_6880325
  have hstable : (prefixWord ++ tailWord_6880325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880325).length < 2 ^ (prefixWord ++ tailWord_6880325).sum := by decide
  have hdescent : baseEnd_6880325 < baseStart_6880325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880333 : List Nat := [1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 3]
def baseStart_6880333 : Nat := 118140960795 + 6880333 * 2 ^ 59
def prefixEnd_6880333 : Nat := 4983230072969 + 3 ^ 40 * 6880333 * 2
def baseEnd_6880333 : Nat := 3532917891991134399195431

theorem tailTrace_6880333 : CollatzResearch.WordTrace tailWord_6880333 prefixEnd_6880333 3532917891991134399195431 := by
  unfold tailWord_6880333
  simp only [CollatzResearch.WordTrace]
  refine ⟨250946360582736083169621653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167297573721824055446414435 250946360582736083169621653)
  ·
    refine ⟨11763110652315753898576015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 250946360582736083169621653 11763110652315753898576015)
    ·
      refine ⟨17644665978473630847864023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11763110652315753898576015 17644665978473630847864023)
      ·
        refine ⟨26466998967710446271796035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17644665978473630847864023 26466998967710446271796035)
        ·
          refine ⟨39700498451565669407694053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26466998967710446271796035 39700498451565669407694053)
          ·
            refine ⟨7443843459668563013942635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39700498451565669407694053 7443843459668563013942635)
            ·
              refine ⟨11165765189502844520913953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443843459668563013942635 11165765189502844520913953)
              ·
                refine ⟨8374323892127133390685465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11165765189502844520913953 8374323892127133390685465)
                ·
                  refine ⟨6280742919095350043014099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8374323892127133390685465 6280742919095350043014099)
                  ·
                    refine ⟨9421114378643025064521149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280742919095350043014099 9421114378643025064521149)
                    ·
                      refine ⟨3532917891991134399195431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421114378643025064521149 3532917891991134399195431)
                      ·
                        rfl

theorem cell23_6880333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_6880333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880333 prefixEnd_6880333 := by exact prefixLift 6880333
  have htrace : WordTrace (prefixWord ++ tailWord_6880333) baseStart_6880333 baseEnd_6880333 := by
    simpa [prefixWord, tailWord_6880333, baseEnd_6880333] using wordTrace_append hprefix tailTrace_6880333
  have hstable : (prefixWord ++ tailWord_6880333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880333).length < 2 ^ (prefixWord ++ tailWord_6880333).sum := by decide
  have hdescent : baseEnd_6880333 < baseStart_6880333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880362 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 7]
def baseStart_6880362 : Nat := 118140960795 + 6880362 * 2 ^ 59
def prefixEnd_6880362 : Nat := 4983230072969 + 3 ^ 40 * 6880362 * 2
def baseEnd_6880362 : Nat := 392548086992234976192533

theorem tailTrace_6880362 : CollatzResearch.WordTrace tailWord_6880362 prefixEnd_6880362 392548086992234976192533 := by
  unfold tailWord_6880362
  simp only [CollatzResearch.WordTrace]
  refine ⟨62736854574907755280606835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167298278866420680748284893 62736854574907755280606835)
  ·
    refine ⟨94105281862361632920910253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62736854574907755280606835 94105281862361632920910253)
    ·
      refine ⟨35289480698385612345341345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94105281862361632920910253 35289480698385612345341345)
      ·
        refine ⟨26467110523789209259006009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35289480698385612345341345 26467110523789209259006009)
        ·
          refine ⟨19850332892841906944254507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26467110523789209259006009 19850332892841906944254507)
          ·
            refine ⟨29775499339262860416381761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19850332892841906944254507 29775499339262860416381761)
            ·
              refine ⟨22331624504447145312286321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29775499339262860416381761 22331624504447145312286321)
              ·
                refine ⟨16748718378335358984214741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22331624504447145312286321 16748718378335358984214741)
                ·
                  refine ⟨392548086992234976192533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16748718378335358984214741 392548086992234976192533)
                  ·
                    rfl

theorem cell23_6880362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 7].length) (baseStart_6880362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880362 prefixEnd_6880362 := by exact prefixLift 6880362
  have htrace : WordTrace (prefixWord ++ tailWord_6880362) baseStart_6880362 baseEnd_6880362 := by
    simpa [prefixWord, tailWord_6880362, baseEnd_6880362] using wordTrace_append hprefix tailTrace_6880362
  have hstable : (prefixWord ++ tailWord_6880362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880362).length < 2 ^ (prefixWord ++ tailWord_6880362).sum := by decide
  have hdescent : baseEnd_6880362 < baseStart_6880362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880375 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 1, 7]
def baseStart_6880375 : Nat := 118140960795 + 6880375 * 2 ^ 59
def prefixEnd_6880375 : Nat := 4983230072969 + 3 ^ 40 * 6880375 * 2
def baseEnd_6880375 : Nat := 1177646486059541078290079

theorem tailTrace_6880375 : CollatzResearch.WordTrace tailWord_6880375 prefixEnd_6880375 1177646486059541078290079 := by
  unfold tailWord_6880375
  simp only [CollatzResearch.WordTrace]
  refine ⟨250947892448583924342650579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167298594965722616228433719 250947892448583924342650579)
  ·
    refine ⟨376421838672875886513975869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250947892448583924342650579 376421838672875886513975869)
    ·
      refine ⟨141158189502328457442740951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376421838672875886513975869 141158189502328457442740951)
      ·
        refine ⟨211737284253492686164111427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141158189502328457442740951 211737284253492686164111427)
        ·
          refine ⟨317605926380239029246167141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211737284253492686164111427 317605926380239029246167141)
          ·
            refine ⟨59551111196294817983656339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317605926380239029246167141 59551111196294817983656339)
            ·
              refine ⟨89326666794442226975484509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59551111196294817983656339 89326666794442226975484509)
              ·
                refine ⟨33497500047915835115806691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89326666794442226975484509 33497500047915835115806691)
                ·
                  refine ⟨50246250071873752673710037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33497500047915835115806691 50246250071873752673710037)
                  ·
                    refine ⟨1177646486059541078290079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50246250071873752673710037 1177646486059541078290079)
                    ·
                      rfl

theorem cell23_6880375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_6880375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880375 prefixEnd_6880375 := by exact prefixLift 6880375
  have htrace : WordTrace (prefixWord ++ tailWord_6880375) baseStart_6880375 baseEnd_6880375 := by
    simpa [prefixWord, tailWord_6880375, baseEnd_6880375] using wordTrace_append hprefix tailTrace_6880375
  have hstable : (prefixWord ++ tailWord_6880375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880375).length < 2 ^ (prefixWord ++ tailWord_6880375).sum := by decide
  have hdescent : baseEnd_6880375 < baseStart_6880375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880402 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6880402 : Nat := 118140960795 + 6880402 * 2 ^ 59
def prefixEnd_6880402 : Nat := 4983230072969 + 3 ^ 40 * 6880402 * 2
def baseEnd_6880402 : Nat := 3532953322156294629232613

theorem tailTrace_6880402 : CollatzResearch.WordTrace tailWord_6880402 prefixEnd_6880402 3532953322156294629232613 := by
  unfold tailWord_6880402
  simp only [CollatzResearch.WordTrace]
  refine ⟨62737219304871526988470865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167299251479657405302588973 62737219304871526988470865)
  ·
    refine ⟨47052914478653645241353149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62737219304871526988470865 47052914478653645241353149)
    ·
      refine ⟨17644842929495116965507431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47052914478653645241353149 17644842929495116965507431)
      ·
        refine ⟨26467264394242675448261147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17644842929495116965507431 26467264394242675448261147)
        ·
          refine ⟨39700896591364013172391721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26467264394242675448261147 39700896591364013172391721)
          ·
            refine ⟨29775672443523009879293791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39700896591364013172391721 29775672443523009879293791)
            ·
              refine ⟨44663508665284514818940687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29775672443523009879293791 44663508665284514818940687)
              ·
                refine ⟨66995262997926772228411031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44663508665284514818940687 66995262997926772228411031)
                ·
                  refine ⟨100492894496890158342616547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66995262997926772228411031 100492894496890158342616547)
                  ·
                    refine ⟨150739341745335237513924821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100492894496890158342616547 150739341745335237513924821)
                    ·
                      refine ⟨3532953322156294629232613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150739341745335237513924821 3532953322156294629232613)
                      ·
                        rfl

theorem cell23_6880402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6880402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880402 prefixEnd_6880402 := by exact prefixLift 6880402
  have htrace : WordTrace (prefixWord ++ tailWord_6880402) baseStart_6880402 baseEnd_6880402 := by
    simpa [prefixWord, tailWord_6880402, baseEnd_6880402] using wordTrace_append hprefix tailTrace_6880402
  have hstable : (prefixWord ++ tailWord_6880402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880402).length < 2 ^ (prefixWord ++ tailWord_6880402).sum := by decide
  have hdescent : baseEnd_6880402 < baseStart_6880402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880405 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 2, 8]
def baseStart_6880405 : Nat := 118140960795 + 6880405 * 2 ^ 59
def prefixEnd_6880405 : Nat := 4983230072969 + 3 ^ 40 * 6880405 * 2
def baseEnd_6880405 : Nat := 1177651620866086039165033

theorem tailTrace_6880405 : CollatzResearch.WordTrace tailWord_6880405 prefixEnd_6880405 1177651620866086039165033 := by
  unfold tailWord_6880405
  simp only [CollatzResearch.WordTrace]
  refine ⟨250948986638475239466242669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167299324425650159644161779 250948986638475239466242669)
  ·
    refine ⟨94105869989428214799841001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250948986638475239466242669 94105869989428214799841001)
    ·
      refine ⟨70579402492071161099880751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94105869989428214799841001 70579402492071161099880751)
      ·
        refine ⟨105869103738106741649821127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70579402492071161099880751 105869103738106741649821127)
        ·
          refine ⟨158803655607160112474731691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105869103738106741649821127 158803655607160112474731691)
          ·
            refine ⟨238205483410740168712097537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158803655607160112474731691 238205483410740168712097537)
            ·
              refine ⟨178654112558055126534073153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238205483410740168712097537 178654112558055126534073153)
              ·
                refine ⟨133990584418541344900554865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178654112558055126534073153 133990584418541344900554865)
                ·
                  refine ⟨100492938313906008675416149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133990584418541344900554865 100492938313906008675416149)
                  ·
                    refine ⟨1177651620866086039165033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100492938313906008675416149 1177651620866086039165033)
                    ·
                      rfl

theorem cell23_6880405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_6880405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880405 prefixEnd_6880405 := by exact prefixLift 6880405
  have htrace : WordTrace (prefixWord ++ tailWord_6880405) baseStart_6880405 baseEnd_6880405 := by
    simpa [prefixWord, tailWord_6880405, baseEnd_6880405] using wordTrace_append hprefix tailTrace_6880405
  have hstable : (prefixWord ++ tailWord_6880405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880405).length < 2 ^ (prefixWord ++ tailWord_6880405).sum := by decide
  have hdescent : baseEnd_6880405 < baseStart_6880405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880425 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_6880425 : Nat := 118140960795 + 6880425 * 2 ^ 59
def prefixEnd_6880425 : Nat := 4983230072969 + 3 ^ 40 * 6880425 * 2
def baseEnd_6880425 : Nat := 3532965132211348039245007

theorem tailTrace_6880425 : CollatzResearch.WordTrace tailWord_6880425 prefixEnd_6880425 3532965132211348039245007 := by
  unfold tailWord_6880425
  simp only [CollatzResearch.WordTrace]
  refine ⟨250949716098402782881970729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167299810732268521921313819 250949716098402782881970729)
  ·
    refine ⟨188212287073802087161478047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250949716098402782881970729 188212287073802087161478047)
    ·
      refine ⟨282318430610703130742217071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188212287073802087161478047 282318430610703130742217071)
      ·
        refine ⟨423477645916054696113325607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282318430610703130742217071 423477645916054696113325607)
        ·
          refine ⟨635216468874082044169988411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423477645916054696113325607 635216468874082044169988411)
          ·
            refine ⟨952824703311123066254982617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635216468874082044169988411 952824703311123066254982617)
            ·
              refine ⟨714618527483342299691236963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952824703311123066254982617 714618527483342299691236963)
              ·
                refine ⟨1071927791225013449536855445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714618527483342299691236963 1071927791225013449536855445)
                ·
                  refine ⟨50246615213672505447040099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1071927791225013449536855445 50246615213672505447040099)
                  ·
                    refine ⟨75369922820508758170560149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50246615213672505447040099 75369922820508758170560149)
                    ·
                      refine ⟨3532965132211348039245007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75369922820508758170560149 3532965132211348039245007)
                      ·
                        rfl

theorem cell23_6880425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_6880425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880425 prefixEnd_6880425 := by exact prefixLift 6880425
  have htrace : WordTrace (prefixWord ++ tailWord_6880425) baseStart_6880425 baseEnd_6880425 := by
    simpa [prefixWord, tailWord_6880425, baseEnd_6880425] using wordTrace_append hprefix tailTrace_6880425
  have hstable : (prefixWord ++ tailWord_6880425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880425).length < 2 ^ (prefixWord ++ tailWord_6880425).sum := by decide
  have hdescent : baseEnd_6880425 < baseStart_6880425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880426 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_6880426 : Nat := 118140960795 + 6880426 * 2 ^ 59
def prefixEnd_6880426 : Nat := 4983230072969 + 3 ^ 40 * 6880426 * 2
def baseEnd_6880426 : Nat := 1177655215230667511777501

theorem tailTrace_6880426 : CollatzResearch.WordTrace tailWord_6880426 prefixEnd_6880426 1177655215230667511777501 := by
  unfold tailWord_6880426
  simp only [CollatzResearch.WordTrace]
  refine ⟨62737438142849790013189283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167299835047599440035171421 62737438142849790013189283)
  ·
    refine ⟨94106157214274685019783925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62737438142849790013189283 94106157214274685019783925)
    ·
      refine ⟨8822452238838251720604743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94106157214274685019783925 8822452238838251720604743)
      ·
        refine ⟨13233678358257377580907115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822452238838251720604743 13233678358257377580907115)
        ·
          refine ⟨19850517537386066371360673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233678358257377580907115 19850517537386066371360673)
          ·
            refine ⟨14887888153039549778520505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19850517537386066371360673 14887888153039549778520505)
            ·
              refine ⟨11165916114779662333890379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14887888153039549778520505 11165916114779662333890379)
              ·
                refine ⟨16748874172169493500835569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11165916114779662333890379 16748874172169493500835569)
                ·
                  refine ⟨12561655629127120125626677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16748874172169493500835569 12561655629127120125626677)
                  ·
                    refine ⟨1177655215230667511777501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12561655629127120125626677 1177655215230667511777501)
                    ·
                      rfl

theorem cell23_6880426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_6880426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880426 prefixEnd_6880426 := by exact prefixLift 6880426
  have htrace : WordTrace (prefixWord ++ tailWord_6880426) baseStart_6880426 baseEnd_6880426 := by
    simpa [prefixWord, tailWord_6880426, baseEnd_6880426] using wordTrace_append hprefix tailTrace_6880426
  have hstable : (prefixWord ++ tailWord_6880426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880426).length < 2 ^ (prefixWord ++ tailWord_6880426).sum := by decide
  have hdescent : baseEnd_6880426 < baseStart_6880426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880432 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_6880432 : Nat := 118140960795 + 6880432 * 2 ^ 59
def prefixEnd_6880432 : Nat := 4983230072969 + 3 ^ 40 * 6880432 * 2
def baseEnd_6880432 : Nat := 3532968726575929511857475

theorem tailTrace_6880432 : CollatzResearch.WordTrace tailWord_6880432 prefixEnd_6880432 3532968726575929511857475 := by
  unfold tailWord_6880432
  simp only [CollatzResearch.WordTrace]
  refine ⟨125474985704688711538737775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167299980939584948718317033 125474985704688711538737775)
  ·
    refine ⟨188212478557033067308106663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125474985704688711538737775 188212478557033067308106663)
    ·
      refine ⟨282318717835549600962159995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188212478557033067308106663 282318717835549600962159995)
      ·
        refine ⟨423478076753324401443239993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282318717835549600962159995 423478076753324401443239993)
        ·
          refine ⟨317608557564993301082429995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423478076753324401443239993 317608557564993301082429995)
          ·
            refine ⟨476412836347489951623644993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317608557564993301082429995 476412836347489951623644993)
            ·
              refine ⟨357309627260617463717733745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476412836347489951623644993 357309627260617463717733745)
              ·
                refine ⟨267982220445463097788300309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 357309627260617463717733745 267982220445463097788300309)
                ·
                  refine ⟨12561666583381082708826577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 267982220445463097788300309 12561666583381082708826577)
                  ·
                    refine ⟨9421249937535812031619933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12561666583381082708826577 9421249937535812031619933)
                    ·
                      refine ⟨3532968726575929511857475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421249937535812031619933 3532968726575929511857475)
                      ·
                        rfl

theorem cell23_6880432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_6880432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880432 prefixEnd_6880432 := by exact prefixLift 6880432
  have htrace : WordTrace (prefixWord ++ tailWord_6880432) baseStart_6880432 baseEnd_6880432 := by
    simpa [prefixWord, tailWord_6880432, baseEnd_6880432] using wordTrace_append hprefix tailTrace_6880432
  have hstable : (prefixWord ++ tailWord_6880432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880432).length < 2 ^ (prefixWord ++ tailWord_6880432).sum := by decide
  have hdescent : baseEnd_6880432 < baseStart_6880432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880435 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 10]
def baseStart_6880435 : Nat := 118140960795 + 6880435 * 2 ^ 59
def prefixEnd_6880435 : Nat := 4983230072969 + 3 ^ 40 * 6880435 * 2
def baseEnd_6880435 : Nat := 392552251890877000013329

theorem tailTrace_6880435 : CollatzResearch.WordTrace tailWord_6880435 prefixEnd_6880435 392552251890877000013329 := by
  unfold tailWord_6880435
  simp only [CollatzResearch.WordTrace]
  refine ⟨250950080828366554589834759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167300053885577703059889839 250950080828366554589834759)
  ·
    refine ⟨376425121242549831884752139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250950080828366554589834759 376425121242549831884752139)
    ·
      refine ⟨564637681863824747827128209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376425121242549831884752139 564637681863824747827128209)
      ·
        refine ⟨423478261397868560870346157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564637681863824747827128209 423478261397868560870346157)
        ·
          refine ⟨158804348024200710326379809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423478261397868560870346157 158804348024200710326379809)
          ·
            refine ⟨119103261018150532744784857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158804348024200710326379809 119103261018150532744784857)
            ·
              refine ⟨89327445763612899558588643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119103261018150532744784857 89327445763612899558588643)
              ·
                refine ⟨133991168645419349337882965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89327445763612899558588643 133991168645419349337882965)
                ·
                  refine ⟨392552251890877000013329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133991168645419349337882965 392552251890877000013329)
                  ·
                    rfl

theorem cell23_6880435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 10].length) (baseStart_6880435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880435 prefixEnd_6880435 := by exact prefixLift 6880435
  have htrace : WordTrace (prefixWord ++ tailWord_6880435) baseStart_6880435 baseEnd_6880435 := by
    simpa [prefixWord, tailWord_6880435, baseEnd_6880435] using wordTrace_append hprefix tailTrace_6880435
  have hstable : (prefixWord ++ tailWord_6880435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880435).length < 2 ^ (prefixWord ++ tailWord_6880435).sum := by decide
  have hdescent : baseEnd_6880435 < baseStart_6880435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880469 : List Nat := [1, 3, 2, 4, 1, 1, 2, 3, 6]
def baseStart_6880469 : Nat := 118140960795 + 6880469 * 2 ^ 59
def prefixEnd_6880469 : Nat := 4983230072969 + 3 ^ 40 * 6880469 * 2
def baseEnd_6880469 : Nat := 392554191706682874121645

theorem tailTrace_6880469 : CollatzResearch.WordTrace tailWord_6880469 prefixEnd_6880469 392554191706682874121645 := by
  unfold tailWord_6880469
  simp only [CollatzResearch.WordTrace]
  refine ⟨250951320910243378396572461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167300880606828918931048307 250951320910243378396572461)
  ·
    refine ⟨94106745341341266898714673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250951320910243378396572461 94106745341341266898714673)
    ·
      refine ⟨70580059006005950174036005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94106745341341266898714673 70580059006005950174036005)
      ·
        refine ⟨13233761063626115657631751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70580059006005950174036005 13233761063626115657631751)
        ·
          refine ⟨19850641595439173486447627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233761063626115657631751 19850641595439173486447627)
          ·
            refine ⟨29775962393158760229671441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19850641595439173486447627 29775962393158760229671441)
            ·
              refine ⟨22331971794869070172253581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29775962393158760229671441 22331971794869070172253581)
              ·
                refine ⟨8374489423075901314595093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22331971794869070172253581 8374489423075901314595093)
                ·
                  refine ⟨392554191706682874121645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8374489423075901314595093 392554191706682874121645)
                  ·
                    rfl

theorem cell23_6880469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 6].length) (baseStart_6880469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880469 prefixEnd_6880469 := by exact prefixLift 6880469
  have htrace : WordTrace (prefixWord ++ tailWord_6880469) baseStart_6880469 baseEnd_6880469 := by
    simpa [prefixWord, tailWord_6880469, baseEnd_6880469] using wordTrace_append hprefix tailTrace_6880469
  have hstable : (prefixWord ++ tailWord_6880469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880469).length < 2 ^ (prefixWord ++ tailWord_6880469).sum := by decide
  have hdescent : baseEnd_6880469 < baseStart_6880469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880479 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 3]
def baseStart_6880479 : Nat := 118140960795 + 6880479 * 2 ^ 59
def prefixEnd_6880479 : Nat := 4983230072969 + 3 ^ 40 * 6880479 * 2
def baseEnd_6880479 : Nat := 3532992860166690827969759

theorem tailTrace_6880479 : CollatzResearch.WordTrace tailWord_6880479 prefixEnd_6880479 3532992860166690827969759 := by
  unfold tailWord_6880479
  simp only [CollatzResearch.WordTrace]
  refine ⟨250951685640207150104436491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167301123760138100069624327 250951685640207150104436491)
  ·
    refine ⟨376427528460310725156654737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250951685640207150104436491 376427528460310725156654737)
    ·
      refine ⟨282320646345233043867491053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376427528460310725156654737 282320646345233043867491053)
      ·
        refine ⟨105870242379462391450309145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282320646345233043867491053 105870242379462391450309145)
        ·
          refine ⟨79402681784596793587731859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105870242379462391450309145 79402681784596793587731859)
          ·
            refine ⟨119104022676895190381597789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79402681784596793587731859 119104022676895190381597789)
            ·
              refine ⟨44664008503835696393099171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119104022676895190381597789 44664008503835696393099171)
              ·
                refine ⟨66996012755753544589648757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44664008503835696393099171 66996012755753544589648757)
                ·
                  refine ⟨6280876195851894805279571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66996012755753544589648757 6280876195851894805279571)
                  ·
                    refine ⟨9421314293777842207919357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280876195851894805279571 9421314293777842207919357)
                    ·
                      refine ⟨3532992860166690827969759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421314293777842207919357 3532992860166690827969759)
                      ·
                        rfl

theorem cell23_6880479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_6880479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880479 prefixEnd_6880479 := by exact prefixLift 6880479
  have htrace : WordTrace (prefixWord ++ tailWord_6880479) baseStart_6880479 baseEnd_6880479 := by
    simpa [prefixWord, tailWord_6880479, baseEnd_6880479] using wordTrace_append hprefix tailTrace_6880479
  have hstable : (prefixWord ++ tailWord_6880479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880479).length < 2 ^ (prefixWord ++ tailWord_6880479).sum := by decide
  have hdescent : baseEnd_6880479 < baseStart_6880479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880499 : List Nat := [1, 1, 1, 2, 2, 6, 1, 3, 1, 5]
def baseStart_6880499 : Nat := 118140960795 + 6880499 * 2 ^ 59
def prefixEnd_6880499 : Nat := 4983230072969 + 3 ^ 40 * 6880499 * 2
def baseEnd_6880499 : Nat := 1177667709926593583239889

theorem tailTrace_6880499 : CollatzResearch.WordTrace tailWord_6880499 prefixEnd_6880499 1177667709926593583239889 := by
  unfold tailWord_6880499
  simp only [CollatzResearch.WordTrace]
  refine ⟨250952415100134693520164551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167301610066756462346776367 250952415100134693520164551)
  ·
    refine ⟨376428622650202040280246827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250952415100134693520164551 376428622650202040280246827)
    ·
      refine ⟨564642933975303060420370241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376428622650202040280246827 564642933975303060420370241)
      ·
        refine ⟨423482200481477295315277681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564642933975303060420370241 423482200481477295315277681)
        ·
          refine ⟨317611650361107971486458261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423482200481477295315277681 317611650361107971486458261)
          ·
            refine ⟨14888046110676936163427731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 317611650361107971486458261 14888046110676936163427731)
            ·
              refine ⟨22332069166015404245141597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14888046110676936163427731 22332069166015404245141597)
              ·
                refine ⟨8374525937255776591928099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22332069166015404245141597 8374525937255776591928099)
                ·
                  refine ⟨12561788905883664887892149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374525937255776591928099 12561788905883664887892149)
                  ·
                    refine ⟨1177667709926593583239889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12561788905883664887892149 1177667709926593583239889)
                    ·
                      rfl

theorem cell23_6880499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 5].length) (baseStart_6880499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880499 prefixEnd_6880499 := by exact prefixLift 6880499
  have htrace : WordTrace (prefixWord ++ tailWord_6880499) baseStart_6880499 baseEnd_6880499 := by
    simpa [prefixWord, tailWord_6880499, baseEnd_6880499] using wordTrace_append hprefix tailTrace_6880499
  have hstable : (prefixWord ++ tailWord_6880499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880499).length < 2 ^ (prefixWord ++ tailWord_6880499).sum := by decide
  have hdescent : baseEnd_6880499 < baseStart_6880499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880513 : List Nat := [1, 2, 4, 1, 1, 3, 2, 4, 1, 1, 3]
def baseStart_6880513 : Nat := 118140960795 + 6880513 * 2 ^ 59
def prefixEnd_6880513 : Nat := 4983230072969 + 3 ^ 40 * 6880513 * 2
def baseEnd_6880513 : Nat := 3533010318508943694944603

theorem tailTrace_6880513 : CollatzResearch.WordTrace tailWord_6880513 prefixEnd_6880513 3533010318508943694944603 := by
  unfold tailWord_6880513
  simp only [CollatzResearch.WordTrace]
  refine ⟨250952925722083973911174193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167301950481389315940782795 250952925722083973911174193)
  ·
    refine ⟨188214694291562980433380645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250952925722083973911174193 188214694291562980433380645)
    ·
      refine ⟨35290255179668058831258871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188214694291562980433380645 35290255179668058831258871)
      ·
        refine ⟨52935382769502088246888307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35290255179668058831258871 52935382769502088246888307)
        ·
          refine ⟨79403074154253132370332461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52935382769502088246888307 79403074154253132370332461)
          ·
            refine ⟨29776152807844924638874673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79403074154253132370332461 29776152807844924638874673)
            ·
              refine ⟨22332114605883693479156005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29776152807844924638874673 22332114605883693479156005)
              ·
                refine ⟨4187271488603192527341751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22332114605883693479156005 4187271488603192527341751)
                ·
                  refine ⟨6280907232904788791012627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187271488603192527341751 6280907232904788791012627)
                  ·
                    refine ⟨9421360849357183186518941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6280907232904788791012627 9421360849357183186518941)
                    ·
                      refine ⟨3533010318508943694944603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421360849357183186518941 3533010318508943694944603)
                      ·
                        rfl

theorem cell23_6880513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_6880513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880513 prefixEnd_6880513 := by exact prefixLift 6880513
  have htrace : WordTrace (prefixWord ++ tailWord_6880513) baseStart_6880513 baseEnd_6880513 := by
    simpa [prefixWord, tailWord_6880513, baseEnd_6880513] using wordTrace_append hprefix tailTrace_6880513
  have hstable : (prefixWord ++ tailWord_6880513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880513).length < 2 ^ (prefixWord ++ tailWord_6880513).sum := by decide
  have hdescent : baseEnd_6880513 < baseStart_6880513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880536 : List Nat := [2, 1, 2, 3, 1, 4, 2, 2, 1, 1, 4]
def baseStart_6880536 : Nat := 118140960795 + 6880536 * 2 ^ 59
def prefixEnd_6880536 : Nat := 4983230072969 + 3 ^ 40 * 6880536 * 2
def baseEnd_6880536 : Nat := 3533022128563997104956997

theorem tailTrace_6880536 : CollatzResearch.WordTrace tailWord_6880536 prefixEnd_6880536 3533022128563997104956997 := by
  unfold tailWord_6880536
  simp only [CollatzResearch.WordTrace]
  refine ⟨125476882300500324419630731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167302509734000432559507641 125476882300500324419630731)
  ·
    refine ⟨188215323450750486629446097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125476882300500324419630731 188215323450750486629446097)
    ·
      refine ⟨141161492588062864972084573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188215323450750486629446097 141161492588062864972084573)
      ·
        refine ⟨52935559720523574364531715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141161492588062864972084573 52935559720523574364531715)
        ·
          refine ⟨79403339580785361546797573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52935559720523574364531715 79403339580785361546797573)
          ·
            refine ⟨14888126171397255290024545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79403339580785361546797573 14888126171397255290024545)
            ·
              refine ⟨11166094628547941467518409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14888126171397255290024545 11166094628547941467518409)
              ·
                refine ⟨8374570971410956100638807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11166094628547941467518409 8374570971410956100638807)
                ·
                  refine ⟨12561856457116434150958211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374570971410956100638807 12561856457116434150958211)
                  ·
                    refine ⟨18842784685674651226437317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12561856457116434150958211 18842784685674651226437317)
                    ·
                      refine ⟨3533022128563997104956997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18842784685674651226437317 3533022128563997104956997)
                      ·
                        rfl

theorem cell23_6880536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_6880536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880536 prefixEnd_6880536 := by exact prefixLift 6880536
  have htrace : WordTrace (prefixWord ++ tailWord_6880536) baseStart_6880536 baseEnd_6880536 := by
    simpa [prefixWord, tailWord_6880536, baseEnd_6880536] using wordTrace_append hprefix tailTrace_6880536
  have hstable : (prefixWord ++ tailWord_6880536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880536).length < 2 ^ (prefixWord ++ tailWord_6880536).sum := by decide
  have hdescent : baseEnd_6880536 < baseStart_6880536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880579 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 2, 7, 2]
def baseStart_6880579 : Nat := 118140960795 + 6880579 * 2 ^ 59
def prefixEnd_6880579 : Nat := 4983230072969 + 3 ^ 40 * 6880579 * 2
def baseEnd_6880579 : Nat := 3533044208232140436719299

theorem tailTrace_6880579 : CollatzResearch.WordTrace tailWord_6880579 prefixEnd_6880579 3533044208232140436719299 := by
  unfold tailWord_6880579
  simp only [CollatzResearch.WordTrace]
  refine ⟨250955332939844867183076791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167303555293229911455384527 250955332939844867183076791)
  ·
    refine ⟨376432999409767300774615187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250955332939844867183076791 376432999409767300774615187)
    ·
      refine ⟨564649499114650951161922781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376432999409767300774615187 564649499114650951161922781)
      ·
        refine ⟨211743562167994106685721043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564649499114650951161922781 211743562167994106685721043)
        ·
          refine ⟨317615343251991160028581565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211743562167994106685721043 317615343251991160028581565)
          ·
            refine ⟨119105753719496685010718087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317615343251991160028581565 119105753719496685010718087)
            ·
              refine ⟨178658630579245027516077131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119105753719496685010718087 178658630579245027516077131)
              ·
                refine ⟨267987945868867541274115697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178658630579245027516077131 267987945868867541274115697)
                ·
                  refine ⟨200990959401650655955586773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 267987945868867541274115697 200990959401650655955586773)
                  ·
                    refine ⟨4710725610976187248959065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 200990959401650655955586773 4710725610976187248959065)
                    ·
                      refine ⟨3533044208232140436719299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710725610976187248959065 3533044208232140436719299)
                      ·
                        rfl

theorem cell23_6880579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_6880579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880579 prefixEnd_6880579 := by exact prefixLift 6880579
  have htrace : WordTrace (prefixWord ++ tailWord_6880579) baseStart_6880579 baseEnd_6880579 := by
    simpa [prefixWord, tailWord_6880579, baseEnd_6880579] using wordTrace_append hprefix tailTrace_6880579
  have hstable : (prefixWord ++ tailWord_6880579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880579).length < 2 ^ (prefixWord ++ tailWord_6880579).sum := by decide
  have hdescent : baseEnd_6880579 < baseStart_6880579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880580 : List Nat := [2, 3, 4, 1, 1, 1, 4, 1, 2, 4]
def baseStart_6880580 : Nat := 118140960795 + 6880580 * 2 ^ 59
def prefixEnd_6880580 : Nat := 4983230072969 + 3 ^ 40 * 6880580 * 2
def baseEnd_6880580 : Nat := 1177681573904264977602265

theorem tailTrace_6880580 : CollatzResearch.WordTrace tailWord_6880580 prefixEnd_6880580 1177681573904264977602265 := by
  unfold tailWord_6880580
  simp only [CollatzResearch.WordTrace]
  refine ⟨125477684706420622176931597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167303579608560829569242129 125477684706420622176931597)
  ·
    refine ⟨47054131764907733316349349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125477684706420622176931597 47054131764907733316349349)
    ·
      refine ⟨8822649705920199996815503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47054131764907733316349349 8822649705920199996815503)
      ·
        refine ⟨13233974558880299995223255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8822649705920199996815503 13233974558880299995223255)
        ·
          refine ⟨19850961838320449992834883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13233974558880299995223255 19850961838320449992834883)
          ·
            refine ⟨29776442757480674989252325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19850961838320449992834883 29776442757480674989252325)
            ·
              refine ⟨5583083017027626560484811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29776442757480674989252325 5583083017027626560484811)
              ·
                refine ⟨8374624525541439840727217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583083017027626560484811 8374624525541439840727217)
                ·
                  refine ⟨6280968394156079880545413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8374624525541439840727217 6280968394156079880545413)
                  ·
                    refine ⟨1177681573904264977602265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6280968394156079880545413 1177681573904264977602265)
                    ·
                      rfl

theorem cell23_6880580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_6880580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880580 prefixEnd_6880580 := by exact prefixLift 6880580
  have htrace : WordTrace (prefixWord ++ tailWord_6880580) baseStart_6880580 baseEnd_6880580 := by
    simpa [prefixWord, tailWord_6880580, baseEnd_6880580] using wordTrace_append hprefix tailTrace_6880580
  have hstable : (prefixWord ++ tailWord_6880580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880580).length < 2 ^ (prefixWord ++ tailWord_6880580).sum := by decide
  have hdescent : baseEnd_6880580 < baseStart_6880580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880626 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_6880626 : Nat := 118140960795 + 6880626 * 2 ^ 59
def prefixEnd_6880626 : Nat := 4983230072969 + 3 ^ 40 * 6880626 * 2
def baseEnd_6880626 : Nat := 3533068341822901752831583

theorem tailTrace_6880626 : CollatzResearch.WordTrace tailWord_6880626 prefixEnd_6880626 3533068341822901752831583 := by
  unfold tailWord_6880626
  simp only [CollatzResearch.WordTrace]
  refine ⟨62739261792668648552509433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167304698113783062806691821 62739261792668648552509433)
  ·
    refine ⟨47054446344501486414382075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62739261792668648552509433 47054446344501486414382075)
    ·
      refine ⟨70581669516752229621573113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47054446344501486414382075 70581669516752229621573113)
      ·
        refine ⟨52936252137564172216179835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70581669516752229621573113 52936252137564172216179835)
        ·
          refine ⟨79404378206346258324269753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52936252137564172216179835 79404378206346258324269753)
          ·
            refine ⟨59553283654759693743202315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79404378206346258324269753 59553283654759693743202315)
            ·
              refine ⟨89329925482139540614803473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59553283654759693743202315 89329925482139540614803473)
              ·
                refine ⟨66997444111604655461102605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89329925482139540614803473 66997444111604655461102605)
                ·
                  refine ⟨25124041541851745797913477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66997444111604655461102605 25124041541851745797913477)
                  ·
                    refine ⟨4710757789097202337108777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25124041541851745797913477 4710757789097202337108777)
                    ·
                      refine ⟨3533068341822901752831583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710757789097202337108777 3533068341822901752831583)
                      ·
                        rfl

theorem cell23_6880626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_6880626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880626 prefixEnd_6880626 := by exact prefixLift 6880626
  have htrace : WordTrace (prefixWord ++ tailWord_6880626) baseStart_6880626 baseEnd_6880626 := by
    simpa [prefixWord, tailWord_6880626, baseEnd_6880626] using wordTrace_append hprefix tailTrace_6880626
  have hstable : (prefixWord ++ tailWord_6880626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880626).length < 2 ^ (prefixWord ++ tailWord_6880626).sum := by decide
  have hdescent : baseEnd_6880626 < baseStart_6880626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880632 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 13]
def baseStart_6880632 : Nat := 118140960795 + 6880632 * 2 ^ 59
def prefixEnd_6880632 : Nat := 4983230072969 + 3 ^ 40 * 6880632 * 2
def baseEnd_6880632 : Nat := 392563491411869858817395

theorem tailTrace_6880632 : CollatzResearch.WordTrace tailWord_6880632 prefixEnd_6880632 392563491411869858817395 := by
  unfold tailWord_6880632
  simp only [CollatzResearch.WordTrace]
  refine ⟨125478633004326428617378075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167304844005768571489837433 125478633004326428617378075)
  ·
    refine ⟨188217949506489642926067113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125478633004326428617378075 188217949506489642926067113)
    ·
      refine ⟨141163462129867232194550335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188217949506489642926067113 141163462129867232194550335)
      ·
        refine ⟨211745193194800848291825503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141163462129867232194550335 211745193194800848291825503)
        ·
          refine ⟨317617789792201272437738255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211745193194800848291825503 317617789792201272437738255)
          ·
            refine ⟨476426684688301908656607383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317617789792201272437738255 476426684688301908656607383)
            ·
              refine ⟨714640027032452862984911075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476426684688301908656607383 714640027032452862984911075)
              ·
                refine ⟨1071960040548679294477366613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714640027032452862984911075 1071960040548679294477366613)
                ·
                  refine ⟨392563491411869858817395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1071960040548679294477366613 392563491411869858817395)
                  ·
                    rfl

theorem cell23_6880632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 13].length) (baseStart_6880632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880632 prefixEnd_6880632 := by exact prefixLift 6880632
  have htrace : WordTrace (prefixWord ++ tailWord_6880632) baseStart_6880632 baseEnd_6880632 := by
    simpa [prefixWord, tailWord_6880632, baseEnd_6880632] using wordTrace_append hprefix tailTrace_6880632
  have hstable : (prefixWord ++ tailWord_6880632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880632).length < 2 ^ (prefixWord ++ tailWord_6880632).sum := by decide
  have hdescent : baseEnd_6880632 < baseStart_6880632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880643 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 1, 4, 2]
def baseStart_6880643 : Nat := 118140960795 + 6880643 * 2 ^ 59
def prefixEnd_6880643 : Nat := 4983230072969 + 3 ^ 40 * 6880643 * 2
def baseEnd_6880643 : Nat := 3533077070994028186319005

theorem tailTrace_6880643 : CollatzResearch.WordTrace tailWord_6880643 prefixEnd_6880643 3533077070994028186319005 := by
  unfold tailWord_6880643
  simp only [CollatzResearch.WordTrace]
  refine ⟨250957667211613006113406583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167305111474408670742271055 250957667211613006113406583)
  ·
    refine ⟨376436500817419509170109875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250957667211613006113406583 376436500817419509170109875)
    ·
      refine ⟨564654751226129263755164813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376436500817419509170109875 564654751226129263755164813)
      ·
        refine ⟨211745531709798473908186805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564654751226129263755164813 211745531709798473908186805)
        ·
          refine ⟨19851143597793606928892513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 211745531709798473908186805 19851143597793606928892513)
          ·
            refine ⟨14888357698345205196669385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19851143597793606928892513 14888357698345205196669385)
            ·
              refine ⟨11166268273758903897502039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14888357698345205196669385 11166268273758903897502039)
              ·
                refine ⟨16749402410638355846253059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166268273758903897502039 16749402410638355846253059)
                ·
                  refine ⟨25124103615957533769379589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16749402410638355846253059 25124103615957533769379589)
                  ·
                    refine ⟨4710769427992037581758673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25124103615957533769379589 4710769427992037581758673)
                    ·
                      refine ⟨3533077070994028186319005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710769427992037581758673 3533077070994028186319005)
                      ·
                        rfl

theorem cell23_6880643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_6880643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880643 prefixEnd_6880643 := by exact prefixLift 6880643
  have htrace : WordTrace (prefixWord ++ tailWord_6880643) baseStart_6880643 baseEnd_6880643 := by
    simpa [prefixWord, tailWord_6880643, baseEnd_6880643] using wordTrace_append hprefix tailTrace_6880643
  have hstable : (prefixWord ++ tailWord_6880643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880643).length < 2 ^ (prefixWord ++ tailWord_6880643).sum := by decide
  have hdescent : baseEnd_6880643 < baseStart_6880643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880664 : List Nat := [2, 1, 2, 5, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6880664 : Nat := 118140960795 + 6880664 * 2 ^ 59
def prefixEnd_6880664 : Nat := 4983230072969 + 3 ^ 40 * 6880664 * 2
def baseEnd_6880664 : Nat := 3533087854087772604156409

theorem tailTrace_6880664 : CollatzResearch.WordTrace tailWord_6880664 prefixEnd_6880664 3533087854087772604156409 := by
  unfold tailWord_6880664
  simp only [CollatzResearch.WordTrace]
  refine ⟨125479216572268463349960523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167305622096357951133280697 125479216572268463349960523)
  ·
    refine ⟨188218824858402695024940785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125479216572268463349960523 188218824858402695024940785)
    ·
      refine ⟨141164118643802021268705589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188218824858402695024940785 141164118643802021268705589)
      ·
        refine ⟨13234136122856439493941149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141164118643802021268705589 13234136122856439493941149)
        ·
          refine ⟨4962801046071164810227931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13234136122856439493941149 4962801046071164810227931)
          ·
            refine ⟨7444201569106747215341897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962801046071164810227931 7444201569106747215341897)
            ·
              refine ⟨5583151176830060411506423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7444201569106747215341897 5583151176830060411506423)
              ·
                refine ⟨8374726765245090617259635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583151176830060411506423 8374726765245090617259635)
                ·
                  refine ⟨12562090147867635925889453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374726765245090617259635 12562090147867635925889453)
                  ·
                    refine ⟨4710783805450363472208545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12562090147867635925889453 4710783805450363472208545)
                    ·
                      refine ⟨3533087854087772604156409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710783805450363472208545 3533087854087772604156409)
                      ·
                        rfl

theorem cell23_6880664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6880664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880664 prefixEnd_6880664 := by exact prefixLift 6880664
  have htrace : WordTrace (prefixWord ++ tailWord_6880664) baseStart_6880664 baseEnd_6880664 := by
    simpa [prefixWord, tailWord_6880664, baseEnd_6880664] using wordTrace_append hprefix tailTrace_6880664
  have hstable : (prefixWord ++ tailWord_6880664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880664).length < 2 ^ (prefixWord ++ tailWord_6880664).sum := by decide
  have hdescent : baseEnd_6880664 < baseStart_6880664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880689 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_6880689 : Nat := 118140960795 + 6880689 * 2 ^ 59
def prefixEnd_6880689 : Nat := 4983230072969 + 3 ^ 40 * 6880689 * 2
def baseEnd_6880689 : Nat := 3533100691104135006343793

theorem tailTrace_6880689 : CollatzResearch.WordTrace tailWord_6880689 prefixEnd_6880689 3533100691104135006343793 := by
  unfold tailWord_6880689
  simp only [CollatzResearch.WordTrace]
  refine ⟨250959344969446355969581121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167306229979630903979720747 250959344969446355969581121)
  ·
    refine ⟨188219508727084766977185841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250959344969446355969581121 188219508727084766977185841)
    ·
      refine ⟨141164631545313575232889381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188219508727084766977185841 141164631545313575232889381)
      ·
        refine ⟨26468368414746295356166759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141164631545313575232889381 26468368414746295356166759)
        ·
          refine ⟨39702552622119443034250139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26468368414746295356166759 39702552622119443034250139)
          ·
            refine ⟨59553828933179164551375209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39702552622119443034250139 59553828933179164551375209)
            ·
              refine ⟨44665371699884373413531407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59553828933179164551375209 44665371699884373413531407)
              ·
                refine ⟨66998057549826560120297111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44665371699884373413531407 66998057549826560120297111)
                ·
                  refine ⟨100497086324739840180445667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66998057549826560120297111 100497086324739840180445667)
                  ·
                    refine ⟨150745629487109760270668501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100497086324739840180445667 150745629487109760270668501)
                    ·
                      refine ⟨3533100691104135006343793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150745629487109760270668501 3533100691104135006343793)
                      ·
                        rfl

theorem cell23_6880689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_6880689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880689 prefixEnd_6880689 := by exact prefixLift 6880689
  have htrace : WordTrace (prefixWord ++ tailWord_6880689) baseStart_6880689 baseEnd_6880689 := by
    simpa [prefixWord, tailWord_6880689, baseEnd_6880689] using wordTrace_append hprefix tailTrace_6880689
  have hstable : (prefixWord ++ tailWord_6880689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880689).length < 2 ^ (prefixWord ++ tailWord_6880689).sum := by decide
  have hdescent : baseEnd_6880689 < baseStart_6880689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880716 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_6880716 : Nat := 118140960795 + 6880716 * 2 ^ 59
def prefixEnd_6880716 : Nat := 4983230072969 + 3 ^ 40 * 6880716 * 2
def baseEnd_6880716 : Nat := 3533114555081806400706169

theorem tailTrace_6880716 : CollatzResearch.WordTrace tailWord_6880716 prefixEnd_6880716 3533114555081806400706169 := by
  unfold tailWord_6880716
  simp only [CollatzResearch.WordTrace]
  refine ⟨125480164870174269790407001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167306886493565693053876001 125480164870174269790407001)
  ·
    refine ⟨94110123652630702342805251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125480164870174269790407001 94110123652630702342805251)
    ·
      refine ⟨141165185478946053514207877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94110123652630702342805251 141165185478946053514207877)
      ·
        refine ⟨26468472277302385033913977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141165185478946053514207877 26468472277302385033913977)
        ·
          refine ⟨19851354207976788775435483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26468472277302385033913977 19851354207976788775435483)
          ·
            refine ⟨29777031311965183163153225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19851354207976788775435483 29777031311965183163153225)
            ·
              refine ⟨22332773483973887372364919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29777031311965183163153225 22332773483973887372364919)
              ·
                refine ⟨33499160225960831058547379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22332773483973887372364919 33499160225960831058547379)
                ·
                  refine ⟨50248740338941246587821069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33499160225960831058547379 50248740338941246587821069)
                  ·
                    refine ⟨18843277627102967470432901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50248740338941246587821069 18843277627102967470432901)
                    ·
                      refine ⟨3533114555081806400706169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18843277627102967470432901 3533114555081806400706169)
                      ·
                        rfl

theorem cell23_6880716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_6880716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880716 prefixEnd_6880716 := by exact prefixLift 6880716
  have htrace : WordTrace (prefixWord ++ tailWord_6880716) baseStart_6880716 baseEnd_6880716 := by
    simpa [prefixWord, tailWord_6880716, baseEnd_6880716] using wordTrace_append hprefix tailTrace_6880716
  have hstable : (prefixWord ++ tailWord_6880716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880716).length < 2 ^ (prefixWord ++ tailWord_6880716).sum := by decide
  have hdescent : baseEnd_6880716 < baseStart_6880716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880733 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6880733 : Nat := 118140960795 + 6880733 * 2 ^ 59
def prefixEnd_6880733 : Nat := 4983230072969 + 3 ^ 40 * 6880733 * 2
def baseEnd_6880733 : Nat := 3533123284252932834193591

theorem tailTrace_6880733 : CollatzResearch.WordTrace tailWord_6880733 prefixEnd_6880733 3533123284252932834193591 := by
  unfold tailWord_6880733
  simp only [CollatzResearch.WordTrace]
  refine ⟨250960949781286951484182853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167307299854191300989455235 250960949781286951484182853)
  ·
    refine ⟨47055178083991303403284285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250960949781286951484182853 47055178083991303403284285)
    ·
      refine ⟨17645691781496738776231607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47055178083991303403284285 17645691781496738776231607)
      ·
        refine ⟨26468537672245108164347411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17645691781496738776231607 26468537672245108164347411)
        ·
          refine ⟨39702806508367662246521117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26468537672245108164347411 39702806508367662246521117)
          ·
            refine ⟨14888552440637873342445419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39702806508367662246521117 14888552440637873342445419)
            ·
              refine ⟨22332828660956810013668129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14888552440637873342445419 22332828660956810013668129)
              ·
                refine ⟨16749621495717607510251097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22332828660956810013668129 16749621495717607510251097)
                ·
                  refine ⟨12562216121788205632688323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16749621495717607510251097 12562216121788205632688323)
                  ·
                    refine ⟨18843324182682308449032485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12562216121788205632688323 18843324182682308449032485)
                    ·
                      refine ⟨3533123284252932834193591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18843324182682308449032485 3533123284252932834193591)
                      ·
                        rfl

theorem cell23_6880733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6880733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880733 prefixEnd_6880733 := by exact prefixLift 6880733
  have htrace : WordTrace (prefixWord ++ tailWord_6880733) baseStart_6880733 baseEnd_6880733 := by
    simpa [prefixWord, tailWord_6880733, baseEnd_6880733] using wordTrace_append hprefix tailTrace_6880733
  have hstable : (prefixWord ++ tailWord_6880733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880733).length < 2 ^ (prefixWord ++ tailWord_6880733).sum := by decide
  have hdescent : baseEnd_6880733 < baseStart_6880733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880743 : List Nat := [1, 1, 5, 2, 1, 2, 3, 1, 3, 4]
def baseStart_6880743 : Nat := 118140960795 + 6880743 * 2 ^ 59
def prefixEnd_6880743 : Nat := 4983230072969 + 3 ^ 40 * 6880743 * 2
def baseEnd_6880743 : Nat := 1177709473019825931689515

theorem tailTrace_6880743 : CollatzResearch.WordTrace tailWord_6880743 prefixEnd_6880743 1177709473019825931689515 := by
  unfold tailWord_6880743
  simp only [CollatzResearch.WordTrace]
  refine ⟨250961314511250723192046883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167307543007500482128031255 250961314511250723192046883)
  ·
    refine ⟨376441971766876084788070325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250961314511250723192046883 376441971766876084788070325)
    ·
      refine ⟨35291434853144632948881593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 376441971766876084788070325 35291434853144632948881593)
      ·
        refine ⟨26468576139858474711661195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35291434853144632948881593 26468576139858474711661195)
        ·
          refine ⟨39702864209787712067491793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26468576139858474711661195 39702864209787712067491793)
          ·
            refine ⟨29777148157340784050618845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39702864209787712067491793 29777148157340784050618845)
            ·
              refine ⟨11166430559002794018982067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29777148157340784050618845 11166430559002794018982067)
              ·
                refine ⟨16749645838504191028473101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166430559002794018982067 16749645838504191028473101)
                ·
                  refine ⟨6281117189439071635677413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16749645838504191028473101 6281117189439071635677413)
                  ·
                    refine ⟨1177709473019825931689515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281117189439071635677413 1177709473019825931689515)
                    ·
                      rfl

theorem cell23_6880743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_6880743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880743 prefixEnd_6880743 := by exact prefixLift 6880743
  have htrace : WordTrace (prefixWord ++ tailWord_6880743) baseStart_6880743 baseEnd_6880743 := by
    simpa [prefixWord, tailWord_6880743, baseEnd_6880743] using wordTrace_append hprefix tailTrace_6880743
  have hstable : (prefixWord ++ tailWord_6880743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880743).length < 2 ^ (prefixWord ++ tailWord_6880743).sum := by decide
  have hdescent : baseEnd_6880743 < baseStart_6880743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880770 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_6880770 : Nat := 118140960795 + 6880770 * 2 ^ 59
def prefixEnd_6880770 : Nat := 4983230072969 + 3 ^ 40 * 6880770 * 2
def baseEnd_6880770 : Nat := 3533142283037149189430921

theorem tailTrace_6880770 : CollatzResearch.WordTrace tailWord_6880770 prefixEnd_6880770 3533142283037149189430921 := by
  unfold tailWord_6880770
  simp only [CollatzResearch.WordTrace]
  refine ⟨62740574820538226700819941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167308199521435271202186509 62740574820538226700819941)
  ·
    refine ⟨11763857778850917506403739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62740574820538226700819941 11763857778850917506403739)
    ·
      refine ⟨17645786668276376259605609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11763857778850917506403739 17645786668276376259605609)
      ·
        refine ⟨13234340001207282194704207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17645786668276376259605609 13234340001207282194704207)
        ·
          refine ⟨19851510001810923292056311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234340001207282194704207 19851510001810923292056311)
          ·
            refine ⟨29777265002716384938084467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19851510001810923292056311 29777265002716384938084467)
            ·
              refine ⟨44665897504074577407126701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29777265002716384938084467 44665897504074577407126701)
              ·
                refine ⟨16749711564027966527672513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44665897504074577407126701 16749711564027966527672513)
                ·
                  refine ⟨12562283673020974895754385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16749711564027966527672513 12562283673020974895754385)
                  ·
                    refine ⟨9421712754765731171815789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12562283673020974895754385 9421712754765731171815789)
                    ·
                      refine ⟨3533142283037149189430921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421712754765731171815789 3533142283037149189430921)
                      ·
                        rfl

theorem cell23_6880770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_6880770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880770 prefixEnd_6880770 := by exact prefixLift 6880770
  have htrace : WordTrace (prefixWord ++ tailWord_6880770) baseStart_6880770 baseEnd_6880770 := by
    simpa [prefixWord, tailWord_6880770, baseEnd_6880770] using wordTrace_append hprefix tailTrace_6880770
  have hstable : (prefixWord ++ tailWord_6880770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880770).length < 2 ^ (prefixWord ++ tailWord_6880770).sum := by decide
  have hdescent : baseEnd_6880770 < baseStart_6880770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880816 : List Nat := [2, 1, 1, 1, 2, 3, 1, 2, 6, 4]
def baseStart_6880816 : Nat := 118140960795 + 6880816 * 2 ^ 59
def prefixEnd_6880816 : Nat := 4983230072969 + 3 ^ 40 * 6880816 * 2
def baseEnd_6880816 : Nat := 1177721967715752003151903

theorem tailTrace_6880816 : CollatzResearch.WordTrace tailWord_6880816 prefixEnd_6880816 1177721967715752003151903 := by
  unfold tailWord_6880816
  simp only [CollatzResearch.WordTrace]
  refine ⟨125481988519993128329727151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167309318026657504439636201 125481988519993128329727151)
  ·
    refine ⟨188222982779989692494590727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125481988519993128329727151 188222982779989692494590727)
    ·
      refine ⟨282334474169984538741886091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188222982779989692494590727 282334474169984538741886091)
      ·
        refine ⟨423501711254976808112829137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282334474169984538741886091 423501711254976808112829137)
        ·
          refine ⟨317626283441232606084621853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423501711254976808112829137 317626283441232606084621853)
          ·
            refine ⟨119109856290462227281733195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317626283441232606084621853 119109856290462227281733195)
            ·
              refine ⟨178664784435693340922599793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119109856290462227281733195 178664784435693340922599793)
              ·
                refine ⟨133998588326770005691949845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178664784435693340922599793 133998588326770005691949845)
                ·
                  refine ⟨6281183827817344016810149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133998588326770005691949845 6281183827817344016810149)
                  ·
                    refine ⟨1177721967715752003151903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281183827817344016810149 1177721967715752003151903)
                    ·
                      rfl

theorem cell23_6880816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 4].length) (baseStart_6880816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880816 prefixEnd_6880816 := by exact prefixLift 6880816
  have htrace : WordTrace (prefixWord ++ tailWord_6880816) baseStart_6880816 baseEnd_6880816 := by
    simpa [prefixWord, tailWord_6880816, baseEnd_6880816] using wordTrace_append hprefix tailTrace_6880816
  have hstable : (prefixWord ++ tailWord_6880816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880816).length < 2 ^ (prefixWord ++ tailWord_6880816).sum := by decide
  have hdescent : baseEnd_6880816 < baseStart_6880816 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880833 : List Nat := [1, 2, 5, 1, 1, 1, 2, 2, 4, 4]
def baseStart_6880833 : Nat := 118140960795 + 6880833 * 2 ^ 59
def prefixEnd_6880833 : Nat := 4983230072969 + 3 ^ 40 * 6880833 * 2
def baseEnd_6880833 : Nat := 1177724877439460814314377

theorem tailTrace_6880833 : CollatzResearch.WordTrace tailWord_6880833 prefixEnd_6880833 1177724877439460814314377 := by
  unfold tailWord_6880833
  simp only [CollatzResearch.WordTrace]
  refine ⟨250964597080924668562823153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167309731387283112375215435 250964597080924668562823153)
  ·
    refine ⟨188223447810693501422117365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250964597080924668562823153 188223447810693501422117365)
    ·
      refine ⟨17645948232252515758323503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188223447810693501422117365 17645948232252515758323503)
      ·
        refine ⟨26468922348378773637485255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17645948232252515758323503 26468922348378773637485255)
        ·
          refine ⟨39703383522568160456227883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26468922348378773637485255 39703383522568160456227883)
          ·
            refine ⟨59555075283852240684341825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39703383522568160456227883 59555075283852240684341825)
            ·
              refine ⟨44666306462889180513256369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59555075283852240684341825 44666306462889180513256369)
              ·
                refine ⟨33499729847166885384942277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44666306462889180513256369 33499729847166885384942277)
                ·
                  refine ⟨6281199346343791009676677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33499729847166885384942277 6281199346343791009676677)
                  ·
                    refine ⟨1177724877439460814314377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281199346343791009676677 1177724877439460814314377)
                    ·
                      rfl

theorem cell23_6880833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 4].length) (baseStart_6880833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880833 prefixEnd_6880833 := by exact prefixLift 6880833
  have htrace : WordTrace (prefixWord ++ tailWord_6880833) baseStart_6880833 baseEnd_6880833 := by
    simpa [prefixWord, tailWord_6880833, baseEnd_6880833] using wordTrace_append hprefix tailTrace_6880833
  have hstable : (prefixWord ++ tailWord_6880833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880833).length < 2 ^ (prefixWord ++ tailWord_6880833).sum := by decide
  have hdescent : baseEnd_6880833 < baseStart_6880833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880850 : List Nat := [3, 2, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_6880850 : Nat := 118140960795 + 6880850 * 2 ^ 59
def prefixEnd_6880850 : Nat := 4983230072969 + 3 ^ 40 * 6880850 * 2
def baseEnd_6880850 : Nat := 1177727787163169625476851

theorem tailTrace_6880850 : CollatzResearch.WordTrace tailWord_6880850 prefixEnd_6880850 1177727787163169625476851 := by
  unfold tailWord_6880850
  simp only [CollatzResearch.WordTrace]
  refine ⟨62741304280465770116548001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167310144747908720310794669 62741304280465770116548001)
  ·
    refine ⟨47055978210349327587411001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62741304280465770116548001 47055978210349327587411001)
    ·
      refine ⟨35291983657761995690558251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47055978210349327587411001 35291983657761995690558251)
      ·
        refine ⟨52937975486642993535837377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35291983657761995690558251 52937975486642993535837377)
        ·
          refine ⟨39703481614982245151878033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52937975486642993535837377 39703481614982245151878033)
          ·
            refine ⟨29777611211236683863908525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39703481614982245151878033 29777611211236683863908525)
            ·
              refine ⟨11166604204213756448965697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29777611211236683863908525 11166604204213756448965697)
              ·
                refine ⟨8374953153160317336724273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11166604204213756448965697 8374953153160317336724273)
                ·
                  refine ⟨6281214864870238002543205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8374953153160317336724273 6281214864870238002543205)
                  ·
                    refine ⟨1177727787163169625476851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281214864870238002543205 1177727787163169625476851)
                    ·
                      rfl

theorem cell23_6880850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_6880850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880850 prefixEnd_6880850 := by exact prefixLift 6880850
  have htrace : WordTrace (prefixWord ++ tailWord_6880850) baseStart_6880850 baseEnd_6880850 := by
    simpa [prefixWord, tailWord_6880850, baseEnd_6880850] using wordTrace_append hprefix tailTrace_6880850
  have hstable : (prefixWord ++ tailWord_6880850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880850).length < 2 ^ (prefixWord ++ tailWord_6880850).sum := by decide
  have hdescent : baseEnd_6880850 < baseStart_6880850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880873 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 3]
def baseStart_6880873 : Nat := 118140960795 + 6880873 * 2 ^ 59
def prefixEnd_6880873 : Nat := 4983230072969 + 3 ^ 40 * 6880873 * 2
def baseEnd_6880873 : Nat := 3533195171544562286442947

theorem tailTrace_6880873 : CollatzResearch.WordTrace tailWord_6880873 prefixEnd_6880873 3533195171544562286442947 := by
  unfold tailWord_6880873
  simp only [CollatzResearch.WordTrace]
  refine ⟨250966056000779755394279273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167310704000519836929519515 250966056000779755394279273)
  ·
    refine ⟨188224542000584816545709455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250966056000779755394279273 188224542000584816545709455)
    ·
      refine ⟨282336813000877224818564183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188224542000584816545709455 282336813000877224818564183)
      ·
        refine ⟨423505219501315837227846275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282336813000877224818564183 423505219501315837227846275)
        ·
          refine ⟨635257829251973755841769413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423505219501315837227846275 635257829251973755841769413)
          ·
            refine ⟨119110842984745079220331765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 635257829251973755841769413 119110842984745079220331765)
            ·
              refine ⟨11166641529819851176906103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119110842984745079220331765 11166641529819851176906103)
              ·
                refine ⟨16749962294729776765359155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166641529819851176906103 16749962294729776765359155)
                ·
                  refine ⟨25124943442094665148038733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16749962294729776765359155 25124943442094665148038733)
                  ·
                    refine ⟨9421853790785499430514525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25124943442094665148038733 9421853790785499430514525)
                    ·
                      refine ⟨3533195171544562286442947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421853790785499430514525 3533195171544562286442947)
                      ·
                        rfl

theorem cell23_6880873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 1, 3, 3].length) (baseStart_6880873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880873 prefixEnd_6880873 := by exact prefixLift 6880873
  have htrace : WordTrace (prefixWord ++ tailWord_6880873) baseStart_6880873 baseEnd_6880873 := by
    simpa [prefixWord, tailWord_6880873, baseEnd_6880873] using wordTrace_append hprefix tailTrace_6880873
  have hstable : (prefixWord ++ tailWord_6880873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880873).length < 2 ^ (prefixWord ++ tailWord_6880873).sum := by decide
  have hdescent : baseEnd_6880873 < baseStart_6880873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880877 : List Nat := [1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_6880877 : Nat := 118140960795 + 6880877 * 2 ^ 59
def prefixEnd_6880877 : Nat := 4983230072969 + 3 ^ 40 * 6880877 * 2
def baseEnd_6880877 : Nat := 3533197225467180270792929

theorem tailTrace_6880877 : CollatzResearch.WordTrace tailWord_6880877 prefixEnd_6880877 3533197225467180270792929 := by
  unfold tailWord_6880877
  simp only [CollatzResearch.WordTrace]
  refine ⟨250966201892765264077424885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167310801261843509384949923 250966201892765264077424885)
  ·
    refine ⟨23528081427446743507258583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 250966201892765264077424885 23528081427446743507258583)
    ·
      refine ⟨35292122141170115260887875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23528081427446743507258583 35292122141170115260887875)
      ·
        refine ⟨52938183211755172891331813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35292122141170115260887875 52938183211755172891331813)
        ·
          refine ⟨9925909352204094917124715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52938183211755172891331813 9925909352204094917124715)
          ·
            refine ⟨14888864028306142375687073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9925909352204094917124715 14888864028306142375687073)
            ·
              refine ⟨11166648021229606781765305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14888864028306142375687073 11166648021229606781765305)
              ·
                refine ⟨8374986015922205086323979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11166648021229606781765305 8374986015922205086323979)
                ·
                  refine ⟨12562479023883307629485969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8374986015922205086323979 12562479023883307629485969)
                  ·
                    refine ⟨9421859267912480722114477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12562479023883307629485969 9421859267912480722114477)
                    ·
                      refine ⟨3533197225467180270792929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9421859267912480722114477 3533197225467180270792929)
                      ·
                        rfl

theorem cell23_6880877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_6880877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880877 prefixEnd_6880877 := by exact prefixLift 6880877
  have htrace : WordTrace (prefixWord ++ tailWord_6880877) baseStart_6880877 baseEnd_6880877 := by
    simpa [prefixWord, tailWord_6880877, baseEnd_6880877] using wordTrace_append hprefix tailTrace_6880877
  have hstable : (prefixWord ++ tailWord_6880877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880877).length < 2 ^ (prefixWord ++ tailWord_6880877).sum := by decide
  have hdescent : baseEnd_6880877 < baseStart_6880877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880883 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 7, 3, 2]
def baseStart_6880883 : Nat := 118140960795 + 6880883 * 2 ^ 59
def prefixEnd_6880883 : Nat := 4983230072969 + 3 ^ 40 * 6880883 * 2
def baseEnd_6880883 : Nat := 3533200306351107247317901

theorem tailTrace_6880883 : CollatzResearch.WordTrace tailWord_6880883 prefixEnd_6880883 3533200306351107247317901 := by
  unfold tailWord_6880883
  simp only [CollatzResearch.WordTrace]
  refine ⟨250966420730743527102143303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167310947153829018068095535 250966420730743527102143303)
  ·
    refine ⟨376449631096115290653214955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250966420730743527102143303 376449631096115290653214955)
    ·
      refine ⟨564674446644172935979822433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376449631096115290653214955 564674446644172935979822433)
      ·
        refine ⟨423505834983129701984866825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564674446644172935979822433 423505834983129701984866825)
        ·
          refine ⟨317629376237347276488650119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423505834983129701984866825 317629376237347276488650119)
          ·
            refine ⟨476444064356020914732975179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317629376237347276488650119 476444064356020914732975179)
            ·
              refine ⟨714666096534031372099462769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476444064356020914732975179 714666096534031372099462769)
              ·
                refine ⟨535999572400523529074597077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714666096534031372099462769 535999572400523529074597077)
                ·
                  refine ⟨12562489978137270212685869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 535999572400523529074597077 12562489978137270212685869)
                  ·
                    refine ⟨4710933741801476329757201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12562489978137270212685869 4710933741801476329757201)
                    ·
                      refine ⟨3533200306351107247317901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710933741801476329757201 3533200306351107247317901)
                      ·
                        rfl

theorem cell23_6880883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 3, 2].length) (baseStart_6880883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880883 prefixEnd_6880883 := by exact prefixLift 6880883
  have htrace : WordTrace (prefixWord ++ tailWord_6880883) baseStart_6880883 baseEnd_6880883 := by
    simpa [prefixWord, tailWord_6880883, baseEnd_6880883] using wordTrace_append hprefix tailTrace_6880883
  have hstable : (prefixWord ++ tailWord_6880883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880883).length < 2 ^ (prefixWord ++ tailWord_6880883).sum := by decide
  have hdescent : baseEnd_6880883 < baseStart_6880883 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880913 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 5, 4, 2]
def baseStart_6880913 : Nat := 118140960795 + 6880913 * 2 ^ 59
def prefixEnd_6880913 : Nat := 4983230072969 + 3 ^ 40 * 6880913 * 2
def baseEnd_6880913 : Nat := 3533215710770742129942763

theorem tailTrace_6880913 : CollatzResearch.WordTrace tailWord_6880913 prefixEnd_6880913 3533215710770742129942763 := by
  unfold tailWord_6880913
  simp only [CollatzResearch.WordTrace]
  refine ⟨250967514920634842225735393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167311676613756561483823595 250967514920634842225735393)
  ·
    refine ⟨188225636190476131669301545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250967514920634842225735393 188225636190476131669301545)
    ·
      refine ⟨141169227142857098751976159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188225636190476131669301545 141169227142857098751976159)
      ·
        refine ⟨211753840714285648127964239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141169227142857098751976159 211753840714285648127964239)
        ·
          refine ⟨317630761071428472191946359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211753840714285648127964239 317630761071428472191946359)
          ·
            refine ⟨476446141607142708287919539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317630761071428472191946359 476446141607142708287919539)
            ·
              refine ⟨714669212410714062431879309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476446141607142708287919539 714669212410714062431879309)
              ·
                refine ⟨268000954654017773411954741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 714669212410714062431879309 268000954654017773411954741)
                ·
                  refine ⟨25125089498814166257370757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 268000954654017773411954741 25125089498814166257370757)
                  ·
                    refine ⟨4710954281027656173257017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25125089498814166257370757 4710954281027656173257017)
                    ·
                      refine ⟨3533215710770742129942763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710954281027656173257017 3533215710770742129942763)
                      ·
                        rfl

theorem cell23_6880913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 4, 2].length) (baseStart_6880913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880913 prefixEnd_6880913 := by exact prefixLift 6880913
  have htrace : WordTrace (prefixWord ++ tailWord_6880913) baseStart_6880913 baseEnd_6880913 := by
    simpa [prefixWord, tailWord_6880913, baseEnd_6880913] using wordTrace_append hprefix tailTrace_6880913
  have hstable : (prefixWord ++ tailWord_6880913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880913).length < 2 ^ (prefixWord ++ tailWord_6880913).sum := by decide
  have hdescent : baseEnd_6880913 < baseStart_6880913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880964 : List Nat := [2, 3, 3, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_6880964 : Nat := 118140960795 + 6880964 * 2 ^ 59
def prefixEnd_6880964 : Nat := 4983230072969 + 3 ^ 40 * 6880964 * 2
def baseEnd_6880964 : Nat := 3533241898284121430405029

theorem tailTrace_6880964 : CollatzResearch.WordTrace tailWord_6880964 prefixEnd_6880964 3533241898284121430405029 := by
  unfold tailWord_6880964
  simp only [CollatzResearch.WordTrace]
  refine ⟨125484687521725038967920973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167312916695633385290561297 125484687521725038967920973)
  ·
    refine ⟨47056757820646889612970365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125484687521725038967920973 47056757820646889612970365)
    ·
      refine ⟨17646284182742583604863887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47056757820646889612970365 17646284182742583604863887)
      ·
        refine ⟨26469426274113875407295831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17646284182742583604863887 26469426274113875407295831)
        ·
          refine ⟨39704139411170813110943747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26469426274113875407295831 39704139411170813110943747)
          ·
            refine ⟨59556209116756219666415621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39704139411170813110943747 59556209116756219666415621)
            ·
              refine ⟨11166789209391791187452929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59556209116756219666415621 11166789209391791187452929)
              ·
                refine ⟨8375091907043843390589697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11166789209391791187452929 8375091907043843390589697)
                ·
                  refine ⟨6281318930282882542942273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8375091907043843390589697 6281318930282882542942273)
                  ·
                    refine ⟨4710989197712161907206705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6281318930282882542942273 4710989197712161907206705)
                    ·
                      refine ⟨3533241898284121430405029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4710989197712161907206705 3533241898284121430405029)
                      ·
                        rfl

theorem cell23_6880964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_6880964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880964 prefixEnd_6880964 := by exact prefixLift 6880964
  have htrace : WordTrace (prefixWord ++ tailWord_6880964) baseStart_6880964 baseEnd_6880964 := by
    simpa [prefixWord, tailWord_6880964, baseEnd_6880964] using wordTrace_append hprefix tailTrace_6880964
  have hstable : (prefixWord ++ tailWord_6880964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880964).length < 2 ^ (prefixWord ++ tailWord_6880964).sum := by decide
  have hdescent : baseEnd_6880964 < baseStart_6880964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880976 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7]
def baseStart_6880976 : Nat := 118140960795 + 6880976 * 2 ^ 59
def prefixEnd_6880976 : Nat := 4983230072969 + 3 ^ 40 * 6880976 * 2
def baseEnd_6880976 : Nat := 3533248060051975383454973

theorem tailTrace_6880976 : CollatzResearch.WordTrace tailWord_6880976 prefixEnd_6880976 3533248060051975383454973 := by
  unfold tailWord_6880976
  simp only [CollatzResearch.WordTrace]
  refine ⟨125484906359703301992639391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167313208479604402656852521 125484906359703301992639391)
  ·
    refine ⟨188227359539554952988959087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125484906359703301992639391 188227359539554952988959087)
    ·
      refine ⟨282341039309332429483438631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188227359539554952988959087 282341039309332429483438631)
      ·
        refine ⟨423511558963998644225157947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282341039309332429483438631 423511558963998644225157947)
        ·
          refine ⟨635267338445997966337736921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423511558963998644225157947 635267338445997966337736921)
          ·
            refine ⟨476450503834498474753302691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635267338445997966337736921 476450503834498474753302691)
            ·
              refine ⟨714675755751747712129954037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476450503834498474753302691 714675755751747712129954037)
              ·
                refine ⟨67000852101726348012183191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 714675755751747712129954037 67000852101726348012183191)
                ·
                  refine ⟨100501278152589522018274787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67000852101726348012183191 100501278152589522018274787)
                  ·
                    refine ⟨150751917228884283027412181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 100501278152589522018274787 150751917228884283027412181)
                    ·
                      refine ⟨3533248060051975383454973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150751917228884283027412181 3533248060051975383454973)
                      ·
                        rfl

theorem cell23_6880976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_6880976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880976 prefixEnd_6880976 := by exact prefixLift 6880976
  have htrace : WordTrace (prefixWord ++ tailWord_6880976) baseStart_6880976 baseEnd_6880976 := by
    simpa [prefixWord, tailWord_6880976, baseEnd_6880976] using wordTrace_append hprefix tailTrace_6880976
  have hstable : (prefixWord ++ tailWord_6880976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880976).length < 2 ^ (prefixWord ++ tailWord_6880976).sum := by decide
  have hdescent : baseEnd_6880976 < baseStart_6880976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6880980 : List Nat := [2, 4, 1, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6880980 : Nat := 118140960795 + 6880980 * 2 ^ 59
def prefixEnd_6880980 : Nat := 4983230072969 + 3 ^ 40 * 6880980 * 2
def baseEnd_6880980 : Nat := 3533250113974593367804955

theorem tailTrace_6880980 : CollatzResearch.WordTrace tailWord_6880980 prefixEnd_6880980 3533250113974593367804955 := by
  unfold tailWord_6880980
  simp only [CollatzResearch.WordTrace]
  refine ⟨125484979305696056334212197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167313305740928075112282929 125484979305696056334212197)
  ·
    refine ⟨23528433619818010562664787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125484979305696056334212197 23528433619818010562664787)
    ·
      refine ⟨35292650429727015843997181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23528433619818010562664787 35292650429727015843997181)
      ·
        refine ⟨13234743911147630941498943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35292650429727015843997181 13234743911147630941498943)
        ·
          refine ⟨19852115866721446412248415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234743911147630941498943 19852115866721446412248415)
          ·
            refine ⟨29778173800082169618372623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19852115866721446412248415 29778173800082169618372623)
            ·
              refine ⟨44667260700123254427558935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29778173800082169618372623 44667260700123254427558935)
              ·
                refine ⟨67000891050184881641338403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44667260700123254427558935 67000891050184881641338403)
                ·
                  refine ⟨100501336575277322462007605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67000891050184881641338403 100501336575277322462007605)
                  ·
                    refine ⟨9422000303932248980813213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100501336575277322462007605 9422000303932248980813213)
                    ·
                      refine ⟨3533250113974593367804955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9422000303932248980813213 3533250113974593367804955)
                      ·
                        rfl

theorem cell23_6880980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6880980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6880980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6880980 prefixEnd_6880980 := by exact prefixLift 6880980
  have htrace : WordTrace (prefixWord ++ tailWord_6880980) baseStart_6880980 baseEnd_6880980 := by
    simpa [prefixWord, tailWord_6880980, baseEnd_6880980] using wordTrace_append hprefix tailTrace_6880980
  have hstable : (prefixWord ++ tailWord_6880980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6880980).length < 2 ^ (prefixWord ++ tailWord_6880980).sum := by decide
  have hdescent : baseEnd_6880980 < baseStart_6880980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6880980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881000 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 2, 5]
def baseStart_6881000 : Nat := 118140960795 + 6881000 * 2 ^ 59
def prefixEnd_6881000 : Nat := 4983230072969 + 3 ^ 40 * 6881000 * 2
def baseEnd_6881000 : Nat := 1177753461195894429851621

theorem tailTrace_6881000 : CollatzResearch.WordTrace tailWord_6881000 prefixEnd_6881000 1177753461195894429851621 := by
  unfold tailWord_6881000
  simp only [CollatzResearch.WordTrace]
  refine ⟨125485344035659828042076227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167313792047546437389434969 125485344035659828042076227)
  ·
    refine ⟨188228016053489742063114341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125485344035659828042076227 188228016053489742063114341)
    ·
      refine ⟨35292753010029326636833939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188228016053489742063114341 35292753010029326636833939)
      ·
        refine ⟨52939129515043989955250909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35292753010029326636833939 52939129515043989955250909)
        ·
          refine ⟨19852173568141496233219091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52939129515043989955250909 19852173568141496233219091)
          ·
            refine ⟨29778260352212244349828637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19852173568141496233219091 29778260352212244349828637)
            ·
              refine ⟨11166847632079591631185739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29778260352212244349828637 11166847632079591631185739)
              ·
                refine ⟨16750271448119387446778609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166847632079591631185739 16750271448119387446778609)
                ·
                  refine ⟨12562703586089540585083957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16750271448119387446778609 12562703586089540585083957)
                  ·
                    refine ⟨1177753461195894429851621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12562703586089540585083957 1177753461195894429851621)
                    ·
                      rfl

theorem cell23_6881000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_6881000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881000 prefixEnd_6881000 := by exact prefixLift 6881000
  have htrace : WordTrace (prefixWord ++ tailWord_6881000) baseStart_6881000 baseEnd_6881000 := by
    simpa [prefixWord, tailWord_6881000, baseEnd_6881000] using wordTrace_append hprefix tailTrace_6881000
  have hstable : (prefixWord ++ tailWord_6881000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881000).length < 2 ^ (prefixWord ++ tailWord_6881000).sum := by decide
  have hdescent : baseEnd_6881000 < baseStart_6881000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881020 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_6881020 : Nat := 118140960795 + 6881020 * 2 ^ 59
def prefixEnd_6881020 : Nat := 4983230072969 + 3 ^ 40 * 6881020 * 2
def baseEnd_6881020 : Nat := 3533270653200773211304771

theorem tailTrace_6881020 : CollatzResearch.WordTrace tailWord_6881020 prefixEnd_6881020 3533270653200773211304771 := by
  unfold tailWord_6881020
  simp only [CollatzResearch.WordTrace]
  refine ⟨125485708765623599749940257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167314278354164799666587009 125485708765623599749940257)
  ·
    refine ⟨94114281574217699812455193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125485708765623599749940257 94114281574217699812455193)
    ·
      refine ⟨70585711180663274859341395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94114281574217699812455193 70585711180663274859341395)
      ·
        refine ⟨105878566770994912289012093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70585711180663274859341395 105878566770994912289012093)
        ·
          refine ⟨39704462539123092108379535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105878566770994912289012093 39704462539123092108379535)
          ·
            refine ⟨59556693808684638162569303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39704462539123092108379535 59556693808684638162569303)
            ·
              refine ⟨89335040713026957243853955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59556693808684638162569303 89335040713026957243853955)
              ·
                refine ⟨134002561069540435865780933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89335040713026957243853955 134002561069540435865780933)
                ·
                  refine ⟨25125480200538831724833925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134002561069540435865780933 25125480200538831724833925)
                  ·
                    refine ⟨4711027537601030948406361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25125480200538831724833925 4711027537601030948406361)
                    ·
                      refine ⟨3533270653200773211304771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711027537601030948406361 3533270653200773211304771)
                      ·
                        rfl

theorem cell23_6881020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_6881020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881020 prefixEnd_6881020 := by exact prefixLift 6881020
  have htrace : WordTrace (prefixWord ++ tailWord_6881020) baseStart_6881020 baseEnd_6881020 := by
    simpa [prefixWord, tailWord_6881020, baseEnd_6881020] using wordTrace_append hprefix tailTrace_6881020
  have hstable : (prefixWord ++ tailWord_6881020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881020).length < 2 ^ (prefixWord ++ tailWord_6881020).sum := by decide
  have hdescent : baseEnd_6881020 < baseStart_6881020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881064 : List Nat := [2, 1, 5, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6881064 : Nat := 118140960795 + 6881064 * 2 ^ 59
def prefixEnd_6881064 : Nat := 4983230072969 + 3 ^ 40 * 6881064 * 2
def baseEnd_6881064 : Nat := 1177764415449857013051523

theorem tailTrace_6881064 : CollatzResearch.WordTrace tailWord_6881064 prefixEnd_6881064 1177764415449857013051523 := by
  unfold tailWord_6881064
  simp only [CollatzResearch.WordTrace]
  refine ⟨125486511171543897507241123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167315348228725196676321497 125486511171543897507241123)
  ·
    refine ⟨188229766757315846260861685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125486511171543897507241123 188229766757315846260861685)
    ·
      refine ⟨17646540633498360586955783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188229766757315846260861685 17646540633498360586955783)
      ·
        refine ⟨26469810950247540880433675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17646540633498360586955783 26469810950247540880433675)
        ·
          refine ⟨39704716425371311320650513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26469810950247540880433675 39704716425371311320650513)
          ·
            refine ⟨29778537319028483490487885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39704716425371311320650513 29778537319028483490487885)
            ·
              refine ⟨11166951494635681308932957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29778537319028483490487885 11166951494635681308932957)
              ·
                refine ⟨4187606810488380490849859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11166951494635681308932957 4187606810488380490849859)
                ·
                  refine ⟨6281410215732570736274789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187606810488380490849859 6281410215732570736274789)
                  ·
                    refine ⟨1177764415449857013051523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281410215732570736274789 1177764415449857013051523)
                    ·
                      rfl

theorem cell23_6881064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6881064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881064 prefixEnd_6881064 := by exact prefixLift 6881064
  have htrace : WordTrace (prefixWord ++ tailWord_6881064) baseStart_6881064 baseEnd_6881064 := by
    simpa [prefixWord, tailWord_6881064, baseEnd_6881064] using wordTrace_append hprefix tailTrace_6881064
  have hstable : (prefixWord ++ tailWord_6881064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881064).length < 2 ^ (prefixWord ++ tailWord_6881064).sum := by decide
  have hdescent : baseEnd_6881064 < baseStart_6881064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881081 : List Nat := [1, 2, 1, 7, 2, 1, 1, 1, 3, 4]
def baseStart_6881081 : Nat := 118140960795 + 6881081 * 2 ^ 59
def prefixEnd_6881081 : Nat := 4983230072969 + 3 ^ 40 * 6881081 * 2
def baseEnd_6881081 : Nat := 1177767325173565824213997

theorem tailTrace_6881081 : CollatzResearch.WordTrace tailWord_6881081 prefixEnd_6881081 1177767325173565824213997 := by
  unfold tailWord_6881081
  simp only [CollatzResearch.WordTrace]
  refine ⟨250973642384026206917851097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167315761589350804611900731 250973642384026206917851097)
  ·
    refine ⟨188230231788019655188388323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250973642384026206917851097 188230231788019655188388323)
    ·
      refine ⟨282345347682029482782582485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188230231788019655188388323 282345347682029482782582485)
      ·
        refine ⟨6617469086297566002716777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 282345347682029482782582485 6617469086297566002716777)
        ·
          refine ⟨4963101814723174502037583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6617469086297566002716777 4963101814723174502037583)
          ·
            refine ⟨7444652722084761753056375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963101814723174502037583 7444652722084761753056375)
            ·
              refine ⟨11166979083127142629584563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7444652722084761753056375 11166979083127142629584563)
              ·
                refine ⟨16750468624690713944376845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11166979083127142629584563 16750468624690713944376845)
                ·
                  refine ⟨6281425734259017729141317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16750468624690713944376845 6281425734259017729141317)
                  ·
                    refine ⟨1177767325173565824213997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281425734259017729141317 1177767325173565824213997)
                    ·
                      rfl

theorem cell23_6881081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 1, 3, 4].length) (baseStart_6881081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881081 prefixEnd_6881081 := by exact prefixLift 6881081
  have htrace : WordTrace (prefixWord ++ tailWord_6881081) baseStart_6881081 baseEnd_6881081 := by
    simpa [prefixWord, tailWord_6881081, baseEnd_6881081] using wordTrace_append hprefix tailTrace_6881081
  have hstable : (prefixWord ++ tailWord_6881081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881081).length < 2 ^ (prefixWord ++ tailWord_6881081).sum := by decide
  have hdescent : baseEnd_6881081 < baseStart_6881081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881094 : List Nat := [6, 1, 1, 2, 1, 2, 1, 3, 6]
def baseStart_6881094 : Nat := 118140960795 + 6881094 * 2 ^ 59
def prefixEnd_6881094 : Nat := 4983230072969 + 3 ^ 40 * 6881094 * 2
def baseEnd_6881094 : Nat := 392589850085467324642159

theorem tailTrace_6881094 : CollatzResearch.WordTrace tailWord_6881094 prefixEnd_6881094 392589850085467324642159 := by
  unfold tailWord_6881094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7842941141655597191814823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167316077688652740092049557 7842941141655597191814823)
  ·
    refine ⟨11764411712483395787722235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7842941141655597191814823 11764411712483395787722235)
    ·
      refine ⟨17646617568725093681583353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11764411712483395787722235 17646617568725093681583353)
      ·
        refine ⟨13234963176543820261187515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17646617568725093681583353 13234963176543820261187515)
        ·
          refine ⟨19852444764815730391781273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13234963176543820261187515 19852444764815730391781273)
          ·
            refine ⟨14889333573611797793835955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19852444764815730391781273 14889333573611797793835955)
            ·
              refine ⟨22334000360417696690753933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14889333573611797793835955 22334000360417696690753933)
              ·
                refine ⟨8375250135156636259032725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22334000360417696690753933 8375250135156636259032725)
                ·
                  refine ⟨392589850085467324642159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8375250135156636259032725 392589850085467324642159)
                  ·
                    rfl

theorem cell23_6881094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_6881094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881094 prefixEnd_6881094 := by exact prefixLift 6881094
  have htrace : WordTrace (prefixWord ++ tailWord_6881094) baseStart_6881094 baseEnd_6881094 := by
    simpa [prefixWord, tailWord_6881094, baseEnd_6881094] using wordTrace_append hprefix tailTrace_6881094
  have hstable : (prefixWord ++ tailWord_6881094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881094).length < 2 ^ (prefixWord ++ tailWord_6881094).sum := by decide
  have hdescent : baseEnd_6881094 < baseStart_6881094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881120 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 1, 6]
def baseStart_6881120 : Nat := 118140960795 + 6881120 * 2 ^ 59
def prefixEnd_6881120 : Nat := 4983230072969 + 3 ^ 40 * 6881120 * 2
def baseEnd_6881120 : Nat := 1177774000422074273351437

theorem tailTrace_6881120 : CollatzResearch.WordTrace tailWord_6881120 prefixEnd_6881120 1177774000422074273351437 := by
  unfold tailWord_6881120
  simp only [CollatzResearch.WordTrace]
  refine ⟨125487532415442458289260407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167316709887256611052347209 125487532415442458289260407)
  ·
    refine ⟨188231298623163687433890611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125487532415442458289260407 188231298623163687433890611)
    ·
      refine ⟨282346947934745531150835917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188231298623163687433890611 282346947934745531150835917)
      ·
        refine ⟨105880105475529574181563469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282346947934745531150835917 105880105475529574181563469)
        ·
          refine ⟨39705039553323590318086301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105880105475529574181563469 39705039553323590318086301)
          ·
            refine ⟨14889389832496346369282363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39705039553323590318086301 14889389832496346369282363)
            ·
              refine ⟨22334084748744519553923545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14889389832496346369282363 22334084748744519553923545)
              ·
                refine ⟨16750563561558389665442659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22334084748744519553923545 16750563561558389665442659)
                ·
                  refine ⟨25125845342337584498163989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16750563561558389665442659 25125845342337584498163989)
                  ·
                    refine ⟨1177774000422074273351437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25125845342337584498163989 1177774000422074273351437)
                    ·
                      rfl

theorem cell23_6881120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 1, 6].length) (baseStart_6881120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881120 prefixEnd_6881120 := by exact prefixLift 6881120
  have htrace : WordTrace (prefixWord ++ tailWord_6881120) baseStart_6881120 baseEnd_6881120 := by
    simpa [prefixWord, tailWord_6881120, baseEnd_6881120] using wordTrace_append hprefix tailTrace_6881120
  have hstable : (prefixWord ++ tailWord_6881120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881120).length < 2 ^ (prefixWord ++ tailWord_6881120).sum := by decide
  have hdescent : baseEnd_6881120 < baseStart_6881120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881124 : List Nat := [2, 3, 1, 1, 5, 1, 3, 1, 1, 5]
def baseStart_6881124 : Nat := 118140960795 + 6881124 * 2 ^ 59
def prefixEnd_6881124 : Nat := 4983230072969 + 3 ^ 40 * 6881124 * 2
def baseEnd_6881124 : Nat := 1177774685062946934801431

theorem tailTrace_6881124 : CollatzResearch.WordTrace tailWord_6881124 prefixEnd_6881124 1177774685062946934801431 := by
  unfold tailWord_6881124
  simp only [CollatzResearch.WordTrace]
  refine ⟨125487605361435212630833213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167316807148580283507777617 125487605361435212630833213)
  ·
    refine ⟨47057852010538204736562455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125487605361435212630833213 47057852010538204736562455)
    ·
      refine ⟨70586778015807307104843683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47057852010538204736562455 70586778015807307104843683)
      ·
        refine ⟨105880167023710960657265525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70586778015807307104843683 105880167023710960657265525)
        ·
          refine ⟨9926265658472902561618643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105880167023710960657265525 9926265658472902561618643)
          ·
            refine ⟨14889398487709353842427965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926265658472902561618643 14889398487709353842427965)
            ·
              refine ⟨5583524432891007690910487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14889398487709353842427965 5583524432891007690910487)
              ·
                refine ⟨8375286649336511536365731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583524432891007690910487 8375286649336511536365731)
                ·
                  refine ⟨12562929974004767304548597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8375286649336511536365731 12562929974004767304548597)
                  ·
                    refine ⟨1177774685062946934801431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12562929974004767304548597 1177774685062946934801431)
                    ·
                      rfl

theorem cell23_6881124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 1, 1, 5].length) (baseStart_6881124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881124 prefixEnd_6881124 := by exact prefixLift 6881124
  have htrace : WordTrace (prefixWord ++ tailWord_6881124) baseStart_6881124 baseEnd_6881124 := by
    simpa [prefixWord, tailWord_6881124, baseEnd_6881124] using wordTrace_append hprefix tailTrace_6881124
  have hstable : (prefixWord ++ tailWord_6881124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881124).length < 2 ^ (prefixWord ++ tailWord_6881124).sum := by decide
  have hdescent : baseEnd_6881124 < baseStart_6881124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881137 : List Nat := [1, 2, 2, 2, 1, 3, 4, 2, 2, 4]
def baseStart_6881137 : Nat := 118140960795 + 6881137 * 2 ^ 59
def prefixEnd_6881137 : Nat := 4983230072969 + 3 ^ 40 * 6881137 * 2
def baseEnd_6881137 : Nat := 1177776910145783084513911

theorem tailTrace_6881137 : CollatzResearch.WordTrace tailWord_6881137 prefixEnd_6881137 1177776910145783084513911 := by
  unfold tailWord_6881137
  simp only [CollatzResearch.WordTrace]
  refine ⟨250975684871823328481889665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167317123247882218987926443 250975684871823328481889665)
  ·
    refine ⟨188231763653867496361417249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250975684871823328481889665 188231763653867496361417249)
    ·
      refine ⟨141173822740400622271062937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188231763653867496361417249 141173822740400622271062937)
      ·
        refine ⟨105880367055300466703297203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141173822740400622271062937 105880367055300466703297203)
        ·
          refine ⟨158820550582950700054945805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105880367055300466703297203 158820550582950700054945805)
          ·
            refine ⟨59557706468606512520604677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158820550582950700054945805 59557706468606512520604677)
            ·
              refine ⟨11167069962863721097613377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59557706468606512520604677 11167069962863721097613377)
              ·
                refine ⟨8375302472147790823210033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11167069962863721097613377 8375302472147790823210033)
                ·
                  refine ⟨6281476854110843117407525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8375302472147790823210033 6281476854110843117407525)
                  ·
                    refine ⟨1177776910145783084513911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281476854110843117407525 1177776910145783084513911)
                    ·
                      rfl

theorem cell23_6881137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 4].length) (baseStart_6881137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881137 prefixEnd_6881137 := by exact prefixLift 6881137
  have htrace : WordTrace (prefixWord ++ tailWord_6881137) baseStart_6881137 baseEnd_6881137 := by
    simpa [prefixWord, tailWord_6881137, baseEnd_6881137] using wordTrace_append hprefix tailTrace_6881137
  have hstable : (prefixWord ++ tailWord_6881137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881137).length < 2 ^ (prefixWord ++ tailWord_6881137).sum := by decide
  have hdescent : baseEnd_6881137 < baseStart_6881137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881163 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 4, 7]
def baseStart_6881163 : Nat := 118140960795 + 6881163 * 2 ^ 59
def prefixEnd_6881163 : Nat := 4983230072969 + 3 ^ 40 * 6881163 * 2
def baseEnd_6881163 : Nat := 1177781360311455383938871

theorem tailTrace_6881163 : CollatzResearch.WordTrace tailWord_6881163 prefixEnd_6881163 1177781360311455383938871 := by
  unfold tailWord_6881163
  simp only [CollatzResearch.WordTrace]
  refine ⟨250976633169729134922336143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167317755446486089948224095 250976633169729134922336143)
  ·
    refine ⟨376464949754593702383504215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250976633169729134922336143 376464949754593702383504215)
    ·
      refine ⟨564697424631890553575256323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376464949754593702383504215 564697424631890553575256323)
      ·
        refine ⟨847046136947835830362884485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564697424631890553575256323 847046136947835830362884485)
        ·
          refine ⟨158821150677719218193040841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 847046136947835830362884485 158821150677719218193040841)
          ·
            refine ⟨119115863008289413644780631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158821150677719218193040841 119115863008289413644780631)
            ·
              refine ⟨178673794512434120467170947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119115863008289413644780631 178673794512434120467170947)
              ·
                refine ⟨268010691768651180700756421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178673794512434120467170947 268010691768651180700756421)
                ·
                  refine ⟨50252004706622096381391829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 268010691768651180700756421 50252004706622096381391829)
                  ·
                    refine ⟨1177781360311455383938871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50252004706622096381391829 1177781360311455383938871)
                    ·
                      rfl

theorem cell23_6881163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 7].length) (baseStart_6881163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881163 prefixEnd_6881163 := by exact prefixLift 6881163
  have htrace : WordTrace (prefixWord ++ tailWord_6881163) baseStart_6881163 baseEnd_6881163 := by
    simpa [prefixWord, tailWord_6881163, baseEnd_6881163] using wordTrace_append hprefix tailTrace_6881163
  have hstable : (prefixWord ++ tailWord_6881163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881163).length < 2 ^ (prefixWord ++ tailWord_6881163).sum := by decide
  have hdescent : baseEnd_6881163 < baseStart_6881163 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881178 : List Nat := [3, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2]
def baseStart_6881178 : Nat := 118140960795 + 6881178 * 2 ^ 59
def prefixEnd_6881178 : Nat := 4983230072969 + 3 ^ 40 * 6881178 * 2
def baseEnd_6881178 : Nat := 3533351783144183593129045

theorem tailTrace_6881178 : CollatzResearch.WordTrace tailWord_6881178 prefixEnd_6881178 3533351783144183593129045 := by
  unfold tailWord_6881178
  simp only [CollatzResearch.WordTrace]
  refine ⟨62744295066168698121033047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167318120176449861656088125 62744295066168698121033047)
  ·
    refine ⟨94116442599253047181549571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62744295066168698121033047 94116442599253047181549571)
    ·
      refine ⟨141174663898879570772324357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94116442599253047181549571 141174663898879570772324357)
      ·
        refine ⟨26470249481039919519810817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141174663898879570772324357 26470249481039919519810817)
        ·
          refine ⟨19852687110779939639858113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26470249481039919519810817 19852687110779939639858113)
          ·
            refine ⟨14889515333084954729893585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19852687110779939639858113 14889515333084954729893585)
            ·
              refine ⟨11167136499813716047420189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14889515333084954729893585 11167136499813716047420189)
              ·
                refine ⟨4187676187430143517782571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11167136499813716047420189 4187676187430143517782571)
                ·
                  refine ⟨6281514281145215276673857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187676187430143517782571 6281514281145215276673857)
                  ·
                    refine ⟨4711135710858911457505393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6281514281145215276673857 4711135710858911457505393)
                    ·
                      refine ⟨3533351783144183593129045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711135710858911457505393 3533351783144183593129045)
                      ·
                        rfl

theorem cell23_6881178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_6881178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881178 prefixEnd_6881178 := by exact prefixLift 6881178
  have htrace : WordTrace (prefixWord ++ tailWord_6881178) baseStart_6881178 baseEnd_6881178 := by
    simpa [prefixWord, tailWord_6881178, baseEnd_6881178] using wordTrace_append hprefix tailTrace_6881178
  have hstable : (prefixWord ++ tailWord_6881178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881178).length < 2 ^ (prefixWord ++ tailWord_6881178).sum := by decide
  have hdescent : baseEnd_6881178 < baseStart_6881178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881181 : List Nat := [1, 4, 2, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_6881181 : Nat := 118140960795 + 6881181 * 2 ^ 59
def prefixEnd_6881181 : Nat := 4983230072969 + 3 ^ 40 * 6881181 * 2
def baseEnd_6881181 : Nat := 3533353323586147081391531

theorem tailTrace_6881181 : CollatzResearch.WordTrace tailWord_6881181 prefixEnd_6881181 3533353323586147081391531 := by
  unfold tailWord_6881181
  simp only [CollatzResearch.WordTrace]
  refine ⟨250977289683663923996491397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167318193122442615997660931 250977289683663923996491397)
  ·
    refine ⟨47058241815686985749342137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250977289683663923996491397 47058241815686985749342137)
    ·
      refine ⟨35293681361765239312006603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47058241815686985749342137 35293681361765239312006603)
      ·
        refine ⟨52940522042647858968009905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35293681361765239312006603 52940522042647858968009905)
        ·
          refine ⟨39705391531985894226007429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52940522042647858968009905 39705391531985894226007429)
          ·
            refine ⟨7444760912247355167376393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39705391531985894226007429 7444760912247355167376393)
            ·
              refine ⟨5583570684185516375532295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7444760912247355167376393 5583570684185516375532295)
              ·
                refine ⟨8375356026278274563298443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5583570684185516375532295 8375356026278274563298443)
                ·
                  refine ⟨12563034039417411844947665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8375356026278274563298443 12563034039417411844947665)
                  ·
                    refine ⟨9422275529563058883710749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12563034039417411844947665 9422275529563058883710749)
                    ·
                      refine ⟨3533353323586147081391531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9422275529563058883710749 3533353323586147081391531)
                      ·
                        rfl

theorem cell23_6881181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_6881181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881181 prefixEnd_6881181 := by exact prefixLift 6881181
  have htrace : WordTrace (prefixWord ++ tailWord_6881181) baseStart_6881181 baseEnd_6881181 := by
    simpa [prefixWord, tailWord_6881181, baseEnd_6881181] using wordTrace_append hprefix tailTrace_6881181
  have hstable : (prefixWord ++ tailWord_6881181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881181).length < 2 ^ (prefixWord ++ tailWord_6881181).sum := by decide
  have hdescent : baseEnd_6881181 < baseStart_6881181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881237 : List Nat := [1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 5]
def baseStart_6881237 : Nat := 118140960795 + 6881237 * 2 ^ 59
def prefixEnd_6881237 : Nat := 4983230072969 + 3 ^ 40 * 6881237 * 2
def baseEnd_6881237 : Nat := 3533382078502798862291273

theorem tailTrace_6881237 : CollatzResearch.WordTrace tailWord_6881237 prefixEnd_6881237 3533382078502798862291273 := by
  unfold tailWord_6881237
  simp only [CollatzResearch.WordTrace]
  refine ⟨250979332171461045560529965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167319554780974030373686643 250979332171461045560529965)
  ·
    refine ⟨94117249564297892085198737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250979332171461045560529965 94117249564297892085198737)
    ·
      refine ⟨70587937173223419063899053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94117249564297892085198737 70587937173223419063899053)
      ·
        refine ⟨26470476439958782148962145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70587937173223419063899053 26470476439958782148962145)
        ·
          refine ⟨19852857329969086611721609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26470476439958782148962145 19852857329969086611721609)
          ·
            refine ⟨14889642997476814958791207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19852857329969086611721609 14889642997476814958791207)
            ·
              refine ⟨22334464496215222438186811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14889642997476814958791207 22334464496215222438186811)
              ·
                refine ⟨33501696744322833657280217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22334464496215222438186811 33501696744322833657280217)
                ·
                  refine ⟨25126272558242125242960163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33501696744322833657280217 25126272558242125242960163)
                  ·
                    refine ⟨37689408837363187864440245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25126272558242125242960163 37689408837363187864440245)
                    ·
                      refine ⟨3533382078502798862291273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37689408837363187864440245 3533382078502798862291273)
                      ·
                        rfl

theorem cell23_6881237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_6881237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881237 prefixEnd_6881237 := by exact prefixLift 6881237
  have htrace : WordTrace (prefixWord ++ tailWord_6881237) baseStart_6881237 baseEnd_6881237 := by
    simpa [prefixWord, tailWord_6881237, baseEnd_6881237] using wordTrace_append hprefix tailTrace_6881237
  have hstable : (prefixWord ++ tailWord_6881237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881237).length < 2 ^ (prefixWord ++ tailWord_6881237).sum := by decide
  have hdescent : baseEnd_6881237 < baseStart_6881237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881287 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 2, 5]
def baseStart_6881287 : Nat := 118140960795 + 6881287 * 2 ^ 59
def prefixEnd_6881287 : Nat := 4983230072969 + 3 ^ 40 * 6881287 * 2
def baseEnd_6881287 : Nat := 1177802584178507888888681

theorem tailTrace_6881287 : CollatzResearch.WordTrace tailWord_6881287 prefixEnd_6881287 1177802584178507888888681 := by
  unfold tailWord_6881287
  simp only [CollatzResearch.WordTrace]
  refine ⟨250981155821279904099850115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167320770547519936066566743 250981155821279904099850115)
  ·
    refine ⟨376471733731919856149775173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250981155821279904099850115 376471733731919856149775173)
    ·
      refine ⟨70588450074734973028082845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376471733731919856149775173 70588450074734973028082845)
      ·
        refine ⟨26470668778025614885531067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70588450074734973028082845 26470668778025614885531067)
        ·
          refine ⟨39706003167038422328296601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26470668778025614885531067 39706003167038422328296601)
          ·
            refine ⟨29779502375278816746222451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39706003167038422328296601 29779502375278816746222451)
            ·
              refine ⟨44669253562918225119333677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29779502375278816746222451 44669253562918225119333677)
              ·
                refine ⟨16750970086094334419750129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44669253562918225119333677 16750970086094334419750129)
                ·
                  refine ⟨12563227564570750814812597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16750970086094334419750129 12563227564570750814812597)
                  ·
                    refine ⟨1177802584178507888888681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12563227564570750814812597 1177802584178507888888681)
                    ·
                      rfl

theorem cell23_6881287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_6881287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881287 prefixEnd_6881287 := by exact prefixLift 6881287
  have htrace : WordTrace (prefixWord ++ tailWord_6881287) baseStart_6881287 baseEnd_6881287 := by
    simpa [prefixWord, tailWord_6881287, baseEnd_6881287] using wordTrace_append hprefix tailTrace_6881287
  have hstable : (prefixWord ++ tailWord_6881287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881287).length < 2 ^ (prefixWord ++ tailWord_6881287).sum := by decide
  have hdescent : baseEnd_6881287 < baseStart_6881287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881344 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3]
def baseStart_6881344 : Nat := 118140960795 + 6881344 * 2 ^ 59
def prefixEnd_6881344 : Nat := 4983230072969 + 3 ^ 40 * 6881344 * 2
def baseEnd_6881344 : Nat := 3533437020932829943653281

theorem tailTrace_6881344 : CollatzResearch.WordTrace tailWord_6881344 prefixEnd_6881344 3533437020932829943653281 := by
  unfold tailWord_6881344
  simp only [CollatzResearch.WordTrace]
  refine ⟨125491617391036701417337543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167322156521382268556450057 125491617391036701417337543)
  ·
    refine ⟨188237426086555052126006315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125491617391036701417337543 188237426086555052126006315)
    ·
      refine ⟨282356139129832578189009473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188237426086555052126006315 282356139129832578189009473)
      ·
        refine ⟨211767104347374433641757105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282356139129832578189009473 211767104347374433641757105)
        ·
          refine ⟨158825328260530825231317829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211767104347374433641757105 158825328260530825231317829)
          ·
            refine ⟨29779749048849529730872093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158825328260530825231317829 29779749048849529730872093)
            ·
              refine ⟨11167405893318573649077035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29779749048849529730872093 11167405893318573649077035)
              ·
                refine ⟨16751108839977860473615553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11167405893318573649077035 16751108839977860473615553)
                ·
                  refine ⟨12563331629983395355211665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16751108839977860473615553 12563331629983395355211665)
                  ·
                    refine ⟨9422498722487546516408749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12563331629983395355211665 9422498722487546516408749)
                    ·
                      refine ⟨3533437020932829943653281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9422498722487546516408749 3533437020932829943653281)
                      ·
                        rfl

theorem cell23_6881344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 2, 2, 3].length) (baseStart_6881344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881344 prefixEnd_6881344 := by exact prefixLift 6881344
  have htrace : WordTrace (prefixWord ++ tailWord_6881344) baseStart_6881344 baseEnd_6881344 := by
    simpa [prefixWord, tailWord_6881344, baseEnd_6881344] using wordTrace_append hprefix tailTrace_6881344
  have hstable : (prefixWord ++ tailWord_6881344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881344).length < 2 ^ (prefixWord ++ tailWord_6881344).sum := by decide
  have hdescent : baseEnd_6881344 < baseStart_6881344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881351 : List Nat := [1, 1, 4, 1, 3, 1, 4, 3, 1, 4]
def baseStart_6881351 : Nat := 118140960795 + 6881351 * 2 ^ 59
def prefixEnd_6881351 : Nat := 4983230072969 + 3 ^ 40 * 6881351 * 2
def baseEnd_6881351 : Nat := 1177813538432470472088583

theorem tailTrace_6881351 : CollatzResearch.WordTrace tailWord_6881351 prefixEnd_6881351 1177813538432470472088583 := by
  unfold tailWord_6881351
  simp only [CollatzResearch.WordTrace]
  refine ⟨250983490093048043030179907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167322326728698695353453271 250983490093048043030179907)
  ·
    refine ⟨376475235139572064545269861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250983490093048043030179907 376475235139572064545269861)
    ·
      refine ⟨70589106588669762102238099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376475235139572064545269861 70589106588669762102238099)
      ·
        refine ⟨105883659883004643153357149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70589106588669762102238099 105883659883004643153357149)
        ·
          refine ⟨39706372456126741182508931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105883659883004643153357149 39706372456126741182508931)
          ·
            refine ⟨59559558684190111773763397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39706372456126741182508931 59559558684190111773763397)
            ·
              refine ⟨11167417253285645957580637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59559558684190111773763397 11167417253285645957580637)
              ·
                refine ⟨4187781469982117234092739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11167417253285645957580637 4187781469982117234092739)
                ·
                  refine ⟨6281672204973175851139109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4187781469982117234092739 6281672204973175851139109)
                  ·
                    refine ⟨1177813538432470472088583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281672204973175851139109 1177813538432470472088583)
                    ·
                      rfl

theorem cell23_6881351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_6881351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881351 prefixEnd_6881351 := by exact prefixLift 6881351
  have htrace : WordTrace (prefixWord ++ tailWord_6881351) baseStart_6881351 baseEnd_6881351 := by
    simpa [prefixWord, tailWord_6881351, baseEnd_6881351] using wordTrace_append hprefix tailTrace_6881351
  have hstable : (prefixWord ++ tailWord_6881351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881351).length < 2 ^ (prefixWord ++ tailWord_6881351).sum := by decide
  have hdescent : baseEnd_6881351 < baseStart_6881351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881394 : List Nat := [3, 2, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_6881394 : Nat := 118140960795 + 6881394 * 2 ^ 59
def prefixEnd_6881394 : Nat := 4983230072969 + 3 ^ 40 * 6881394 * 2
def baseEnd_6881394 : Nat := 1177820898321851582676017

theorem tailTrace_6881394 : CollatzResearch.WordTrace tailWord_6881394 prefixEnd_6881394 1177820898321851582676017 := by
  unfold tailWord_6881394
  simp only [CollatzResearch.WordTrace]
  refine ⟨62746264607973065343498809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167323372287928174249330157 62746264607973065343498809)
  ·
    refine ⟨47059698455979799007624107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62746264607973065343498809 47059698455979799007624107)
    ·
      refine ⟨70589547683969698511436161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47059698455979799007624107 70589547683969698511436161)
      ·
        refine ⟨52942160762977273883577121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70589547683969698511436161 52942160762977273883577121)
        ·
          refine ⟨39706620572232955412682841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52942160762977273883577121 39706620572232955412682841)
          ·
            refine ⟨29779965429174716559512131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39706620572232955412682841 29779965429174716559512131)
            ·
              refine ⟨44669948143762074839268197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29779965429174716559512131 44669948143762074839268197)
              ·
                refine ⟨8375615276955389032362787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44669948143762074839268197 8375615276955389032362787)
                ·
                  refine ⟨12563422915433083548544181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8375615276955389032362787 12563422915433083548544181)
                  ·
                    refine ⟨1177820898321851582676017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12563422915433083548544181 1177820898321851582676017)
                    ·
                      rfl

theorem cell23_6881394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_6881394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881394 prefixEnd_6881394 := by exact prefixLift 6881394
  have htrace : WordTrace (prefixWord ++ tailWord_6881394) baseStart_6881394 baseEnd_6881394 := by
    simpa [prefixWord, tailWord_6881394, baseEnd_6881394] using wordTrace_append hprefix tailTrace_6881394
  have hstable : (prefixWord ++ tailWord_6881394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881394).length < 2 ^ (prefixWord ++ tailWord_6881394).sum := by decide
  have hdescent : baseEnd_6881394 < baseStart_6881394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881424 : List Nat := [2, 1, 1, 1, 1, 1, 6, 4, 2, 4]
def baseStart_6881424 : Nat := 118140960795 + 6881424 * 2 ^ 59
def prefixEnd_6881424 : Nat := 4983230072969 + 3 ^ 40 * 6881424 * 2
def baseEnd_6881424 : Nat := 1177826033128396543550971

theorem tailTrace_6881424 : CollatzResearch.WordTrace tailWord_6881424 prefixEnd_6881424 1177826033128396543550971 := by
  unfold tailWord_6881424
  simp only [CollatzResearch.WordTrace]
  refine ⟨125493076310891788248793663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167324101747855717665058217 125493076310891788248793663)
  ·
    refine ⟨188239614466337682373190495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125493076310891788248793663 188239614466337682373190495)
    ·
      refine ⟨282359421699506523559785743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188239614466337682373190495 282359421699506523559785743)
      ·
        refine ⟨423539132549259785339678615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282359421699506523559785743 423539132549259785339678615)
        ·
          refine ⟨635308698823889678009517923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423539132549259785339678615 635308698823889678009517923)
          ·
            refine ⟨952963048235834517014276885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635308698823889678009517923 952963048235834517014276885)
            ·
              refine ⟨44670142886054742985044229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 952963048235834517014276885 44670142886054742985044229)
              ·
                refine ⟨8375651791135264309695793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44670142886054742985044229 8375651791135264309695793)
                ·
                  refine ⟨6281738843351448232271845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8375651791135264309695793 6281738843351448232271845)
                  ·
                    refine ⟨1177826033128396543550971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281738843351448232271845 1177826033128396543550971)
                    ·
                      rfl

theorem cell23_6881424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 4, 2, 4].length) (baseStart_6881424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881424 prefixEnd_6881424 := by exact prefixLift 6881424
  have htrace : WordTrace (prefixWord ++ tailWord_6881424) baseStart_6881424 baseEnd_6881424 := by
    simpa [prefixWord, tailWord_6881424, baseEnd_6881424] using wordTrace_append hprefix tailTrace_6881424
  have hstable : (prefixWord ++ tailWord_6881424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881424).length < 2 ^ (prefixWord ++ tailWord_6881424).sum := by decide
  have hdescent : baseEnd_6881424 < baseStart_6881424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881437 : List Nat := [1, 4, 2, 1, 1, 3, 1, 10]
def baseStart_6881437 : Nat := 118140960795 + 6881437 * 2 ^ 59
def prefixEnd_6881437 : Nat := 4983230072969 + 3 ^ 40 * 6881437 * 2
def baseEnd_6881437 : Nat := 130869806467914743695939

theorem tailTrace_6881437 : CollatzResearch.WordTrace tailWord_6881437 prefixEnd_6881437 130869806467914743695939 := by
  unfold tailWord_6881437
  simp only [CollatzResearch.WordTrace]
  refine ⟨250986626770736479717810565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167324417847157653145207043 250986626770736479717810565)
  ·
    refine ⟨47059992519513089947089481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 250986626770736479717810565 47059992519513089947089481)
    ·
      refine ⟨35294994389634817460317111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47059992519513089947089481 35294994389634817460317111)
      ·
        refine ⟨52942491584452226190475667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35294994389634817460317111 52942491584452226190475667)
        ·
          refine ⟨79413737376678339285713501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52942491584452226190475667 79413737376678339285713501)
          ·
            refine ⟨29780151516254377232142563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79413737376678339285713501 29780151516254377232142563)
            ·
              refine ⟨44670227274381565848213845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29780151516254377232142563 44670227274381565848213845)
              ·
                refine ⟨130869806467914743695939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44670227274381565848213845 130869806467914743695939)
                ·
                  rfl

theorem cell23_6881437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 10].length) (baseStart_6881437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881437 prefixEnd_6881437 := by exact prefixLift 6881437
  have htrace : WordTrace (prefixWord ++ tailWord_6881437) baseStart_6881437 baseEnd_6881437 := by
    simpa [prefixWord, tailWord_6881437, baseEnd_6881437] using wordTrace_append hprefix tailTrace_6881437
  have hstable : (prefixWord ++ tailWord_6881437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881437).length < 2 ^ (prefixWord ++ tailWord_6881437).sum := by decide
  have hdescent : baseEnd_6881437 < baseStart_6881437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881441 : List Nat := [1, 2, 3, 3, 1, 3, 1, 3, 2, 4]
def baseStart_6881441 : Nat := 118140960795 + 6881441 * 2 ^ 59
def prefixEnd_6881441 : Nat := 4983230072969 + 3 ^ 40 * 6881441 * 2
def baseEnd_6881441 : Nat := 1177828942852105354713445

theorem tailTrace_6881441 : CollatzResearch.WordTrace tailWord_6881441 prefixEnd_6881441 1177828942852105354713445 := by
  unfold tailWord_6881441
  simp only [CollatzResearch.WordTrace]
  refine ⟨250986772662721988400956177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167324515108481325600637451 250986772662721988400956177)
  ·
    refine ⟨188240079497041491300717133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250986772662721988400956177 188240079497041491300717133)
    ·
      refine ⟨70590029811390559237768925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188240079497041491300717133 70590029811390559237768925)
      ·
        refine ⟨26471261179271459714163347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70590029811390559237768925 26471261179271459714163347)
        ·
          refine ⟨39706891768907189571245021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26471261179271459714163347 39706891768907189571245021)
          ·
            refine ⟨14890084413340196089216883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39706891768907189571245021 14890084413340196089216883)
            ·
              refine ⟨22335126620010294133825325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14890084413340196089216883 22335126620010294133825325)
              ·
                refine ⟨8375672482503860300184497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22335126620010294133825325 8375672482503860300184497)
                ·
                  refine ⟨6281754361877895225138373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8375672482503860300184497 6281754361877895225138373)
                  ·
                    refine ⟨1177828942852105354713445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6281754361877895225138373 1177828942852105354713445)
                    ·
                      rfl

theorem cell23_6881441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_6881441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881441 prefixEnd_6881441 := by exact prefixLift 6881441
  have htrace : WordTrace (prefixWord ++ tailWord_6881441) baseStart_6881441 baseEnd_6881441 := by
    simpa [prefixWord, tailWord_6881441, baseEnd_6881441] using wordTrace_append hprefix tailTrace_6881441
  have hstable : (prefixWord ++ tailWord_6881441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881441).length < 2 ^ (prefixWord ++ tailWord_6881441).sum := by decide
  have hdescent : baseEnd_6881441 < baseStart_6881441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881464 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 1, 3, 3]
def baseStart_6881464 : Nat := 118140960795 + 6881464 * 2 ^ 59
def prefixEnd_6881464 : Nat := 4983230072969 + 3 ^ 40 * 6881464 * 2
def baseEnd_6881464 : Nat := 3533498638611369474152729

theorem tailTrace_6881464 : CollatzResearch.WordTrace tailWord_6881464 prefixEnd_6881464 3533498638611369474152729 := by
  unfold tailWord_6881464
  simp only [CollatzResearch.WordTrace]
  refine ⟨125493805770819331664521723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167325074361092442219362297 125493805770819331664521723)
  ·
    refine ⟨188240708656228997496782585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125493805770819331664521723 188240708656228997496782585)
    ·
      refine ⟨141180531492171748122586939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188240708656228997496782585 141180531492171748122586939)
      ·
        refine ⟨211770797238257622183880409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141180531492171748122586939 211770797238257622183880409)
        ·
          refine ⟨158828097928693216637910307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211770797238257622183880409 158828097928693216637910307)
          ·
            refine ⟨238242146893039824956865461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158828097928693216637910307 238242146893039824956865461)
            ·
              refine ⟨22335201271222483589706137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 238242146893039824956865461 22335201271222483589706137)
              ·
                refine ⟨16751400953416862692279603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22335201271222483589706137 16751400953416862692279603)
                ·
                  refine ⟨25127101430125294038419405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16751400953416862692279603 25127101430125294038419405)
                  ·
                    refine ⟨9422663036296985264407277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25127101430125294038419405 9422663036296985264407277)
                    ·
                      refine ⟨3533498638611369474152729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9422663036296985264407277 3533498638611369474152729)
                      ·
                        rfl

theorem cell23_6881464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_6881464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881464 prefixEnd_6881464 := by exact prefixLift 6881464
  have htrace : WordTrace (prefixWord ++ tailWord_6881464) baseStart_6881464 baseEnd_6881464 := by
    simpa [prefixWord, tailWord_6881464, baseEnd_6881464] using wordTrace_append hprefix tailTrace_6881464
  have hstable : (prefixWord ++ tailWord_6881464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881464).length < 2 ^ (prefixWord ++ tailWord_6881464).sum := by decide
  have hdescent : baseEnd_6881464 < baseStart_6881464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881468 : List Nat := [2, 2, 2, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6881468 : Nat := 118140960795 + 6881468 * 2 ^ 59
def prefixEnd_6881468 : Nat := 4983230072969 + 3 ^ 40 * 6881468 * 2
def baseEnd_6881468 : Nat := 3533500692533987458502711

theorem tailTrace_6881468 : CollatzResearch.WordTrace tailWord_6881468 prefixEnd_6881468 3533500692533987458502711 := by
  unfold tailWord_6881468
  simp only [CollatzResearch.WordTrace]
  refine ⟨125493878716812086006094529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167325171622416114674792705 125493878716812086006094529)
  ·
    refine ⟨94120409037609064504570897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125493878716812086006094529 94120409037609064504570897)
    ·
      refine ⟨70590306778206798378428173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94120409037609064504570897 70590306778206798378428173)
      ·
        refine ⟨26471365041827549391910565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70590306778206798378428173 26471365041827549391910565)
        ·
          refine ⟨4963380945342665510983231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26471365041827549391910565 4963380945342665510983231)
          ·
            refine ⟨7445071418013998266474847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963380945342665510983231 7445071418013998266474847)
            ·
              refine ⟨11167607127020997399712271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445071418013998266474847 11167607127020997399712271)
              ·
                refine ⟨16751410690531496099568407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11167607127020997399712271 16751410690531496099568407)
                ·
                  refine ⟨25127116035797244149352611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16751410690531496099568407 25127116035797244149352611)
                  ·
                    refine ⟨37690674053695866224028917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25127116035797244149352611 37690674053695866224028917)
                    ·
                      refine ⟨3533500692533987458502711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37690674053695866224028917 3533500692533987458502711)
                      ·
                        rfl

theorem cell23_6881468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6881468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881468 prefixEnd_6881468 := by exact prefixLift 6881468
  have htrace : WordTrace (prefixWord ++ tailWord_6881468) baseStart_6881468 baseEnd_6881468 := by
    simpa [prefixWord, tailWord_6881468, baseEnd_6881468] using wordTrace_append hprefix tailTrace_6881468
  have hstable : (prefixWord ++ tailWord_6881468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881468).length < 2 ^ (prefixWord ++ tailWord_6881468).sum := by decide
  have hdescent : baseEnd_6881468 < baseStart_6881468 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881477 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_6881477 : Nat := 118140960795 + 6881477 * 2 ^ 59
def prefixEnd_6881477 : Nat := 4983230072969 + 3 ^ 40 * 6881477 * 2
def baseEnd_6881477 : Nat := 3533505313859877923290169

theorem tailTrace_6881477 : CollatzResearch.WordTrace tailWord_6881477 prefixEnd_6881477 3533505313859877923290169 := by
  unfold tailWord_6881477
  simp only [CollatzResearch.WordTrace]
  refine ⟨250988085690591566549266685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167325390460394377699511123 250988085690591566549266685)
  ·
    refine ⟨94120532133971837455975007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 250988085690591566549266685 94120532133971837455975007)
    ·
      refine ⟨141180798200957756183962511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94120532133971837455975007 141180798200957756183962511)
      ·
        refine ⟨211771197301436634275943767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141180798200957756183962511 211771197301436634275943767)
        ·
          refine ⟨317656795952154951413915651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211771197301436634275943767 317656795952154951413915651)
          ·
            refine ⟨476485193928232427120873477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317656795952154951413915651 476485193928232427120873477)
            ·
              refine ⟨89340973861543580085163777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 476485193928232427120873477 89340973861543580085163777)
              ·
                refine ⟨67005730396157685063872833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89340973861543580085163777 67005730396157685063872833)
                ·
                  refine ⟨50254297797118263797904625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67005730396157685063872833 50254297797118263797904625)
                  ·
                    refine ⟨37690723347838697848428469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50254297797118263797904625 37690723347838697848428469)
                    ·
                      refine ⟨3533505313859877923290169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37690723347838697848428469 3533505313859877923290169)
                      ·
                        rfl

theorem cell23_6881477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_6881477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881477 prefixEnd_6881477 := by exact prefixLift 6881477
  have htrace : WordTrace (prefixWord ++ tailWord_6881477) baseStart_6881477 baseEnd_6881477 := by
    simpa [prefixWord, tailWord_6881477, baseEnd_6881477] using wordTrace_append hprefix tailTrace_6881477
  have hstable : (prefixWord ++ tailWord_6881477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881477).length < 2 ^ (prefixWord ++ tailWord_6881477).sum := by decide
  have hdescent : baseEnd_6881477 < baseStart_6881477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881487 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 4]
def baseStart_6881487 : Nat := 118140960795 + 6881487 * 2 ^ 59
def prefixEnd_6881487 : Nat := 4983230072969 + 3 ^ 40 * 6881487 * 2
def baseEnd_6881487 : Nat := 3533510448666422884165123

theorem tailTrace_6881487 : CollatzResearch.WordTrace tailWord_6881487 prefixEnd_6881487 3533510448666422884165123 := by
  unfold tailWord_6881487
  simp only [CollatzResearch.WordTrace]
  refine ⟨250988450420555338257130715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167325633613703558838087143 250988450420555338257130715)
  ·
    refine ⟨376482675630833007385696073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250988450420555338257130715 376482675630833007385696073)
    ·
      refine ⟨282362006723124755539272055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376482675630833007385696073 282362006723124755539272055)
      ·
        refine ⟨423543010084687133308908083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282362006723124755539272055 423543010084687133308908083)
        ·
          refine ⟨635314515127030699963362125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423543010084687133308908083 635314515127030699963362125)
          ·
            refine ⟨238242943172636512486260797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 635314515127030699963362125 238242943172636512486260797)
            ·
              refine ⟨89341103689738692182347799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 238242943172636512486260797 89341103689738692182347799)
              ·
                refine ⟨134011655534608038273521699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89341103689738692182347799 134011655534608038273521699)
                ·
                  refine ⟨201017483301912057410282549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134011655534608038273521699 201017483301912057410282549)
                  ·
                    refine ⟨18845389059554255382213989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 201017483301912057410282549 18845389059554255382213989)
                    ·
                      refine ⟨3533510448666422884165123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18845389059554255382213989 3533510448666422884165123)
                      ·
                        rfl

theorem cell23_6881487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_6881487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881487 prefixEnd_6881487 := by exact prefixLift 6881487
  have htrace : WordTrace (prefixWord ++ tailWord_6881487) baseStart_6881487 baseEnd_6881487 := by
    simpa [prefixWord, tailWord_6881487, baseEnd_6881487] using wordTrace_append hprefix tailTrace_6881487
  have hstable : (prefixWord ++ tailWord_6881487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881487).length < 2 ^ (prefixWord ++ tailWord_6881487).sum := by decide
  have hdescent : baseEnd_6881487 < baseStart_6881487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881497 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 1, 8]
def baseStart_6881497 : Nat := 118140960795 + 6881497 * 2 ^ 59
def prefixEnd_6881497 : Nat := 4983230072969 + 3 ^ 40 * 6881497 * 2
def baseEnd_6881497 : Nat := 1177838527824322615013359

theorem tailTrace_6881497 : CollatzResearch.WordTrace tailWord_6881497 prefixEnd_6881497 1177838527824322615013359 := by
  unfold tailWord_6881497
  simp only [CollatzResearch.WordTrace]
  refine ⟨250988815150519109964994745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167325876767012739976663163 250988815150519109964994745)
  ·
    refine ⟨188241611362889332473746059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250988815150519109964994745 188241611362889332473746059)
    ·
      refine ⟨282362417044333998710619089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188241611362889332473746059 282362417044333998710619089)
      ·
        refine ⟨211771812783250499032964317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282362417044333998710619089 211771812783250499032964317)
        ·
          refine ⟨79414429793718937137361619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211771812783250499032964317 79414429793718937137361619)
          ·
            refine ⟨119121644690578405706042429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79414429793718937137361619 119121644690578405706042429)
            ·
              refine ⟨44670616758966902139765911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119121644690578405706042429 44670616758966902139765911)
              ·
                refine ⟨67005925138450353209648867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44670616758966902139765911 67005925138450353209648867)
                ·
                  refine ⟨100508887707675529814473301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67005925138450353209648867 100508887707675529814473301)
                  ·
                    refine ⟨1177838527824322615013359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100508887707675529814473301 1177838527824322615013359)
                    ·
                      rfl

theorem cell23_6881497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_6881497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881497 prefixEnd_6881497 := by exact prefixLift 6881497
  have htrace : WordTrace (prefixWord ++ tailWord_6881497) baseStart_6881497 baseEnd_6881497 := by
    simpa [prefixWord, tailWord_6881497, baseEnd_6881497] using wordTrace_append hprefix tailTrace_6881497
  have hstable : (prefixWord ++ tailWord_6881497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881497).length < 2 ^ (prefixWord ++ tailWord_6881497).sum := by decide
  have hdescent : baseEnd_6881497 < baseStart_6881497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881521 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 1, 4, 2]
def baseStart_6881521 : Nat := 118140960795 + 6881521 * 2 ^ 59
def prefixEnd_6881521 : Nat := 4983230072969 + 3 ^ 40 * 6881521 * 2
def baseEnd_6881521 : Nat := 3533527907008675751139967

theorem tailTrace_6881521 : CollatzResearch.WordTrace tailWord_6881521 prefixEnd_6881521 3533527907008675751139967 := by
  unfold tailWord_6881521
  simp only [CollatzResearch.WordTrace]
  refine ⟨250989690502432162063868417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167326460334954774709245611 250989690502432162063868417)
  ·
    refine ⟨188242267876824121547901313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250989690502432162063868417 188242267876824121547901313)
    ·
      refine ⟨141181700907618091160925985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188242267876824121547901313 141181700907618091160925985)
      ·
        refine ⟨105886275680713568370694489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141181700907618091160925985 105886275680713568370694489)
        ·
          refine ⟨79414706760535176278020867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105886275680713568370694489 79414706760535176278020867)
          ·
            refine ⟨119122060140802764417031301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79414706760535176278020867 119122060140802764417031301)
            ·
              refine ⟨22335386276400518328193369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119122060140802764417031301 22335386276400518328193369)
              ·
                refine ⟨16751539707300388746145027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22335386276400518328193369 16751539707300388746145027)
                ·
                  refine ⟨25127309560950583119217541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16751539707300388746145027 25127309560950583119217541)
                  ·
                    refine ⟨4711370542678234334853289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25127309560950583119217541 4711370542678234334853289)
                    ·
                      refine ⟨3533527907008675751139967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711370542678234334853289 3533527907008675751139967)
                      ·
                        rfl

theorem cell23_6881521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_6881521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881521 prefixEnd_6881521 := by exact prefixLift 6881521
  have htrace : WordTrace (prefixWord ++ tailWord_6881521) baseStart_6881521 baseEnd_6881521 := by
    simpa [prefixWord, tailWord_6881521, baseEnd_6881521] using wordTrace_append hprefix tailTrace_6881521
  have hstable : (prefixWord ++ tailWord_6881521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881521).length < 2 ^ (prefixWord ++ tailWord_6881521).sum := by decide
  have hdescent : baseEnd_6881521 < baseStart_6881521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881544 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 7]
def baseStart_6881544 : Nat := 118140960795 + 6881544 * 2 ^ 59
def prefixEnd_6881544 : Nat := 4983230072969 + 3 ^ 40 * 6881544 * 2
def baseEnd_6881544 : Nat := 392615524118192129016929

theorem tailTrace_6881544 : CollatzResearch.WordTrace tailWord_6881544 prefixEnd_6881544 392615524118192129016929 := by
  unfold tailWord_6881544
  simp only [CollatzResearch.WordTrace]
  refine ⟨125495264690674418495977843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167327019587565891327970457 125495264690674418495977843)
  ·
    refine ⟨188242897036011627743966765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125495264690674418495977843 188242897036011627743966765)
    ·
      refine ⟨70591086388504360403987537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188242897036011627743966765 70591086388504360403987537)
      ·
        refine ⟨52943314791378270302990653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70591086388504360403987537 52943314791378270302990653)
        ·
          refine ⟨19853743046766851363621495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52943314791378270302990653 19853743046766851363621495)
          ·
            refine ⟨29780614570150277045432243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19853743046766851363621495 29780614570150277045432243)
            ·
              refine ⟨44670921855225415568148365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29780614570150277045432243 44670921855225415568148365)
              ·
                refine ⟨16751595695709530838055637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44670921855225415568148365 16751595695709530838055637)
                ·
                  refine ⟨392615524118192129016929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16751595695709530838055637 392615524118192129016929)
                  ·
                    rfl

theorem cell23_6881544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 7].length) (baseStart_6881544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881544 prefixEnd_6881544 := by exact prefixLift 6881544
  have htrace : WordTrace (prefixWord ++ tailWord_6881544) baseStart_6881544 baseEnd_6881544 := by
    simpa [prefixWord, tailWord_6881544, baseEnd_6881544] using wordTrace_append hprefix tailTrace_6881544
  have hstable : (prefixWord ++ tailWord_6881544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881544).length < 2 ^ (prefixWord ++ tailWord_6881544).sum := by decide
  have hdescent : baseEnd_6881544 < baseStart_6881544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881575 : List Nat := [1, 1, 8, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6881575 : Nat := 118140960795 + 6881575 * 2 ^ 59
def prefixEnd_6881575 : Nat := 4983230072969 + 3 ^ 40 * 6881575 * 2
def baseEnd_6881575 : Nat := 3533555634964018539864719

theorem tailTrace_6881575 : CollatzResearch.WordTrace tailWord_6881575 prefixEnd_6881575 3533555634964018539864719 := by
  unfold tailWord_6881575
  simp only [CollatzResearch.WordTrace]
  refine ⟨250991660044236529286334179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167327773362824352857556119 250991660044236529286334179)
  ·
    refine ⟨376487490066354793929501269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250991660044236529286334179 376487490066354793929501269)
    ·
      refine ⟨4411962774215095241361343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 376487490066354793929501269 4411962774215095241361343)
      ·
        refine ⟨6617944161322642862042015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4411962774215095241361343 6617944161322642862042015)
        ·
          refine ⟨9926916241983964293063023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6617944161322642862042015 9926916241983964293063023)
          ·
            refine ⟨14890374362975946439594535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9926916241983964293063023 14890374362975946439594535)
            ·
              refine ⟨22335561544463919659391803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14890374362975946439594535 22335561544463919659391803)
              ·
                refine ⟨33503342316695879489087705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22335561544463919659391803 33503342316695879489087705)
                ·
                  refine ⟨25127506737521909616815779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33503342316695879489087705 25127506737521909616815779)
                  ·
                    refine ⟨37691260106282864425223669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25127506737521909616815779 37691260106282864425223669)
                    ·
                      refine ⟨3533555634964018539864719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37691260106282864425223669 3533555634964018539864719)
                      ·
                        rfl

theorem cell23_6881575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6881575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881575 prefixEnd_6881575 := by exact prefixLift 6881575
  have htrace : WordTrace (prefixWord ++ tailWord_6881575) baseStart_6881575 baseEnd_6881575 := by
    simpa [prefixWord, tailWord_6881575, baseEnd_6881575] using wordTrace_append hprefix tailTrace_6881575
  have hstable : (prefixWord ++ tailWord_6881575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881575).length < 2 ^ (prefixWord ++ tailWord_6881575).sum := by decide
  have hdescent : baseEnd_6881575 < baseStart_6881575 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881631 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 3]
def baseStart_6881631 : Nat := 118140960795 + 6881631 * 2 ^ 59
def prefixEnd_6881631 : Nat := 4983230072969 + 3 ^ 40 * 6881631 * 2
def baseEnd_6881631 : Nat := 3533584389880670320764461

theorem tailTrace_6881631 : CollatzResearch.WordTrace tailWord_6881631 prefixEnd_6881631 3533584389880670320764461 := by
  unfold tailWord_6881631
  simp only [CollatzResearch.WordTrace]
  refine ⟨250993702532033650850372747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167329135021355767233581831 250993702532033650850372747)
  ·
    refine ⟨376490553798050476275559121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250993702532033650850372747 376490553798050476275559121)
    ·
      refine ⟨282367915348537857206669341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376490553798050476275559121 282367915348537857206669341)
      ·
        refine ⟨105887968255701696452501003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282367915348537857206669341 105887968255701696452501003)
        ·
          refine ⟨158831952383552544678751505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105887968255701696452501003 158831952383552544678751505)
          ·
            refine ⟨119123964287664408509063629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158831952383552544678751505 119123964287664408509063629)
            ·
              refine ⟨44671486607874153190898861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119123964287664408509063629 44671486607874153190898861)
              ·
                refine ⟨16751807477952807446587073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44671486607874153190898861 16751807477952807446587073)
                ·
                  refine ⟨12563855608464605584940305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16751807477952807446587073 12563855608464605584940305)
                  ·
                    refine ⟨9422891706348454188705229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12563855608464605584940305 9422891706348454188705229)
                    ·
                      refine ⟨3533584389880670320764461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9422891706348454188705229 3533584389880670320764461)
                      ·
                        rfl

theorem cell23_6881631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_6881631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881631 prefixEnd_6881631 := by exact prefixLift 6881631
  have htrace : WordTrace (prefixWord ++ tailWord_6881631) baseStart_6881631 baseEnd_6881631 := by
    simpa [prefixWord, tailWord_6881631, baseEnd_6881631] using wordTrace_append hprefix tailTrace_6881631
  have hstable : (prefixWord ++ tailWord_6881631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881631).length < 2 ^ (prefixWord ++ tailWord_6881631).sum := by decide
  have hdescent : baseEnd_6881631 < baseStart_6881631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881698 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_6881698 : Nat := 118140960795 + 6881698 * 2 ^ 59
def prefixEnd_6881698 : Nat := 4983230072969 + 3 ^ 40 * 6881698 * 2
def baseEnd_6881698 : Nat := 1177872931028173852875551

theorem tailTrace_6881698 : CollatzResearch.WordTrace tailWord_6881698 prefixEnd_6881698 1177872931028173852875551 := by
  unfold tailWord_6881698
  simp only [CollatzResearch.WordTrace]
  refine ⟨62749036555697730323265437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167330764148527280862041165 62749036555697730323265437)
  ·
    refine ⟨23530888708386648871224539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62749036555697730323265437 23530888708386648871224539)
    ·
      refine ⟨35296333062579973306836809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23530888708386648871224539 35296333062579973306836809)
      ·
        refine ⟨26472249796934979980127607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35296333062579973306836809 26472249796934979980127607)
        ·
          refine ⟨39708374695402469970191411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26472249796934979980127607 39708374695402469970191411)
          ·
            refine ⟨59562562043103704955287117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39708374695402469970191411 59562562043103704955287117)
            ·
              refine ⟨22335960766163889358232669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59562562043103704955287117 22335960766163889358232669)
              ·
                refine ⟨8375985287311458509337251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22335960766163889358232669 8375985287311458509337251)
                ·
                  refine ⟨12563977930967187764005877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8375985287311458509337251 12563977930967187764005877)
                  ·
                    refine ⟨1177872931028173852875551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12563977930967187764005877 1177872931028173852875551)
                    ·
                      rfl

theorem cell23_6881698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_6881698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881698 prefixEnd_6881698 := by exact prefixLift 6881698
  have htrace : WordTrace (prefixWord ++ tailWord_6881698) baseStart_6881698 baseEnd_6881698 := by
    simpa [prefixWord, tailWord_6881698, baseEnd_6881698] using wordTrace_append hprefix tailTrace_6881698
  have hstable : (prefixWord ++ tailWord_6881698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881698).length < 2 ^ (prefixWord ++ tailWord_6881698).sum := by decide
  have hdescent : baseEnd_6881698 < baseStart_6881698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881721 : List Nat := [1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6881721 : Nat := 118140960795 + 6881721 * 2 ^ 59
def prefixEnd_6881721 : Nat := 4983230072969 + 3 ^ 40 * 6881721 * 2
def baseEnd_6881721 : Nat := 3533630603139574968639047

theorem tailTrace_6881721 : CollatzResearch.WordTrace tailWord_6881721 prefixEnd_6881721 3533630603139574968639047 := by
  unfold tailWord_6881721
  simp only [CollatzResearch.WordTrace]
  refine ⟨250996985101707596221149017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167331323401138397480766011 250996985101707596221149017)
  ·
    refine ⟨188247738826280697165861763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 250996985101707596221149017 188247738826280697165861763)
    ·
      refine ⟨282371608239421045748792645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188247738826280697165861763 282371608239421045748792645)
      ·
        refine ⟨52944676544891446077898621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282371608239421045748792645 52944676544891446077898621)
        ·
          refine ⟨19854253704334292279211983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52944676544891446077898621 19854253704334292279211983)
          ·
            refine ⟨29781380556501438418817975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19854253704334292279211983 29781380556501438418817975)
            ·
              refine ⟨44672070834752157628226963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29781380556501438418817975 44672070834752157628226963)
              ·
                refine ⟨67008106252128236442340445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44672070834752157628226963 67008106252128236442340445)
                ·
                  refine ⟨25128039844548088665877667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67008106252128236442340445 25128039844548088665877667)
                  ·
                    refine ⟨37692059766822132998816501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25128039844548088665877667 37692059766822132998816501)
                    ·
                      refine ⟨3533630603139574968639047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37692059766822132998816501 3533630603139574968639047)
                      ·
                        rfl

theorem cell23_6881721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6881721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881721 prefixEnd_6881721 := by exact prefixLift 6881721
  have htrace : WordTrace (prefixWord ++ tailWord_6881721) baseStart_6881721 baseEnd_6881721 := by
    simpa [prefixWord, tailWord_6881721, baseEnd_6881721] using wordTrace_append hprefix tailTrace_6881721
  have hstable : (prefixWord ++ tailWord_6881721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881721).length < 2 ^ (prefixWord ++ tailWord_6881721).sum := by decide
  have hdescent : baseEnd_6881721 < baseStart_6881721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881735 : List Nat := [1, 1, 4, 1, 1, 4, 2, 2, 3, 2, 2]
def baseStart_6881735 : Nat := 118140960795 + 6881735 * 2 ^ 59
def prefixEnd_6881735 : Nat := 4983230072969 + 3 ^ 40 * 6881735 * 2
def baseEnd_6881735 : Nat := 3533637791868737913863983

theorem tailTrace_6881735 : CollatzResearch.WordTrace tailWord_6881735 prefixEnd_6881735 3533637791868737913863983 := by
  unfold tailWord_6881735
  simp only [CollatzResearch.WordTrace]
  refine ⟨250997495723656876612158659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167331663815771251074772439 250997495723656876612158659)
  ·
    refine ⟨376496243585485314918237989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 250997495723656876612158659 376496243585485314918237989)
    ·
      refine ⟨70593045672278496547169623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376496243585485314918237989 70593045672278496547169623)
      ·
        refine ⟨105889568508417744820754435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70593045672278496547169623 105889568508417744820754435)
        ·
          refine ⟨158834352762626617231131653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105889568508417744820754435 158834352762626617231131653)
          ·
            refine ⟨29781441142992490730837185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158834352762626617231131653 29781441142992490730837185)
            ·
              refine ⟨22336080857244368048127889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29781441142992490730837185 22336080857244368048127889)
              ·
                refine ⟨16752060642933276036095917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22336080857244368048127889 16752060642933276036095917)
                ·
                  refine ⟨6282022741099978513535969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16752060642933276036095917 6282022741099978513535969)
                  ·
                    refine ⟨4711517055824983885151977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6282022741099978513535969 4711517055824983885151977)
                    ·
                      refine ⟨3533637791868737913863983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711517055824983885151977 3533637791868737913863983)
                      ·
                        rfl

theorem cell23_6881735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 3, 2, 2].length) (baseStart_6881735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881735 prefixEnd_6881735 := by exact prefixLift 6881735
  have htrace : WordTrace (prefixWord ++ tailWord_6881735) baseStart_6881735 baseEnd_6881735 := by
    simpa [prefixWord, tailWord_6881735, baseEnd_6881735] using wordTrace_append hprefix tailTrace_6881735
  have hstable : (prefixWord ++ tailWord_6881735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881735).length < 2 ^ (prefixWord ++ tailWord_6881735).sum := by decide
  have hdescent : baseEnd_6881735 < baseStart_6881735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881746 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_6881746 : Nat := 118140960795 + 6881746 * 2 ^ 59
def prefixEnd_6881746 : Nat := 4983230072969 + 3 ^ 40 * 6881746 * 2
def baseEnd_6881746 : Nat := 3533643440155937370826433

theorem tailTrace_6881746 : CollatzResearch.WordTrace tailWord_6881746 prefixEnd_6881746 3533643440155937370826433 := by
  unfold tailWord_6881746
  simp only [CollatzResearch.WordTrace]
  refine ⟨62749474231654256372702273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167331931284411350327206061 62749474231654256372702273)
  ·
    refine ⟨47062105673740692279526705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62749474231654256372702273 47062105673740692279526705)
    ·
      refine ⟨35296579255305519209645029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47062105673740692279526705 35296579255305519209645029)
      ·
        refine ⟨6618108610369784851808443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35296579255305519209645029 6618108610369784851808443)
        ·
          refine ⟨9927162915554677277712665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6618108610369784851808443 9927162915554677277712665)
          ·
            refine ⟨7445372186666007958284499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9927162915554677277712665 7445372186666007958284499)
            ·
              refine ⟨11168058279999011937426749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445372186666007958284499 11168058279999011937426749)
              ·
                refine ⟨4188021854999629476535031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11168058279999011937426749 4188021854999629476535031)
                ·
                  refine ⟨6282032782499444214802547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188021854999629476535031 6282032782499444214802547)
                  ·
                    refine ⟨9423049173749166322203821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6282032782499444214802547 9423049173749166322203821)
                    ·
                      refine ⟨3533643440155937370826433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423049173749166322203821 3533643440155937370826433)
                      ·
                        rfl

theorem cell23_6881746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_6881746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881746 prefixEnd_6881746 := by exact prefixLift 6881746
  have htrace : WordTrace (prefixWord ++ tailWord_6881746) baseStart_6881746 baseEnd_6881746 := by
    simpa [prefixWord, tailWord_6881746, baseEnd_6881746] using wordTrace_append hprefix tailTrace_6881746
  have hstable : (prefixWord ++ tailWord_6881746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881746).length < 2 ^ (prefixWord ++ tailWord_6881746).sum := by decide
  have hdescent : baseEnd_6881746 < baseStart_6881746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881811 : List Nat := [1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5]
def baseStart_6881811 : Nat := 118140960795 + 6881811 * 2 ^ 59
def prefixEnd_6881811 : Nat := 4983230072969 + 3 ^ 40 * 6881811 * 2
def baseEnd_6881811 : Nat := 3533676816398479616513633

theorem tailTrace_6881811 : CollatzResearch.WordTrace tailWord_6881811 prefixEnd_6881811 3533676816398479616513633 := by
  unfold tailWord_6881811
  simp only [CollatzResearch.WordTrace]
  refine ⟨251000267671381541591925287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167333511780921027727950191 251000267671381541591925287)
  ·
    refine ⟨376500401507072312387887931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251000267671381541591925287 376500401507072312387887931)
    ·
      refine ⟨564750602260608468581831897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376500401507072312387887931 564750602260608468581831897)
      ·
        refine ⟨423562951695456351436373923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564750602260608468581831897 423562951695456351436373923)
        ·
          refine ⟨635344427543184527154560885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423562951695456351436373923 635344427543184527154560885)
          ·
            refine ⟨59563540082173549420740083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 635344427543184527154560885 59563540082173549420740083)
            ·
              refine ⟨89345310123260324131110125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59563540082173549420740083 89345310123260324131110125)
              ·
                refine ⟨33504491296222621549166297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89345310123260324131110125 33504491296222621549166297)
                ·
                  refine ⟨25128368472166966161874723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33504491296222621549166297 25128368472166966161874723)
                  ·
                    refine ⟨37692552708250449242812085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25128368472166966161874723 37692552708250449242812085)
                    ·
                      refine ⟨3533676816398479616513633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37692552708250449242812085 3533676816398479616513633)
                      ·
                        rfl

theorem cell23_6881811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_6881811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881811 prefixEnd_6881811 := by exact prefixLift 6881811
  have htrace : WordTrace (prefixWord ++ tailWord_6881811) baseStart_6881811 baseEnd_6881811 := by
    simpa [prefixWord, tailWord_6881811, baseEnd_6881811] using wordTrace_append hprefix tailTrace_6881811
  have hstable : (prefixWord ++ tailWord_6881811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881811).length < 2 ^ (prefixWord ++ tailWord_6881811).sum := by decide
  have hdescent : baseEnd_6881811 < baseStart_6881811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881842 : List Nat := [3, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_6881842 : Nat := 118140960795 + 6881842 * 2 ^ 59
def prefixEnd_6881842 : Nat := 4983230072969 + 3 ^ 40 * 6881842 * 2
def baseEnd_6881842 : Nat := 3533692734298768995225991

theorem tailTrace_6881842 : CollatzResearch.WordTrace tailWord_6881842 prefixEnd_6881842 3533692734298768995225991 := by
  unfold tailWord_6881842
  simp only [CollatzResearch.WordTrace]
  refine ⟨62750349583567308471575945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167334265556179489257535853 62750349583567308471575945)
  ·
    refine ⟨47062762187675481353681959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62750349583567308471575945 47062762187675481353681959)
    ·
      refine ⟨70594143281513222030522939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47062762187675481353681959 70594143281513222030522939)
      ·
        refine ⟨105891214922269833045784409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70594143281513222030522939 105891214922269833045784409)
        ·
          refine ⟨79418411191702374784338307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105891214922269833045784409 79418411191702374784338307)
          ·
            refine ⟨119127616787553562176507461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79418411191702374784338307 119127616787553562176507461)
            ·
              refine ⟨22336428147666292908095149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119127616787553562176507461 22336428147666292908095149)
              ·
                refine ⟨8376160555374859840535681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22336428147666292908095149 8376160555374859840535681)
                ·
                  refine ⟨6282120416531144880401761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8376160555374859840535681 6282120416531144880401761)
                  ·
                    refine ⟨4711590312398358660301321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6282120416531144880401761 4711590312398358660301321)
                    ·
                      refine ⟨3533692734298768995225991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711590312398358660301321 3533692734298768995225991)
                      ·
                        rfl

theorem cell23_6881842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_6881842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881842 prefixEnd_6881842 := by exact prefixLift 6881842
  have htrace : WordTrace (prefixWord ++ tailWord_6881842) baseStart_6881842 baseEnd_6881842 := by
    simpa [prefixWord, tailWord_6881842, baseEnd_6881842] using wordTrace_append hprefix tailTrace_6881842
  have hstable : (prefixWord ++ tailWord_6881842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881842).length < 2 ^ (prefixWord ++ tailWord_6881842).sum := by decide
  have hdescent : baseEnd_6881842 < baseStart_6881842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881871 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 5]
def baseStart_6881871 : Nat := 118140960795 + 6881871 * 2 ^ 59
def prefixEnd_6881871 : Nat := 4983230072969 + 3 ^ 40 * 6881871 * 2
def baseEnd_6881871 : Nat := 3533707625237749381763357

theorem tailTrace_6881871 : CollatzResearch.WordTrace tailWord_6881871 prefixEnd_6881871 3533707625237749381763357 := by
  unfold tailWord_6881871
  simp only [CollatzResearch.WordTrace]
  refine ⟨251002456051164171839109467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167334970700776114559406311 251002456051164171839109467)
  ·
    refine ⟨376503684076746257758664201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251002456051164171839109467 376503684076746257758664201)
    ·
      refine ⟨282377763057559693318998151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376503684076746257758664201 282377763057559693318998151)
      ·
        refine ⟨423566644586339539978497227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282377763057559693318998151 423566644586339539978497227)
        ·
          refine ⟨635349966879509309967745841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423566644586339539978497227 635349966879509309967745841)
          ·
            refine ⟨476512475159631982475809381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635349966879509309967745841 476512475159631982475809381)
            ·
              refine ⟨89346089092430996714214259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 476512475159631982475809381 89346089092430996714214259)
              ·
                refine ⟨134019133638646495071321389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89346089092430996714214259 134019133638646495071321389)
                ·
                  refine ⟨50257175114492435651745521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134019133638646495071321389 50257175114492435651745521)
                  ·
                    refine ⟨37692881335869326738809141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50257175114492435651745521 37692881335869326738809141)
                    ·
                      refine ⟨3533707625237749381763357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37692881335869326738809141 3533707625237749381763357)
                      ·
                        rfl

theorem cell23_6881871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 5].length) (baseStart_6881871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881871 prefixEnd_6881871 := by exact prefixLift 6881871
  have htrace : WordTrace (prefixWord ++ tailWord_6881871) baseStart_6881871 baseEnd_6881871 := by
    simpa [prefixWord, tailWord_6881871, baseEnd_6881871] using wordTrace_append hprefix tailTrace_6881871
  have hstable : (prefixWord ++ tailWord_6881871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881871).length < 2 ^ (prefixWord ++ tailWord_6881871).sum := by decide
  have hdescent : baseEnd_6881871 < baseStart_6881871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881898 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6881898 : Nat := 118140960795 + 6881898 * 2 ^ 59
def prefixEnd_6881898 : Nat := 4983230072969 + 3 ^ 40 * 6881898 * 2
def baseEnd_6881898 : Nat := 3533721489215420776125733

theorem tailTrace_6881898 : CollatzResearch.WordTrace tailWord_6881898 prefixEnd_6881898 3533721489215420776125733 := by
  unfold tailWord_6881898
  simp only [CollatzResearch.WordTrace]
  refine ⟨62750860205516588862585587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167335627214710903633561565 62750860205516588862585587)
  ·
    refine ⟨94126290308274883293878381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62750860205516588862585587 94126290308274883293878381)
    ·
      refine ⟨35297358865603081235204393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94126290308274883293878381 35297358865603081235204393)
      ·
        refine ⟨26473019149202310926403295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35297358865603081235204393 26473019149202310926403295)
        ·
          refine ⟨39709528723803466389604943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26473019149202310926403295 39709528723803466389604943)
          ·
            refine ⟨59564293085705199584407415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39709528723803466389604943 59564293085705199584407415)
            ·
              refine ⟨89346439628557799376611123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59564293085705199584407415 89346439628557799376611123)
              ·
                refine ⟨134019659442836699064916685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89346439628557799376611123 134019659442836699064916685)
                ·
                  refine ⟨50257372291063762149343757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 134019659442836699064916685 50257372291063762149343757)
                  ·
                    refine ⟨18846514609148910806003909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50257372291063762149343757 18846514609148910806003909)
                    ·
                      refine ⟨3533721489215420776125733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18846514609148910806003909 3533721489215420776125733)
                      ·
                        rfl

theorem cell23_6881898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6881898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881898 prefixEnd_6881898 := by exact prefixLift 6881898
  have htrace : WordTrace (prefixWord ++ tailWord_6881898) baseStart_6881898 baseEnd_6881898 := by
    simpa [prefixWord, tailWord_6881898, baseEnd_6881898] using wordTrace_append hprefix tailTrace_6881898
  have hstable : (prefixWord ++ tailWord_6881898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881898).length < 2 ^ (prefixWord ++ tailWord_6881898).sum := by decide
  have hdescent : baseEnd_6881898 < baseStart_6881898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881969 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 3]
def baseStart_6881969 : Nat := 118140960795 + 6881969 * 2 ^ 59
def prefixEnd_6881969 : Nat := 4983230072969 + 3 ^ 40 * 6881969 * 2
def baseEnd_6881969 : Nat := 3533757946341889998337907

theorem tailTrace_6881969 : CollatzResearch.WordTrace tailWord_6881969 prefixEnd_6881969 3533757946341889998337907 := by
  unfold tailWord_6881969
  simp only [CollatzResearch.WordTrace]
  refine ⟨251006030404809134576176961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167337353603206089717451307 251006030404809134576176961)
  ·
    refine ⟨188254522803606850932132721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251006030404809134576176961 188254522803606850932132721)
    ·
      refine ⟨141190892102705138199099541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188254522803606850932132721 141190892102705138199099541)
      ·
        refine ⟨6618323067314303353082791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141190892102705138199099541 6618323067314303353082791)
        ·
          refine ⟨9927484600971455029624187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6618323067314303353082791 9927484600971455029624187)
          ·
            refine ⟨14891226901457182544436281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9927484600971455029624187 14891226901457182544436281)
            ·
              refine ⟨11168420176092886908327211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14891226901457182544436281 11168420176092886908327211)
              ·
                refine ⟨16752630264139330362490817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11168420176092886908327211 16752630264139330362490817)
                ·
                  refine ⟨12564472698104497771868113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16752630264139330362490817 12564472698104497771868113)
                  ·
                    refine ⟨9423354523578373328901085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12564472698104497771868113 9423354523578373328901085)
                    ·
                      refine ⟨3533757946341889998337907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423354523578373328901085 3533757946341889998337907)
                      ·
                        rfl

theorem cell23_6881969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_6881969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881969 prefixEnd_6881969 := by exact prefixLift 6881969
  have htrace : WordTrace (prefixWord ++ tailWord_6881969) baseStart_6881969 baseEnd_6881969 := by
    simpa [prefixWord, tailWord_6881969, baseEnd_6881969] using wordTrace_append hprefix tailTrace_6881969
  have hstable : (prefixWord ++ tailWord_6881969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881969).length < 2 ^ (prefixWord ++ tailWord_6881969).sum := by decide
  have hdescent : baseEnd_6881969 < baseStart_6881969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6881992 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 2, 3, 2]
def baseStart_6881992 : Nat := 118140960795 + 6881992 * 2 ^ 59
def prefixEnd_6881992 : Nat := 4983230072969 + 3 ^ 40 * 6881992 * 2
def baseEnd_6881992 : Nat := 3533769756396943408350301

theorem tailTrace_6881992 : CollatzResearch.WordTrace tailWord_6881992 prefixEnd_6881992 3533769756396943408350301 := by
  unfold tailWord_6881992
  simp only [CollatzResearch.WordTrace]
  refine ⟨125503434641862904752132115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167337912855817206336176153 125503434641862904752132115)
  ·
    refine ⟨188255151962794357128198173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125503434641862904752132115 188255151962794357128198173)
    ·
      refine ⟨70595681986047883923074315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188255151962794357128198173 70595681986047883923074315)
      ·
        refine ⟨105893522979071825884611473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70595681986047883923074315 105893522979071825884611473)
        ·
          refine ⟨79420142234303869413458605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105893522979071825884611473 79420142234303869413458605)
          ·
            refine ⟨29782553337863951030046977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79420142234303869413458605 29782553337863951030046977)
            ·
              refine ⟨22336915003397963272535233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29782553337863951030046977 22336915003397963272535233)
              ·
                refine ⟨16752686252548472454401425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22336915003397963272535233 16752686252548472454401425)
                ·
                  refine ⟨12564514689411354340801069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16752686252548472454401425 12564514689411354340801069)
                  ·
                    refine ⟨4711693008529257877800401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12564514689411354340801069 4711693008529257877800401)
                    ·
                      refine ⟨3533769756396943408350301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711693008529257877800401 3533769756396943408350301)
                      ·
                        rfl

theorem cell23_6881992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 3, 2].length) (baseStart_6881992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6881992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6881992 prefixEnd_6881992 := by exact prefixLift 6881992
  have htrace : WordTrace (prefixWord ++ tailWord_6881992) baseStart_6881992 baseEnd_6881992 := by
    simpa [prefixWord, tailWord_6881992, baseEnd_6881992] using wordTrace_append hprefix tailTrace_6881992
  have hstable : (prefixWord ++ tailWord_6881992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6881992).length < 2 ^ (prefixWord ++ tailWord_6881992).sum := by decide
  have hdescent : baseEnd_6881992 < baseStart_6881992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6881992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882015 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 1, 6]
def baseStart_6882015 : Nat := 118140960795 + 6882015 * 2 ^ 59
def prefixEnd_6882015 : Nat := 4983230072969 + 3 ^ 40 * 6882015 * 2
def baseEnd_6882015 : Nat := 1177927188817332272787565

theorem tailTrace_6882015 : CollatzResearch.WordTrace tailWord_6882015 prefixEnd_6882015 1177927188817332272787565 := by
  unfold tailWord_6882015
  simp only [CollatzResearch.WordTrace]
  refine ⟨251007708162642484432351499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167338472108428322954900999 251007708162642484432351499)
  ·
    refine ⟨376511562243963726648527249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251007708162642484432351499 376511562243963726648527249)
    ·
      refine ⟨282383671682972794986395437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376511562243963726648527249 282383671682972794986395437)
      ·
        refine ⟨105893876881114798119898289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282383671682972794986395437 105893876881114798119898289)
        ·
          refine ⟨79420407660836098589923717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105893876881114798119898289 79420407660836098589923717)
          ·
            refine ⟨14891326436406768485610697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79420407660836098589923717 14891326436406768485610697)
            ·
              refine ⟨11168494827305076364208023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14891326436406768485610697 11168494827305076364208023)
              ·
                refine ⟨16752742240957614546312035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11168494827305076364208023 16752742240957614546312035)
                ·
                  refine ⟨25129113361436421819468053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16752742240957614546312035 25129113361436421819468053)
                  ·
                    refine ⟨1177927188817332272787565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25129113361436421819468053 1177927188817332272787565)
                    ·
                      rfl

theorem cell23_6882015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_6882015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882015 prefixEnd_6882015 := by exact prefixLift 6882015
  have htrace : WordTrace (prefixWord ++ tailWord_6882015) baseStart_6882015 baseEnd_6882015 := by
    simpa [prefixWord, tailWord_6882015, baseEnd_6882015] using wordTrace_append hprefix tailTrace_6882015
  have hstable : (prefixWord ++ tailWord_6882015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882015).length < 2 ^ (prefixWord ++ tailWord_6882015).sum := by decide
  have hdescent : baseEnd_6882015 < baseStart_6882015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882025 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_6882025 : Nat := 118140960795 + 6882025 * 2 ^ 59
def prefixEnd_6882025 : Nat := 4983230072969 + 3 ^ 40 * 6882025 * 2
def baseEnd_6882025 : Nat := 3533786701258541779237649

theorem tailTrace_6882025 : CollatzResearch.WordTrace tailWord_6882025 prefixEnd_6882025 3533786701258541779237649 := by
  unfold tailWord_6882025
  simp only [CollatzResearch.WordTrace]
  refine ⟨251008072892606256140215529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167338715261737504093477019 251008072892606256140215529)
  ·
    refine ⟨188256054669454692105161647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251008072892606256140215529 188256054669454692105161647)
    ·
      refine ⟨282384082004182038157742471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188256054669454692105161647 282384082004182038157742471)
      ·
        refine ⟨423576123006273057236613707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282384082004182038157742471 423576123006273057236613707)
        ·
          refine ⟨635364184509409585854920561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423576123006273057236613707 635364184509409585854920561)
          ·
            refine ⟨476523138382057189391190421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635364184509409585854920561 476523138382057189391190421)
            ·
              refine ⟨22337022111658930752712051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 476523138382057189391190421 22337022111658930752712051)
              ·
                refine ⟨33505533167488396129068077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22337022111658930752712051 33505533167488396129068077)
                ·
                  refine ⟨12564574937808148548400529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33505533167488396129068077 12564574937808148548400529)
                  ·
                    refine ⟨9423431203356111411300397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12564574937808148548400529 9423431203356111411300397)
                    ·
                      refine ⟨3533786701258541779237649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423431203356111411300397 3533786701258541779237649)
                      ·
                        rfl

theorem cell23_6882025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_6882025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882025 prefixEnd_6882025 := by exact prefixLift 6882025
  have htrace : WordTrace (prefixWord ++ tailWord_6882025) baseStart_6882025 baseEnd_6882025 := by
    simpa [prefixWord, tailWord_6882025, baseEnd_6882025] using wordTrace_append hprefix tailTrace_6882025
  have hstable : (prefixWord ++ tailWord_6882025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882025).length < 2 ^ (prefixWord ++ tailWord_6882025).sum := by decide
  have hdescent : baseEnd_6882025 < baseStart_6882025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882036 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6882036 : Nat := 118140960795 + 6882036 * 2 ^ 59
def prefixEnd_6882036 : Nat := 4983230072969 + 3 ^ 40 * 6882036 * 2
def baseEnd_6882036 : Nat := 1177930783181913745400033

theorem tailTrace_6882036 : CollatzResearch.WordTrace tailWord_6882036 prefixEnd_6882036 1177930783181913745400033 := by
  unfold tailWord_6882036
  simp only [CollatzResearch.WordTrace]
  refine ⟨125504237047783202509432981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167338982730377603345910641 125504237047783202509432981)
  ·
    refine ⟨5883011111614837617629671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 125504237047783202509432981 5883011111614837617629671)
    ·
      refine ⟨8824516667422256426444507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5883011111614837617629671 8824516667422256426444507)
      ·
        refine ⟨13236775001133384639666761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824516667422256426444507 13236775001133384639666761)
        ·
          refine ⟨9927581250850038479750071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13236775001133384639666761 9927581250850038479750071)
          ·
            refine ⟨14891371876275057719625107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9927581250850038479750071 14891371876275057719625107)
            ·
              refine ⟨22337057814412586579437661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14891371876275057719625107 22337057814412586579437661)
              ·
                refine ⟨8376396680404719967289123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22337057814412586579437661 8376396680404719967289123)
                ·
                  refine ⟨12564595020607079950933685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376396680404719967289123 12564595020607079950933685)
                  ·
                    refine ⟨1177930783181913745400033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12564595020607079950933685 1177930783181913745400033)
                    ·
                      rfl

theorem cell23_6882036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6882036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882036 prefixEnd_6882036 := by exact prefixLift 6882036
  have htrace : WordTrace (prefixWord ++ tailWord_6882036) baseStart_6882036 baseEnd_6882036 := by
    simpa [prefixWord, tailWord_6882036, baseEnd_6882036] using wordTrace_append hprefix tailTrace_6882036
  have hstable : (prefixWord ++ tailWord_6882036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882036).length < 2 ^ (prefixWord ++ tailWord_6882036).sum := by decide
  have hdescent : baseEnd_6882036 < baseStart_6882036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882056 : List Nat := [2, 1, 3, 2, 2, 2, 2, 4, 1, 2, 2]
def baseStart_6882056 : Nat := 118140960795 + 6882056 * 2 ^ 59
def prefixEnd_6882056 : Nat := 4983230072969 + 3 ^ 40 * 6882056 * 2
def baseEnd_6882056 : Nat := 3533802619158831157950007

theorem tailTrace_6882056 : CollatzResearch.WordTrace tailWord_6882056 prefixEnd_6882056 3533802619158831157950007 := by
  unfold tailWord_6882056
  simp only [CollatzResearch.WordTrace]
  refine ⟨125504601777746974217297011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167339469036995965623062681 125504601777746974217297011)
  ·
    refine ⟨188256902666620461325945517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125504601777746974217297011 188256902666620461325945517)
    ·
      refine ⟨70596338499982672997229569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188256902666620461325945517 70596338499982672997229569)
      ·
        refine ⟨52947253874987004747922177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70596338499982672997229569 52947253874987004747922177)
        ·
          refine ⟨39710440406240253560941633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52947253874987004747922177 39710440406240253560941633)
          ·
            refine ⟨29782830304680190170706225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39710440406240253560941633 29782830304680190170706225)
            ·
              refine ⟨22337122728510142628029669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29782830304680190170706225 22337122728510142628029669)
              ·
                refine ⟨4188210511595651742755563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22337122728510142628029669 4188210511595651742755563)
                ·
                  refine ⟨6282315767393477614133345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188210511595651742755563 6282315767393477614133345)
                  ·
                    refine ⟨4711736825545108210600009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6282315767393477614133345 4711736825545108210600009)
                    ·
                      refine ⟨3533802619158831157950007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711736825545108210600009 3533802619158831157950007)
                      ·
                        rfl

theorem cell23_6882056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_6882056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882056 prefixEnd_6882056 := by exact prefixLift 6882056
  have htrace : WordTrace (prefixWord ++ tailWord_6882056) baseStart_6882056 baseEnd_6882056 := by
    simpa [prefixWord, tailWord_6882056, baseEnd_6882056] using wordTrace_append hprefix tailTrace_6882056
  have hstable : (prefixWord ++ tailWord_6882056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882056).length < 2 ^ (prefixWord ++ tailWord_6882056).sum := by decide
  have hdescent : baseEnd_6882056 < baseStart_6882056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882066 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6882066 : Nat := 118140960795 + 6882066 * 2 ^ 59
def prefixEnd_6882066 : Nat := 4983230072969 + 3 ^ 40 * 6882066 * 2
def baseEnd_6882066 : Nat := 1177935917988458706274987

theorem tailTrace_6882066 : CollatzResearch.WordTrace tailWord_6882066 prefixEnd_6882066 1177935917988458706274987 := by
  unfold tailWord_6882066
  simp only [CollatzResearch.WordTrace]
  refine ⟨62752392071364430035614513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167339712190305146761638701 62752392071364430035614513)
  ·
    refine ⟨47064294053523322526710885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62752392071364430035614513 47064294053523322526710885)
    ·
      refine ⟨8824555135035622973758291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47064294053523322526710885 8824555135035622973758291)
      ·
        refine ⟨13236832702553434460637437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8824555135035622973758291 13236832702553434460637437)
        ·
          refine ⟨4963812263457537922739039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13236832702553434460637437 4963812263457537922739039)
          ·
            refine ⟨7445718395186306884108559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4963812263457537922739039 7445718395186306884108559)
            ·
              refine ⟨11168577592779460326162839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7445718395186306884108559 11168577592779460326162839)
              ·
                refine ⟨16752866389169190489244259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11168577592779460326162839 16752866389169190489244259)
                ·
                  refine ⟨25129299583753785733866389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16752866389169190489244259 25129299583753785733866389)
                  ·
                    refine ⟨1177935917988458706274987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25129299583753785733866389 1177935917988458706274987)
                    ·
                      rfl

theorem cell23_6882066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6882066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882066 prefixEnd_6882066 := by exact prefixLift 6882066
  have htrace : WordTrace (prefixWord ++ tailWord_6882066) baseStart_6882066 baseEnd_6882066 := by
    simpa [prefixWord, tailWord_6882066, baseEnd_6882066] using wordTrace_append hprefix tailTrace_6882066
  have hstable : (prefixWord ++ tailWord_6882066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882066).length < 2 ^ (prefixWord ++ tailWord_6882066).sum := by decide
  have hdescent : baseEnd_6882066 < baseStart_6882066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882099 : List Nat := [1, 1, 1, 2, 6, 1, 2, 3, 1, 3, 2]
def baseStart_6882099 : Nat := 118140960795 + 6882099 * 2 ^ 59
def prefixEnd_6882099 : Nat := 4983230072969 + 3 ^ 40 * 6882099 * 2
def baseEnd_6882099 : Nat := 3533824698826974489712309

theorem tailTrace_6882099 : CollatzResearch.WordTrace tailWord_6882099 prefixEnd_6882099 3533824698826974489712309 := by
  unfold tailWord_6882099
  simp only [CollatzResearch.WordTrace]
  refine ⟨251010771894338166778409351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167340514596225444518939567 251010771894338166778409351)
  ·
    refine ⟨376516157841507250167614027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251010771894338166778409351 376516157841507250167614027)
    ·
      refine ⟨564774236762260875251421041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376516157841507250167614027 564774236762260875251421041)
      ·
        refine ⟨423580677571695656438565781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564774236762260875251421041 423580677571695656438565781)
        ·
          refine ⟨19855344261173233895557771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 423580677571695656438565781 19855344261173233895557771)
          ·
            refine ⟨29783016391759850843336657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19855344261173233895557771 29783016391759850843336657)
            ·
              refine ⟨22337262293819888132502493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29783016391759850843336657 22337262293819888132502493)
              ·
                refine ⟨8376473360182458049688435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22337262293819888132502493 8376473360182458049688435)
                ·
                  refine ⟨12564710040273687074532653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376473360182458049688435 12564710040273687074532653)
                  ·
                    refine ⟨4711766265102632652949745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12564710040273687074532653 4711766265102632652949745)
                    ·
                      refine ⟨3533824698826974489712309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711766265102632652949745 3533824698826974489712309)
                      ·
                        rfl

theorem cell23_6882099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 3, 1, 3, 2].length) (baseStart_6882099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882099 prefixEnd_6882099 := by exact prefixLift 6882099
  have htrace : WordTrace (prefixWord ++ tailWord_6882099) baseStart_6882099 baseEnd_6882099 := by
    simpa [prefixWord, tailWord_6882099, baseEnd_6882099] using wordTrace_append hprefix tailTrace_6882099
  have hstable : (prefixWord ++ tailWord_6882099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882099).length < 2 ^ (prefixWord ++ tailWord_6882099).sum := by decide
  have hdescent : baseEnd_6882099 < baseStart_6882099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882115 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 3]
def baseStart_6882115 : Nat := 118140960795 + 6882115 * 2 ^ 59
def prefixEnd_6882115 : Nat := 4983230072969 + 3 ^ 40 * 6882115 * 2
def baseEnd_6882115 : Nat := 3533832914517446427112235

theorem tailTrace_6882115 : CollatzResearch.WordTrace tailWord_6882115 prefixEnd_6882115 3533832914517446427112235 := by
  unfold tailWord_6882115
  simp only [CollatzResearch.WordTrace]
  refine ⟨251011355462280201510991799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167340903641520134340661199 251011355462280201510991799)
  ·
    refine ⟨376517033193420302266487699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251011355462280201510991799 376517033193420302266487699)
    ·
      refine ⟨564775549790130453399731549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376517033193420302266487699 564775549790130453399731549)
      ·
        refine ⟨211790831171298920024899331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564775549790130453399731549 211790831171298920024899331)
        ·
          refine ⟨317686246756948380037348997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211790831171298920024899331 317686246756948380037348997)
          ·
            refine ⟨59566171266927821257002937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 317686246756948380037348997 59566171266927821257002937)
            ·
              refine ⟨44674628450195865942752203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59566171266927821257002937 44674628450195865942752203)
              ·
                refine ⟨67011942675293798914128305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44674628450195865942752203 67011942675293798914128305)
                ·
                  refine ⟨50258957006470349185596229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67011942675293798914128305 50258957006470349185596229)
                  ·
                    refine ⟨9423554438713190472299293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50258957006470349185596229 9423554438713190472299293)
                    ·
                      refine ⟨3533832914517446427112235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423554438713190472299293 3533832914517446427112235)
                      ·
                        rfl

theorem cell23_6882115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_6882115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882115 prefixEnd_6882115 := by exact prefixLift 6882115
  have htrace : WordTrace (prefixWord ++ tailWord_6882115) baseStart_6882115 baseEnd_6882115 := by
    simpa [prefixWord, tailWord_6882115, baseEnd_6882115] using wordTrace_append hprefix tailTrace_6882115
  have hstable : (prefixWord ++ tailWord_6882115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882115).length < 2 ^ (prefixWord ++ tailWord_6882115).sum := by decide
  have hdescent : baseEnd_6882115 < baseStart_6882115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882145 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 3]
def baseStart_6882145 : Nat := 118140960795 + 6882145 * 2 ^ 59
def prefixEnd_6882145 : Nat := 4983230072969 + 3 ^ 40 * 6882145 * 2
def baseEnd_6882145 : Nat := 3533848318937081309737097

theorem tailTrace_6882145 : CollatzResearch.WordTrace tailWord_6882145 prefixEnd_6882145 3533848318937081309737097 := by
  unfold tailWord_6882145
  simp only [CollatzResearch.WordTrace]
  refine ⟨251012449652171516634583889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167341633101447677756389259 251012449652171516634583889)
  ·
    refine ⟨188259337239128637475937917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251012449652171516634583889 188259337239128637475937917)
    ·
      refine ⟨70597251464673239053476719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188259337239128637475937917 70597251464673239053476719)
      ·
        refine ⟨105895877197009858580215079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70597251464673239053476719 105895877197009858580215079)
        ·
          refine ⟨158843815795514787870322619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105895877197009858580215079 158843815795514787870322619)
          ·
            refine ⟨238265723693272181805483929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158843815795514787870322619 238265723693272181805483929)
            ·
              refine ⟨178699292769954136354112947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238265723693272181805483929 178699292769954136354112947)
              ·
                refine ⟨268048939154931204531169421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178699292769954136354112947 268048939154931204531169421)
                ·
                  refine ⟨100518352183099201699188533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 268048939154931204531169421 100518352183099201699188533)
                  ·
                    refine ⟨9423595517165550159298925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100518352183099201699188533 9423595517165550159298925)
                    ·
                      refine ⟨3533848318937081309737097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423595517165550159298925 3533848318937081309737097)
                      ·
                        rfl

theorem cell23_6882145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_6882145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882145 prefixEnd_6882145 := by exact prefixLift 6882145
  have htrace : WordTrace (prefixWord ++ tailWord_6882145) baseStart_6882145 baseEnd_6882145 := by
    simpa [prefixWord, tailWord_6882145, baseEnd_6882145] using wordTrace_append hprefix tailTrace_6882145
  have hstable : (prefixWord ++ tailWord_6882145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882145).length < 2 ^ (prefixWord ++ tailWord_6882145).sum := by decide
  have hdescent : baseEnd_6882145 < baseStart_6882145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882146 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_6882146 : Nat := 118140960795 + 6882146 * 2 ^ 59
def prefixEnd_6882146 : Nat := 4983230072969 + 3 ^ 40 * 6882146 * 2
def baseEnd_6882146 : Nat := 3533848832417735805824593

theorem tailTrace_6882146 : CollatzResearch.WordTrace tailWord_6882146 prefixEnd_6882146 3533848832417735805824593 := by
  unfold tailWord_6882146
  simp only [CollatzResearch.WordTrace]
  refine ⟨62753121531291973451342573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167341657416778595870246861 62753121531291973451342573)
  ·
    refine ⟨23532420574234490044253465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62753121531291973451342573 23532420574234490044253465)
    ·
      refine ⟨17649315430675867533190099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23532420574234490044253465 17649315430675867533190099)
      ·
        refine ⟨26473973146013801299785149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17649315430675867533190099 26473973146013801299785149)
        ·
          refine ⟨9927739929755175487419431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26473973146013801299785149 9927739929755175487419431)
          ·
            refine ⟨14891609894632763231129147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9927739929755175487419431 14891609894632763231129147)
            ·
              refine ⟨22337414841949144846693721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14891609894632763231129147 22337414841949144846693721)
              ·
                refine ⟨16753061131461858635020291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22337414841949144846693721 16753061131461858635020291)
                ·
                  refine ⟨25129591697192787952530437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16753061131461858635020291 25129591697192787952530437)
                  ·
                    refine ⟨4711798443223647741099457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25129591697192787952530437 4711798443223647741099457)
                    ·
                      refine ⟨3533848832417735805824593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711798443223647741099457 3533848832417735805824593)
                      ·
                        rfl

theorem cell23_6882146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_6882146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882146 prefixEnd_6882146 := by exact prefixLift 6882146
  have htrace : WordTrace (prefixWord ++ tailWord_6882146) baseStart_6882146 baseEnd_6882146 := by
    simpa [prefixWord, tailWord_6882146, baseEnd_6882146] using wordTrace_append hprefix tailTrace_6882146
  have hstable : (prefixWord ++ tailWord_6882146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882146).length < 2 ^ (prefixWord ++ tailWord_6882146).sum := by decide
  have hdescent : baseEnd_6882146 < baseStart_6882146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882169 : List Nat := [1, 2, 1, 3, 2, 3, 4, 2, 5]
def baseStart_6882169 : Nat := 118140960795 + 6882169 * 2 ^ 59
def prefixEnd_6882169 : Nat := 4983230072969 + 3 ^ 40 * 6882169 * 2
def baseEnd_6882169 : Nat := 392651182496976579537443

theorem tailTrace_6882169 : CollatzResearch.WordTrace tailWord_6882169 prefixEnd_6882169 392651182496976579537443 := by
  unfold tailWord_6882169
  simp only [CollatzResearch.WordTrace]
  refine ⟨251013325004084568733457561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167342216669389712488971707 251013325004084568733457561)
  ·
    refine ⟨188259993753063426550093171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251013325004084568733457561 188259993753063426550093171)
    ·
      refine ⟨282389990629595139825139757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188259993753063426550093171 282389990629595139825139757)
      ·
        refine ⟨105896246486098177434427409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282389990629595139825139757 105896246486098177434427409)
        ·
          refine ⟨79422184864573633075820557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105896246486098177434427409 79422184864573633075820557)
          ·
            refine ⟨29783319324215112403432709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79422184864573633075820557 29783319324215112403432709)
            ·
              refine ⟨5584372373290333575643633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29783319324215112403432709 5584372373290333575643633)
              ·
                refine ⟨4188279279967750181732725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5584372373290333575643633 4188279279967750181732725)
                ·
                  refine ⟨392651182496976579537443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4188279279967750181732725 392651182496976579537443)
                  ·
                    rfl

theorem cell23_6882169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 5].length) (baseStart_6882169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882169 prefixEnd_6882169 := by exact prefixLift 6882169
  have htrace : WordTrace (prefixWord ++ tailWord_6882169) baseStart_6882169 baseEnd_6882169 := by
    simpa [prefixWord, tailWord_6882169, baseEnd_6882169] using wordTrace_append hprefix tailTrace_6882169
  have hstable : (prefixWord ++ tailWord_6882169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882169).length < 2 ^ (prefixWord ++ tailWord_6882169).sum := by decide
  have hdescent : baseEnd_6882169 < baseStart_6882169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882175 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 5]
def baseStart_6882175 : Nat := 118140960795 + 6882175 * 2 ^ 59
def prefixEnd_6882175 : Nat := 4983230072969 + 3 ^ 40 * 6882175 * 2
def baseEnd_6882175 : Nat := 3533863723356716192361959

theorem tailTrace_6882175 : CollatzResearch.WordTrace tailWord_6882175 prefixEnd_6882175 3533863723356716192361959 := by
  unfold tailWord_6882175
  simp only [CollatzResearch.WordTrace]
  refine ⟨251013543842062831758175979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167342362561375221172117319 251013543842062831758175979)
  ·
    refine ⟨376520315763094247637263969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251013543842062831758175979 376520315763094247637263969)
    ·
      refine ⟨282390236822320685727947977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376520315763094247637263969 282390236822320685727947977)
      ·
        refine ⟨211792677616740514295960983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282390236822320685727947977 211792677616740514295960983)
        ·
          refine ⟨317689016425110771443941475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211792677616740514295960983 317689016425110771443941475)
          ·
            refine ⟨476533524637666157165912213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317689016425110771443941475 476533524637666157165912213)
            ·
              refine ⟨22337508967390601117152135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 476533524637666157165912213 22337508967390601117152135)
              ·
                refine ⟨33506263451085901675728203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22337508967390601117152135 33506263451085901675728203)
                ·
                  refine ⟨50259395176628852513592305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33506263451085901675728203 50259395176628852513592305)
                  ·
                    refine ⟨37694546382471639385194229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50259395176628852513592305 37694546382471639385194229)
                    ·
                      refine ⟨3533863723356716192361959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37694546382471639385194229 3533863723356716192361959)
                      ·
                        rfl

theorem cell23_6882175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_6882175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882175 prefixEnd_6882175 := by exact prefixLift 6882175
  have htrace : WordTrace (prefixWord ++ tailWord_6882175) baseStart_6882175 baseEnd_6882175 := by
    simpa [prefixWord, tailWord_6882175, baseEnd_6882175] using wordTrace_append hprefix tailTrace_6882175
  have hstable : (prefixWord ++ tailWord_6882175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882175).length < 2 ^ (prefixWord ++ tailWord_6882175).sum := by decide
  have hdescent : baseEnd_6882175 < baseStart_6882175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882212 : List Nat := [2, 3, 1, 2, 1, 2, 1, 2, 5, 4]
def baseStart_6882212 : Nat := 118140960795 + 6882212 * 2 ^ 59
def prefixEnd_6882212 : Nat := 4983230072969 + 3 ^ 40 * 6882212 * 2
def baseEnd_6882212 : Nat := 1177960907380310849199763

theorem tailTrace_6882212 : CollatzResearch.WordTrace tailWord_6882212 prefixEnd_6882212 1177960907380310849199763 := by
  unfold tailWord_6882212
  simp only [CollatzResearch.WordTrace]
  refine ⟨125507446671464393538636445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167343262228619191384848593 125507446671464393538636445)
  ·
    refine ⟨47065292501799147576988667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125507446671464393538636445 47065292501799147576988667)
    ·
      refine ⟨70597938752698721365483001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47065292501799147576988667 70597938752698721365483001)
      ·
        refine ⟨52948454064524041024112251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70597938752698721365483001 52948454064524041024112251)
        ·
          refine ⟨79422681096786061536168377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52948454064524041024112251 79422681096786061536168377)
          ·
            refine ⟨59567010822589546152126283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79422681096786061536168377 59567010822589546152126283)
            ·
              refine ⟨89350516233884319228189425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59567010822589546152126283 89350516233884319228189425)
              ·
                refine ⟨67012887175413239421142069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89350516233884319228189425 67012887175413239421142069)
                ·
                  refine ⟨6282458172694991195732069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67012887175413239421142069 6282458172694991195732069)
                  ·
                    refine ⟨1177960907380310849199763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6282458172694991195732069 1177960907380310849199763)
                    ·
                      rfl

theorem cell23_6882212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 2, 5, 4].length) (baseStart_6882212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882212 prefixEnd_6882212 := by exact prefixLift 6882212
  have htrace : WordTrace (prefixWord ++ tailWord_6882212) baseStart_6882212 baseEnd_6882212 := by
    simpa [prefixWord, tailWord_6882212, baseEnd_6882212] using wordTrace_append hprefix tailTrace_6882212
  have hstable : (prefixWord ++ tailWord_6882212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882212).length < 2 ^ (prefixWord ++ tailWord_6882212).sum := by decide
  have hdescent : baseEnd_6882212 < baseStart_6882212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882229 : List Nat := [1, 3, 3, 2, 1, 1, 4, 1, 3, 4]
def baseStart_6882229 : Nat := 118140960795 + 6882229 * 2 ^ 59
def prefixEnd_6882229 : Nat := 4983230072969 + 3 ^ 40 * 6882229 * 2
def baseEnd_6882229 : Nat := 1177963817104019660362237

theorem tailTrace_6882229 : CollatzResearch.WordTrace tailWord_6882229 prefixEnd_6882229 1177963817104019660362237 := by
  unfold tailWord_6882229
  simp only [CollatzResearch.WordTrace]
  refine ⟨251015513383867198980641741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167343675589244799320427827 251015513383867198980641741)
  ·
    refine ⟨94130817518950199617740653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251015513383867198980641741 94130817518950199617740653)
    ·
      refine ⟨35299056569606324856652745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94130817518950199617740653 35299056569606324856652745)
      ·
        refine ⟨26474292427204743642489559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35299056569606324856652745 26474292427204743642489559)
        ·
          refine ⟨39711438640807115463734339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26474292427204743642489559 39711438640807115463734339)
          ·
            refine ⟨59567157961210673195601509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39711438640807115463734339 59567157961210673195601509)
            ·
              refine ⟨11168842117727001224175283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59567157961210673195601509 11168842117727001224175283)
              ·
                refine ⟨16753263176590501836262925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11168842117727001224175283 16753263176590501836262925)
                ·
                  refine ⟨6282473691221438188598597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16753263176590501836262925 6282473691221438188598597)
                  ·
                    refine ⟨1177963817104019660362237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6282473691221438188598597 1177963817104019660362237)
                    ·
                      rfl

theorem cell23_6882229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_6882229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882229 prefixEnd_6882229 := by exact prefixLift 6882229
  have htrace : WordTrace (prefixWord ++ tailWord_6882229) baseStart_6882229 baseEnd_6882229 := by
    simpa [prefixWord, tailWord_6882229, baseEnd_6882229] using wordTrace_append hprefix tailTrace_6882229
  have hstable : (prefixWord ++ tailWord_6882229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882229).length < 2 ^ (prefixWord ++ tailWord_6882229).sum := by decide
  have hdescent : baseEnd_6882229 < baseStart_6882229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882252 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_6882252 : Nat := 118140960795 + 6882252 * 2 ^ 59
def prefixEnd_6882252 : Nat := 4983230072969 + 3 ^ 40 * 6882252 * 2
def baseEnd_6882252 : Nat := 3533903261367112391099105

theorem tailTrace_6882252 : CollatzResearch.WordTrace tailWord_6882252 prefixEnd_6882252 3533903261367112391099105 := by
  unfold tailWord_6882252
  simp only [CollatzResearch.WordTrace]
  refine ⟨125508176131391936954364505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167344234841855915939152673 125508176131391936954364505)
  ·
    refine ⟨94131132098543952715773379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125508176131391936954364505 94131132098543952715773379)
    ·
      refine ⟨141196698147815929073660069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94131132098543952715773379 141196698147815929073660069)
      ·
        refine ⟨26474380902715486701311263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141196698147815929073660069 26474380902715486701311263)
        ·
          refine ⟨39711571354073230051966895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26474380902715486701311263 39711571354073230051966895)
          ·
            refine ⟨59567357031109845077950343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39711571354073230051966895 59567357031109845077950343)
            ·
              refine ⟨89351035546664767616925515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59567357031109845077950343 89351035546664767616925515)
              ·
                refine ⟨134026553319997151425388273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89351035546664767616925515 134026553319997151425388273)
                ·
                  refine ⟨100519914989997863569041205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 134026553319997151425388273 100519914989997863569041205)
                  ·
                    refine ⟨9423742030312299709597613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100519914989997863569041205 9423742030312299709597613)
                    ·
                      refine ⟨3533903261367112391099105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423742030312299709597613 3533903261367112391099105)
                      ·
                        rfl

theorem cell23_6882252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_6882252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882252 prefixEnd_6882252 := by exact prefixLift 6882252
  have htrace : WordTrace (prefixWord ++ tailWord_6882252) baseStart_6882252 baseEnd_6882252 := by
    simpa [prefixWord, tailWord_6882252, baseEnd_6882252] using wordTrace_append hprefix tailTrace_6882252
  have hstable : (prefixWord ++ tailWord_6882252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882252).length < 2 ^ (prefixWord ++ tailWord_6882252).sum := by decide
  have hdescent : baseEnd_6882252 < baseStart_6882252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882329 : List Nat := [1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 3]
def baseStart_6882329 : Nat := 118140960795 + 6882329 * 2 ^ 59
def prefixEnd_6882329 : Nat := 4983230072969 + 3 ^ 40 * 6882329 * 2
def baseEnd_6882329 : Nat := 3533942799377508589836251

theorem tailTrace_6882329 : CollatzResearch.WordTrace tailWord_6882329 prefixEnd_6882329 3533942799377508589836251 := by
  unfold tailWord_6882329
  simp only [CollatzResearch.WordTrace]
  refine ⟨251019160683504916059282041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167346107122336610706188027 251019160683504916059282041)
  ·
    refine ⟨188264370512628687044461531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251019160683504916059282041 188264370512628687044461531)
    ·
      refine ⟨282396555768943030566692297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188264370512628687044461531 282396555768943030566692297)
      ·
        refine ⟨211797416826707272925019223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282396555768943030566692297 211797416826707272925019223)
        ·
          refine ⟨317696125240060909387528835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211797416826707272925019223 317696125240060909387528835)
          ·
            refine ⟨476544187860091364081293253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317696125240060909387528835 476544187860091364081293253)
            ·
              refine ⟨89352035223767130765242485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 476544187860091364081293253 89352035223767130765242485)
              ·
                refine ⟨8376753302228168509241483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89352035223767130765242485 8376753302228168509241483)
                ·
                  refine ⟨12565129953342252763862225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8376753302228168509241483 12565129953342252763862225)
                  ·
                    refine ⟨9423847465006689572896669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12565129953342252763862225 9423847465006689572896669)
                    ·
                      refine ⟨3533942799377508589836251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423847465006689572896669 3533942799377508589836251)
                      ·
                        rfl

theorem cell23_6882329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_6882329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882329 prefixEnd_6882329 := by exact prefixLift 6882329
  have htrace : WordTrace (prefixWord ++ tailWord_6882329) baseStart_6882329 baseEnd_6882329 := by
    simpa [prefixWord, tailWord_6882329, baseEnd_6882329] using wordTrace_append hprefix tailTrace_6882329
  have hstable : (prefixWord ++ tailWord_6882329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882329).length < 2 ^ (prefixWord ++ tailWord_6882329).sum := by decide
  have hdescent : baseEnd_6882329 < baseStart_6882329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882332 : List Nat := [2, 2, 3, 1, 4, 11]
def baseStart_6882332 : Nat := 118140960795 + 6882332 * 2 ^ 59
def prefixEnd_6882332 : Nat := 4983230072969 + 3 ^ 40 * 6882332 * 2
def baseEnd_6882332 : Nat := 14542980822302354230859

theorem tailTrace_6882332 : CollatzResearch.WordTrace tailWord_6882332 prefixEnd_6882332 14542980822302354230859 := by
  unfold tailWord_6882332
  simp only [CollatzResearch.WordTrace]
  refine ⟨125509635051247023785820625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167346180068329365047760833 125509635051247023785820625)
  ·
    refine ⟨94132226288435267839365469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125509635051247023785820625 94132226288435267839365469)
    ·
      refine ⟨35299584858163225439762051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94132226288435267839365469 35299584858163225439762051)
      ·
        refine ⟨52949377287244838159643077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35299584858163225439762051 52949377287244838159643077)
        ·
          refine ⟨9928008241358407154933077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52949377287244838159643077 9928008241358407154933077)
          ·
            refine ⟨14542980822302354230859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9928008241358407154933077 14542980822302354230859)
            ·
              rfl

theorem cell23_6882332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 11].length) (baseStart_6882332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882332 prefixEnd_6882332 := by exact prefixLift 6882332
  have htrace : WordTrace (prefixWord ++ tailWord_6882332) baseStart_6882332 baseEnd_6882332 := by
    simpa [prefixWord, tailWord_6882332, baseEnd_6882332] using wordTrace_append hprefix tailTrace_6882332
  have hstable : (prefixWord ++ tailWord_6882332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882332).length < 2 ^ (prefixWord ++ tailWord_6882332).sum := by decide
  have hdescent : baseEnd_6882332 < baseStart_6882332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882356 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_6882356 : Nat := 118140960795 + 6882356 * 2 ^ 59
def prefixEnd_6882356 : Nat := 4983230072969 + 3 ^ 40 * 6882356 * 2
def baseEnd_6882356 : Nat := 3533956663355179984198627

theorem tailTrace_6882356 : CollatzResearch.WordTrace tailWord_6882356 prefixEnd_6882356 3533956663355179984198627 := by
  unfold tailWord_6882356
  simp only [CollatzResearch.WordTrace]
  refine ⟨125510072727203549835257461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167346763636271399780343281 125510072727203549835257461)
  ·
    refine ⟨11766569318175332797055387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 125510072727203549835257461 11766569318175332797055387)
    ·
      refine ⟨17649853977262999195583081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11766569318175332797055387 17649853977262999195583081)
      ·
        refine ⟨13237390482947249396687311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17649853977262999195583081 13237390482947249396687311)
        ·
          refine ⟨19856085724420874095030967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13237390482947249396687311 19856085724420874095030967)
          ·
            refine ⟨29784128586631311142546451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19856085724420874095030967 29784128586631311142546451)
            ·
              refine ⟨44676192879946966713819677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29784128586631311142546451 44676192879946966713819677)
              ·
                refine ⟨16753572329980112517682379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44676192879946966713819677 16753572329980112517682379)
                ·
                  refine ⟨25130358494970168776523569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16753572329980112517682379 25130358494970168776523569)
                  ·
                    refine ⟨18847768871227626582392677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25130358494970168776523569 18847768871227626582392677)
                    ·
                      refine ⟨3533956663355179984198627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18847768871227626582392677 3533956663355179984198627)
                      ·
                        rfl

theorem cell23_6882356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_6882356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882356 prefixEnd_6882356 := by exact prefixLift 6882356
  have htrace : WordTrace (prefixWord ++ tailWord_6882356) baseStart_6882356 baseEnd_6882356 := by
    simpa [prefixWord, tailWord_6882356, baseEnd_6882356] using wordTrace_append hprefix tailTrace_6882356
  have hstable : (prefixWord ++ tailWord_6882356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882356).length < 2 ^ (prefixWord ++ tailWord_6882356).sum := by decide
  have hdescent : baseEnd_6882356 < baseStart_6882356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882359 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 3]
def baseStart_6882359 : Nat := 118140960795 + 6882359 * 2 ^ 59
def prefixEnd_6882359 : Nat := 4983230072969 + 3 ^ 40 * 6882359 * 2
def baseEnd_6882359 : Nat := 3533958203797143472461113

theorem tailTrace_6882359 : CollatzResearch.WordTrace tailWord_6882359 prefixEnd_6882359 3533958203797143472461113 := by
  unfold tailWord_6882359
  simp only [CollatzResearch.WordTrace]
  refine ⟨251020254873396231182874131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167346836582264154121916087 251020254873396231182874131)
  ·
    refine ⟨376530382310094346774311197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251020254873396231182874131 376530382310094346774311197)
    ·
      refine ⟨141198893366285380040366699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376530382310094346774311197 141198893366285380040366699)
      ·
        refine ⟨211798340049428070060550049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141198893366285380040366699 211798340049428070060550049)
        ·
          refine ⟨158848755037071052545412537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211798340049428070060550049 158848755037071052545412537)
          ·
            refine ⟨119136566277803289409059403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158848755037071052545412537 119136566277803289409059403)
            ·
              refine ⟨178704849416704934113589105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119136566277803289409059403 178704849416704934113589105)
              ·
                refine ⟨134028637062528700585191829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178704849416704934113589105 134028637062528700585191829)
                ·
                  refine ⟨6282592362306032839930867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134028637062528700585191829 6282592362306032839930867)
                  ·
                    refine ⟨9423888543459049259896301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6282592362306032839930867 9423888543459049259896301)
                    ·
                      refine ⟨3533958203797143472461113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423888543459049259896301 3533958203797143472461113)
                      ·
                        rfl

theorem cell23_6882359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6, 1, 3].length) (baseStart_6882359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882359 prefixEnd_6882359 := by exact prefixLift 6882359
  have htrace : WordTrace (prefixWord ++ tailWord_6882359) baseStart_6882359 baseEnd_6882359 := by
    simpa [prefixWord, tailWord_6882359, baseEnd_6882359] using wordTrace_append hprefix tailTrace_6882359
  have hstable : (prefixWord ++ tailWord_6882359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882359).length < 2 ^ (prefixWord ++ tailWord_6882359).sum := by decide
  have hdescent : baseEnd_6882359 < baseStart_6882359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882366 : List Nat := [4, 2, 1, 3, 1, 2, 3, 7]
def baseStart_6882366 : Nat := 118140960795 + 6882366 * 2 ^ 59
def prefixEnd_6882366 : Nat := 4983230072969 + 3 ^ 40 * 6882366 * 2
def baseEnd_6882366 : Nat := 130887474005989812780503

theorem tailTrace_6882366 : CollatzResearch.WordTrace tailWord_6882366 prefixEnd_6882366 130887474005989812780503 := by
  unfold tailWord_6882366
  simp only [CollatzResearch.WordTrace]
  refine ⟨31377563773046358922297369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167347006789580580918919301 31377563773046358922297369)
  ·
    refine ⟨23533172829784769191723027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31377563773046358922297369 23533172829784769191723027)
    ·
      refine ⟨35299759244677153787584541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23533172829784769191723027 35299759244677153787584541)
      ·
        refine ⟨13237409716753932670344203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35299759244677153787584541 13237409716753932670344203)
        ·
          refine ⟨19856114575130899005516305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13237409716753932670344203 19856114575130899005516305)
          ·
            refine ⟨14892085931348174254137229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19856114575130899005516305 14892085931348174254137229)
            ·
              refine ⟨5584532224255565345301461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14892085931348174254137229 5584532224255565345301461)
              ·
                refine ⟨130887474005989812780503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5584532224255565345301461 130887474005989812780503)
                ·
                  rfl

theorem cell23_6882366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 7].length) (baseStart_6882366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882366 prefixEnd_6882366 := by exact prefixLift 6882366
  have htrace : WordTrace (prefixWord ++ tailWord_6882366) baseStart_6882366 baseEnd_6882366 := by
    simpa [prefixWord, tailWord_6882366, baseEnd_6882366] using wordTrace_append hprefix tailTrace_6882366
  have hstable : (prefixWord ++ tailWord_6882366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882366).length < 2 ^ (prefixWord ++ tailWord_6882366).sum := by decide
  have hdescent : baseEnd_6882366 < baseStart_6882366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882392 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 4, 6]
def baseStart_6882392 : Nat := 118140960795 + 6882392 * 2 ^ 59
def prefixEnd_6882392 : Nat := 4983230072969 + 3 ^ 40 * 6882392 * 2
def baseEnd_6882392 : Nat := 1177991716219580614449487

theorem tailTrace_6882392 : CollatzResearch.WordTrace tailWord_6882392 prefixEnd_6882392 1177991716219580614449487 := by
  unfold tailWord_6882392
  simp only [CollatzResearch.WordTrace]
  refine ⟨125510729241138338909412715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167347638988184451879216953 125510729241138338909412715)
  ·
    refine ⟨188266093861707508364119073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125510729241138338909412715 188266093861707508364119073)
    ·
      refine ⟨141199570396280631273089305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188266093861707508364119073 141199570396280631273089305)
      ·
        refine ⟨105899677797210473454816979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141199570396280631273089305 105899677797210473454816979)
        ·
          refine ⟨158849516695815710182225469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105899677797210473454816979 158849516695815710182225469)
          ·
            refine ⟨59568568760930891318334551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158849516695815710182225469 59568568760930891318334551)
            ·
              refine ⟨89352853141396336977501827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59568568760930891318334551 89352853141396336977501827)
              ·
                refine ⟨134029279712094505466252741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89352853141396336977501827 134029279712094505466252741)
                ·
                  refine ⟨25130489946017719774922389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134029279712094505466252741 25130489946017719774922389)
                  ·
                    refine ⟨1177991716219580614449487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25130489946017719774922389 1177991716219580614449487)
                    ·
                      rfl

theorem cell23_6882392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 4, 6].length) (baseStart_6882392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882392 prefixEnd_6882392 := by exact prefixLift 6882392
  have htrace : WordTrace (prefixWord ++ tailWord_6882392) baseStart_6882392 baseEnd_6882392 := by
    simpa [prefixWord, tailWord_6882392, baseEnd_6882392] using wordTrace_append hprefix tailTrace_6882392
  have hstable : (prefixWord ++ tailWord_6882392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882392).length < 2 ^ (prefixWord ++ tailWord_6882392).sum := by decide
  have hdescent : baseEnd_6882392 < baseStart_6882392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882410 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_6882410 : Nat := 118140960795 + 6882410 * 2 ^ 59
def prefixEnd_6882410 : Nat := 4983230072969 + 3 ^ 40 * 6882410 * 2
def baseEnd_6882410 : Nat := 3533984391310522772923379

theorem tailTrace_6882410 : CollatzResearch.WordTrace tailWord_6882410 prefixEnd_6882410 3533984391310522772923379 := by
  unfold tailWord_6882410
  simp only [CollatzResearch.WordTrace]
  refine ⟨62755528749052866723245171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167348076664140977928653789 62755528749052866723245171)
  ·
    refine ⟨94133293123579300084867757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62755528749052866723245171 94133293123579300084867757)
    ·
      refine ⟨35299984921342237531825409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94133293123579300084867757 35299984921342237531825409)
      ·
        refine ⟨26474988691006678148869057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35299984921342237531825409 26474988691006678148869057)
        ·
          refine ⟨19856241518255008611651793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26474988691006678148869057 19856241518255008611651793)
          ·
            refine ⟨14892181138691256458738845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19856241518255008611651793 14892181138691256458738845)
            ·
              refine ⟨5584567927009221172027067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14892181138691256458738845 5584567927009221172027067)
              ·
                refine ⟨8376851890513831758040601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5584567927009221172027067 8376851890513831758040601)
                ·
                  refine ⟨6282638917885373818530451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8376851890513831758040601 6282638917885373818530451)
                  ·
                    refine ⟨9423958376828060727795677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6282638917885373818530451 9423958376828060727795677)
                    ·
                      refine ⟨3533984391310522772923379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9423958376828060727795677 3533984391310522772923379)
                      ·
                        rfl

theorem cell23_6882410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_6882410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882410 prefixEnd_6882410 := by exact prefixLift 6882410
  have htrace : WordTrace (prefixWord ++ tailWord_6882410) baseStart_6882410 baseEnd_6882410 := by
    simpa [prefixWord, tailWord_6882410, baseEnd_6882410] using wordTrace_append hprefix tailTrace_6882410
  have hstable : (prefixWord ++ tailWord_6882410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882410).length < 2 ^ (prefixWord ++ tailWord_6882410).sum := by decide
  have hdescent : baseEnd_6882410 < baseStart_6882410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882433 : List Nat := [1, 2, 4, 2, 2, 1, 1, 2, 4, 2, 2]
def baseStart_6882433 : Nat := 118140960795 + 6882433 * 2 ^ 59
def prefixEnd_6882433 : Nat := 4983230072969 + 3 ^ 40 * 6882433 * 2
def baseEnd_6882433 : Nat := 3533996201365576182935773

theorem tailTrace_6882433 : CollatzResearch.WordTrace tailWord_6882433 prefixEnd_6882433 3533996201365576182935773 := by
  unfold tailWord_6882433
  simp only [CollatzResearch.WordTrace]
  refine ⟨251022953875128141821067953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167348635916752094547378635 251022953875128141821067953)
  ·
    refine ⟨188267215406346106365800965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251022953875128141821067953 188267215406346106365800965)
    ·
      refine ⟨35300102888689894943587681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188267215406346106365800965 35300102888689894943587681)
      ·
        refine ⟨26475077166517421207690761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35300102888689894943587681 26475077166517421207690761)
        ·
          refine ⟨19856307874888065905768071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26475077166517421207690761 19856307874888065905768071)
          ·
            refine ⟨29784461812332098858652107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19856307874888065905768071 29784461812332098858652107)
            ·
              refine ⟨44676692718498148287978161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29784461812332098858652107 44676692718498148287978161)
              ·
                refine ⟨33507519538873611215983621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44676692718498148287978161 33507519538873611215983621)
                ·
                  refine ⟨6282659913538802102996929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33507519538873611215983621 6282659913538802102996929)
                  ·
                    refine ⟨4711994935154101577247697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6282659913538802102996929 4711994935154101577247697)
                    ·
                      refine ⟨3533996201365576182935773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4711994935154101577247697 3533996201365576182935773)
                      ·
                        rfl

theorem cell23_6882433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_6882433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882433 prefixEnd_6882433 := by exact prefixLift 6882433
  have htrace : WordTrace (prefixWord ++ tailWord_6882433) baseStart_6882433 baseEnd_6882433 := by
    simpa [prefixWord, tailWord_6882433, baseEnd_6882433] using wordTrace_append hprefix tailTrace_6882433
  have hstable : (prefixWord ++ tailWord_6882433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882433).length < 2 ^ (prefixWord ++ tailWord_6882433).sum := by decide
  have hdescent : baseEnd_6882433 < baseStart_6882433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882456 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 7]
def baseStart_6882456 : Nat := 118140960795 + 6882456 * 2 ^ 59
def prefixEnd_6882456 : Nat := 4983230072969 + 3 ^ 40 * 6882456 * 2
def baseEnd_6882456 : Nat := 392667556824514399216463

theorem tailTrace_6882456 : CollatzResearch.WordTrace tailWord_6882456 prefixEnd_6882456 392667556824514399216463 := by
  unfold tailWord_6882456
  simp only [CollatzResearch.WordTrace]
  refine ⟨125511896377022408374577611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167349195169363211166103481 125511896377022408374577611)
  ·
    refine ⟨188267844565533612561866417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125511896377022408374577611 188267844565533612561866417)
    ·
      refine ⟨141200883424150209421399813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188267844565533612561866417 141200883424150209421399813)
      ·
        refine ⟨26475165642028164266512465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141200883424150209421399813 26475165642028164266512465)
        ·
          refine ⟨19856374231521123199884349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26475165642028164266512465 19856374231521123199884349)
          ·
            refine ⟨7446140336820421199956631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19856374231521123199884349 7446140336820421199956631)
            ·
              refine ⟨11169210505230631799934947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446140336820421199956631 11169210505230631799934947)
              ·
                refine ⟨16753815757845947699902421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11169210505230631799934947 16753815757845947699902421)
                ·
                  refine ⟨392667556824514399216463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16753815757845947699902421 392667556824514399216463)
                  ·
                    rfl

theorem cell23_6882456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 7].length) (baseStart_6882456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882456 prefixEnd_6882456 := by exact prefixLift 6882456
  have htrace : WordTrace (prefixWord ++ tailWord_6882456) baseStart_6882456 baseEnd_6882456 := by
    simpa [prefixWord, tailWord_6882456, baseEnd_6882456] using wordTrace_append hprefix tailTrace_6882456
  have hstable : (prefixWord ++ tailWord_6882456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882456).length < 2 ^ (prefixWord ++ tailWord_6882456).sum := by decide
  have hdescent : baseEnd_6882456 < baseStart_6882456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882499 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 7, 4]
def baseStart_6882499 : Nat := 118140960795 + 6882499 * 2 ^ 59
def prefixEnd_6882499 : Nat := 4983230072969 + 3 ^ 40 * 6882499 * 2
def baseEnd_6882499 : Nat := 1178010030362924308236823

theorem tailTrace_6882499 : CollatzResearch.WordTrace tailWord_6882499 prefixEnd_6882499 1178010030362924308236823 := by
  unfold tailWord_6882499
  simp only [CollatzResearch.WordTrace]
  refine ⟨251025361092889035092970551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167350240728592690061980367 251025361092889035092970551)
  ·
    refine ⟨376538041639333552639455827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251025361092889035092970551 376538041639333552639455827)
    ·
      refine ⟨564807062459000328959183741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376538041639333552639455827 564807062459000328959183741)
      ·
        refine ⟨211802648422125123359693903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564807062459000328959183741 211802648422125123359693903)
        ·
          refine ⟨317703972633187685039540855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211802648422125123359693903 317703972633187685039540855)
          ·
            refine ⟨476555958949781527559311283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317703972633187685039540855 476555958949781527559311283)
            ·
              refine ⟨714833938424672291338966925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 476555958949781527559311283 714833938424672291338966925)
              ·
                refine ⟨268062726909252109252112597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 714833938424672291338966925 268062726909252109252112597)
                ·
                  refine ⟨6282720161935596310596389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 268062726909252109252112597 6282720161935596310596389)
                  ·
                    refine ⟨1178010030362924308236823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6282720161935596310596389 1178010030362924308236823)
                    ·
                      rfl

theorem cell23_6882499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 4].length) (baseStart_6882499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882499 prefixEnd_6882499 := by exact prefixLift 6882499
  have htrace : WordTrace (prefixWord ++ tailWord_6882499) baseStart_6882499 baseEnd_6882499 := by
    simpa [prefixWord, tailWord_6882499, baseEnd_6882499] using wordTrace_append hprefix tailTrace_6882499
  have hstable : (prefixWord ++ tailWord_6882499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882499).length < 2 ^ (prefixWord ++ tailWord_6882499).sum := by decide
  have hdescent : baseEnd_6882499 < baseStart_6882499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882506 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_6882506 : Nat := 118140960795 + 6882506 * 2 ^ 59
def prefixEnd_6882506 : Nat := 4983230072969 + 3 ^ 40 * 6882506 * 2
def baseEnd_6882506 : Nat := 3534033685453354397322937

theorem tailTrace_6882506 : CollatzResearch.WordTrace tailWord_6882506 prefixEnd_6882506 3534033685453354397322937 := by
  unfold tailWord_6882506
  simp only [CollatzResearch.WordTrace]
  refine ⟨62756404100965918822118843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167350410935909116858983581 62756404100965918822118843)
  ·
    refine ⟨94134606151448878233178265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62756404100965918822118843 94134606151448878233178265)
    ·
      refine ⟨70600954613586658674883699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94134606151448878233178265 70600954613586658674883699)
      ·
        refine ⟨105901431920379988012325549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70600954613586658674883699 105901431920379988012325549)
        ·
          refine ⟨39713036970142495504622081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105901431920379988012325549 39713036970142495504622081)
          ·
            refine ⟨29784777727606871628466561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39713036970142495504622081 29784777727606871628466561)
            ·
              refine ⟨22338583295705153721349921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29784777727606871628466561 22338583295705153721349921)
              ·
                refine ⟨16753937471778865291012441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22338583295705153721349921 16753937471778865291012441)
                ·
                  refine ⟨12565453103834148968259331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16753937471778865291012441 12565453103834148968259331)
                  ·
                    refine ⟨18848179655751223452388997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12565453103834148968259331 18848179655751223452388997)
                    ·
                      refine ⟨3534033685453354397322937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18848179655751223452388997 3534033685453354397322937)
                      ·
                        rfl

theorem cell23_6882506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_6882506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882506 prefixEnd_6882506 := by exact prefixLift 6882506
  have htrace : WordTrace (prefixWord ++ tailWord_6882506) baseStart_6882506 baseEnd_6882506 := by
    simpa [prefixWord, tailWord_6882506, baseEnd_6882506] using wordTrace_append hprefix tailTrace_6882506
  have hstable : (prefixWord ++ tailWord_6882506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882506).length < 2 ^ (prefixWord ++ tailWord_6882506).sum := by decide
  have hdescent : baseEnd_6882506 < baseStart_6882506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882533 : List Nat := [1, 3, 1, 4, 3, 1, 1, 2, 3, 4]
def baseStart_6882533 : Nat := 118140960795 + 6882533 * 2 ^ 59
def prefixEnd_6882533 : Nat := 4983230072969 + 3 ^ 40 * 6882533 * 2
def baseEnd_6882533 : Nat := 1178015849810341930561771

theorem tailTrace_6882533 : CollatzResearch.WordTrace tailWord_6882533 prefixEnd_6882533 1178015849810341930561771 := by
  unfold tailWord_6882533
  simp only [CollatzResearch.WordTrace]
  refine ⟨251026601174765858899708253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167351067449843905933138835 251026601174765858899708253)
  ·
    refine ⟨94134975440537197087390595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251026601174765858899708253 94134975440537197087390595)
    ·
      refine ⟨141202463160805795631085893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94134975440537197087390595 141202463160805795631085893)
      ·
        refine ⟨26475461842651086680828605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141202463160805795631085893 26475461842651086680828605)
        ·
          refine ⟨9928298190994157505310727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26475461842651086680828605 9928298190994157505310727)
          ·
            refine ⟨14892447286491236257966091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9928298190994157505310727 14892447286491236257966091)
            ·
              refine ⟨22338670929736854386949137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14892447286491236257966091 22338670929736854386949137)
              ·
                refine ⟨16754003197302640790211853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22338670929736854386949137 16754003197302640790211853)
                ·
                  refine ⟨6282751198988490296329445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16754003197302640790211853 6282751198988490296329445)
                  ·
                    refine ⟨1178015849810341930561771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6282751198988490296329445 1178015849810341930561771)
                    ·
                      rfl

theorem cell23_6882533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 2, 3, 4].length) (baseStart_6882533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882533 prefixEnd_6882533 := by exact prefixLift 6882533
  have htrace : WordTrace (prefixWord ++ tailWord_6882533) baseStart_6882533 baseEnd_6882533 := by
    simpa [prefixWord, tailWord_6882533, baseEnd_6882533] using wordTrace_append hprefix tailTrace_6882533
  have hstable : (prefixWord ++ tailWord_6882533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882533).length < 2 ^ (prefixWord ++ tailWord_6882533).sum := by decide
  have hdescent : baseEnd_6882533 < baseStart_6882533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882613 : List Nat := [1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 4]
def baseStart_6882613 : Nat := 118140960795 + 6882613 * 2 ^ 59
def prefixEnd_6882613 : Nat := 4983230072969 + 3 ^ 40 * 6882613 * 2
def baseEnd_6882613 : Nat := 3534088627883385478684945

theorem tailTrace_6882613 : CollatzResearch.WordTrace tailWord_6882613 prefixEnd_6882613 3534088627883385478684945 := by
  unfold tailWord_6882613
  simp only [CollatzResearch.WordTrace]
  refine ⟨251029519014476032562620493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167353012676317355041746995 251029519014476032562620493)
  ·
    refine ⟨94136069630428512210982685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251029519014476032562620493 94136069630428512210982685)
    ·
      refine ⟨35301026111410692079118507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94136069630428512210982685 35301026111410692079118507)
      ·
        refine ⟨52951539167116038118677761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35301026111410692079118507 52951539167116038118677761)
        ·
          refine ⟨39713654375337028589008321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52951539167116038118677761 39713654375337028589008321)
          ·
            refine ⟨29785240781502771441756241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39713654375337028589008321 29785240781502771441756241)
            ·
              refine ⟨22338930586127078581317181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29785240781502771441756241 22338930586127078581317181)
              ·
                refine ⟨8377098969797654467993943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22338930586127078581317181 8377098969797654467993943)
                ·
                  refine ⟨12565648454696481701990915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8377098969797654467993943 12565648454696481701990915)
                  ·
                    refine ⟨18848472682044722552986373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12565648454696481701990915 18848472682044722552986373)
                    ·
                      refine ⟨3534088627883385478684945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18848472682044722552986373 3534088627883385478684945)
                      ·
                        rfl

theorem cell23_6882613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_6882613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882613 prefixEnd_6882613 := by exact prefixLift 6882613
  have htrace : WordTrace (prefixWord ++ tailWord_6882613) baseStart_6882613 baseEnd_6882613 := by
    simpa [prefixWord, tailWord_6882613, baseEnd_6882613] using wordTrace_append hprefix tailTrace_6882613
  have hstable : (prefixWord ++ tailWord_6882613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882613).length < 2 ^ (prefixWord ++ tailWord_6882613).sum := by decide
  have hdescent : baseEnd_6882613 < baseStart_6882613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882616 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 5, 2, 3]
def baseStart_6882616 : Nat := 118140960795 + 6882616 * 2 ^ 59
def prefixEnd_6882616 : Nat := 4983230072969 + 3 ^ 40 * 6882616 * 2
def baseEnd_6882616 : Nat := 3534090168325348966947431

theorem tailTrace_6882616 : CollatzResearch.WordTrace tailWord_6882616 prefixEnd_6882616 3534090168325348966947431 := by
  unfold tailWord_6882616
  simp only [CollatzResearch.WordTrace]
  refine ⟨125514814216732582037489851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167353085622310109383319801 125514814216732582037489851)
  ·
    refine ⟨188272221325098873056234777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125514814216732582037489851 188272221325098873056234777)
    ·
      refine ⟨141204165993824154792176083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188272221325098873056234777 141204165993824154792176083)
      ·
        refine ⟨211806248990736232188264125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141204165993824154792176083 211806248990736232188264125)
        ·
          refine ⟨79427343371526087070599047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211806248990736232188264125 79427343371526087070599047)
          ·
            refine ⟨119141015057289130605898571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79427343371526087070599047 119141015057289130605898571)
            ·
              refine ⟨178711522585933695908847857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 119141015057289130605898571 178711522585933695908847857)
              ·
                refine ⟨134033641939450271931635893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178711522585933695908847857 134033641939450271931635893)
                ·
                  refine ⟨12565653931823462993590865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 134033641939450271931635893 12565653931823462993590865)
                  ·
                    refine ⟨9424240448867597245193149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12565653931823462993590865 9424240448867597245193149)
                    ·
                      refine ⟨3534090168325348966947431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9424240448867597245193149 3534090168325348966947431)
                      ·
                        rfl

theorem cell23_6882616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_6882616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882616 prefixEnd_6882616 := by exact prefixLift 6882616
  have htrace : WordTrace (prefixWord ++ tailWord_6882616) baseStart_6882616 baseEnd_6882616 := by
    simpa [prefixWord, tailWord_6882616, baseEnd_6882616] using wordTrace_append hprefix tailTrace_6882616
  have hstable : (prefixWord ++ tailWord_6882616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882616).length < 2 ^ (prefixWord ++ tailWord_6882616).sum := by decide
  have hdescent : baseEnd_6882616 < baseStart_6882616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882636 : List Nat := [2, 2, 1, 3, 2, 3, 2, 8]
def baseStart_6882636 : Nat := 118140960795 + 6882636 * 2 ^ 59
def prefixEnd_6882636 : Nat := 4983230072969 + 3 ^ 40 * 6882636 * 2
def baseEnd_6882636 : Nat := 130892608812534773655457

theorem tailTrace_6882636 : CollatzResearch.WordTrace tailWord_6882636 prefixEnd_6882636 130892608812534773655457 := by
  unfold tailWord_6882636
  simp only [CollatzResearch.WordTrace]
  refine ⟨125515178946696353745353881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167353571928928471660471841 125515178946696353745353881)
  ·
    refine ⟨94136384210022265309015411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125515178946696353745353881 94136384210022265309015411)
    ·
      refine ⟨141204576315033397963523117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94136384210022265309015411 141204576315033397963523117)
      ·
        refine ⟨52951716118137524236321169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141204576315033397963523117 52951716118137524236321169)
        ·
          refine ⟨39713787088603143177240877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52951716118137524236321169 39713787088603143177240877)
          ·
            refine ⟨14892670158226178691465329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39713787088603143177240877 14892670158226178691465329)
            ·
              refine ⟨11169502618669634018598997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14892670158226178691465329 11169502618669634018598997)
              ·
                refine ⟨130892608812534773655457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11169502618669634018598997 130892608812534773655457)
                ·
                  rfl

theorem cell23_6882636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 8].length) (baseStart_6882636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882636 prefixEnd_6882636 := by exact prefixLift 6882636
  have htrace : WordTrace (prefixWord ++ tailWord_6882636) baseStart_6882636 baseEnd_6882636 := by
    simpa [prefixWord, tailWord_6882636, baseEnd_6882636] using wordTrace_append hprefix tailTrace_6882636
  have hstable : (prefixWord ++ tailWord_6882636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882636).length < 2 ^ (prefixWord ++ tailWord_6882636).sum := by decide
  have hdescent : baseEnd_6882636 < baseStart_6882636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882696 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 8]
def baseStart_6882696 : Nat := 118140960795 + 6882696 * 2 ^ 59
def prefixEnd_6882696 : Nat := 4983230072969 + 3 ^ 40 * 6882696 * 2
def baseEnd_6882696 : Nat := 1178043748925902884649021

theorem tailTrace_6882696 : CollatzResearch.WordTrace tailWord_6882696 prefixEnd_6882696 1178043748925902884649021 := by
  unfold tailWord_6882696
  simp only [CollatzResearch.WordTrace]
  refine ⟨125516273136587668868945971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167355030848783558491927961 125516273136587668868945971)
  ·
    refine ⟨188274409704881503303418957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125516273136587668868945971 188274409704881503303418957)
    ·
      refine ⟨70602903639330563738782109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188274409704881503303418957 70602903639330563738782109)
      ·
        refine ⟨26476088864748961402043291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70602903639330563738782109 26476088864748961402043291)
        ·
          refine ⟨39714133297123442103064937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26476088864748961402043291 39714133297123442103064937)
          ·
            refine ⟨29785599972842581577298703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39714133297123442103064937 29785599972842581577298703)
            ·
              refine ⟨44678399959263872365948055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29785599972842581577298703 44678399959263872365948055)
              ·
                refine ⟨67017599938895808548922083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44678399959263872365948055 67017599938895808548922083)
                ·
                  refine ⟨100526399908343712823383125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67017599938895808548922083 100526399908343712823383125)
                  ·
                    refine ⟨1178043748925902884649021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 100526399908343712823383125 1178043748925902884649021)
                    ·
                      rfl

theorem cell23_6882696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_6882696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882696 prefixEnd_6882696 := by exact prefixLift 6882696
  have htrace : WordTrace (prefixWord ++ tailWord_6882696) baseStart_6882696 baseEnd_6882696 := by
    simpa [prefixWord, tailWord_6882696, baseEnd_6882696] using wordTrace_append hprefix tailTrace_6882696
  have hstable : (prefixWord ++ tailWord_6882696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882696).length < 2 ^ (prefixWord ++ tailWord_6882696).sum := by decide
  have hdescent : baseEnd_6882696 < baseStart_6882696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882720 : List Nat := [2, 1, 1, 4, 1, 2, 2, 2, 4, 2, 2]
def baseStart_6882720 : Nat := 118140960795 + 6882720 * 2 ^ 59
def prefixEnd_6882720 : Nat := 4983230072969 + 3 ^ 40 * 6882720 * 2
def baseEnd_6882720 : Nat := 3534143570313416560046953

theorem tailTrace_6882720 : CollatzResearch.WordTrace tailWord_6882720 prefixEnd_6882720 3534143570313416560046953 := by
  unfold tailWord_6882720
  simp only [CollatzResearch.WordTrace]
  refine ⟨125516710812544194918382807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167355614416725593224510409 125516710812544194918382807)
  ·
    refine ⟨188275066218816292377574211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125516710812544194918382807 188275066218816292377574211)
    ·
      refine ⟨282412599328224438566361317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188275066218816292377574211 282412599328224438566361317)
      ·
        refine ⟨52952362374042082231192747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282412599328224438566361317 52952362374042082231192747)
        ·
          refine ⟨79428543561063123346789121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52952362374042082231192747 79428543561063123346789121)
          ·
            refine ⟨59571407670797342510091841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79428543561063123346789121 59571407670797342510091841)
            ·
              refine ⟨44678555753098006882568881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59571407670797342510091841 44678555753098006882568881)
              ·
                refine ⟨33508916814823505161926661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44678555753098006882568881 33508916814823505161926661)
                ·
                  refine ⟨6282921902779407217861249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33508916814823505161926661 6282921902779407217861249)
                  ·
                    refine ⟨4712191427084555413395937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6282921902779407217861249 4712191427084555413395937)
                    ·
                      refine ⟨3534143570313416560046953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712191427084555413395937 3534143570313416560046953)
                      ·
                        rfl

theorem cell23_6882720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 2, 4, 2, 2].length) (baseStart_6882720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882720 prefixEnd_6882720 := by exact prefixLift 6882720
  have htrace : WordTrace (prefixWord ++ tailWord_6882720) baseStart_6882720 baseEnd_6882720 := by
    simpa [prefixWord, tailWord_6882720, baseEnd_6882720] using wordTrace_append hprefix tailTrace_6882720
  have hstable : (prefixWord ++ tailWord_6882720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882720).length < 2 ^ (prefixWord ++ tailWord_6882720).sum := by decide
  have hdescent : baseEnd_6882720 < baseStart_6882720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882743 : List Nat := [1, 1, 3, 1, 3, 2, 1, 6, 5]
def baseStart_6882743 : Nat := 118140960795 + 6882743 * 2 ^ 59
def prefixEnd_6882743 : Nat := 4983230072969 + 3 ^ 40 * 6882743 * 2
def baseEnd_6882743 : Nat := 392683931152052218895483

theorem tailTrace_6882743 : CollatzResearch.WordTrace tailWord_6882743 prefixEnd_6882743 392683931152052218895483 := by
  unfold tailWord_6882743
  simp only [CollatzResearch.WordTrace]
  refine ⟨251034260504005064764852883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167356173669336709843235255 251034260504005064764852883)
  ·
    refine ⟨376551390756007597147279325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251034260504005064764852883 376551390756007597147279325)
    ·
      refine ⟨141206771533502848930229747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376551390756007597147279325 141206771533502848930229747)
      ·
        refine ⟨211810157300254273395344621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141206771533502848930229747 211810157300254273395344621)
        ·
          refine ⟨79428808987595352523254233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211810157300254273395344621 79428808987595352523254233)
          ·
            refine ⟨59571606740696514392440675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79428808987595352523254233 59571606740696514392440675)
            ·
              refine ⟨89357410111044771588661013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59571606740696514392440675 89357410111044771588661013)
              ·
                refine ⟨4188628598955223668218485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89357410111044771588661013 4188628598955223668218485)
                ·
                  refine ⟨392683931152052218895483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4188628598955223668218485 392683931152052218895483)
                  ·
                    rfl

theorem cell23_6882743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 6, 5].length) (baseStart_6882743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882743 prefixEnd_6882743 := by exact prefixLift 6882743
  have htrace : WordTrace (prefixWord ++ tailWord_6882743) baseStart_6882743 baseEnd_6882743 := by
    simpa [prefixWord, tailWord_6882743, baseEnd_6882743] using wordTrace_append hprefix tailTrace_6882743
  have hstable : (prefixWord ++ tailWord_6882743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882743).length < 2 ^ (prefixWord ++ tailWord_6882743).sum := by decide
  have hdescent : baseEnd_6882743 < baseStart_6882743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882763 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 2, 5, 2]
def baseStart_6882763 : Nat := 118140960795 + 6882763 * 2 ^ 59
def prefixEnd_6882763 : Nat := 4983230072969 + 3 ^ 40 * 6882763 * 2
def baseEnd_6882763 : Nat := 3534165649981559891809255

theorem tailTrace_6882763 : CollatzResearch.WordTrace tailWord_6882763 prefixEnd_6882763 3534165649981559891809255 := by
  unfold tailWord_6882763
  simp only [CollatzResearch.WordTrace]
  refine ⟨251034989963932608180580943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167356659975955072120387295 251034989963932608180580943)
  ·
    refine ⟨376552484945898912270871415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251034989963932608180580943 376552484945898912270871415)
    ·
      refine ⟨564828727418848368406307123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376552484945898912270871415 564828727418848368406307123)
      ·
        refine ⟨847243091128272552609460685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564828727418848368406307123 847243091128272552609460685)
        ·
          refine ⟨317716159173102207228547757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 847243091128272552609460685 317716159173102207228547757)
          ·
            refine ⟨119143559689913327710705409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317716159173102207228547757 119143559689913327710705409)
            ·
              refine ⟨89357669767434995783029057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119143559689913327710705409 89357669767434995783029057)
              ·
                refine ⟨67018252325576246837271793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89357669767434995783029057 67018252325576246837271793)
                ·
                  refine ⟨50263689244182185127953845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67018252325576246837271793 50263689244182185127953845)
                  ·
                    refine ⟨4712220866642079855745673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50263689244182185127953845 4712220866642079855745673)
                    ·
                      refine ⟨3534165649981559891809255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712220866642079855745673 3534165649981559891809255)
                      ·
                        rfl

theorem cell23_6882763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 5, 2].length) (baseStart_6882763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882763 prefixEnd_6882763 := by exact prefixLift 6882763
  have htrace : WordTrace (prefixWord ++ tailWord_6882763) baseStart_6882763 baseEnd_6882763 := by
    simpa [prefixWord, tailWord_6882763, baseEnd_6882763] using wordTrace_append hprefix tailTrace_6882763
  have hstable : (prefixWord ++ tailWord_6882763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882763).length < 2 ^ (prefixWord ++ tailWord_6882763).sum := by decide
  have hdescent : baseEnd_6882763 < baseStart_6882763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882773 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 2, 5]
def baseStart_6882773 : Nat := 118140960795 + 6882773 * 2 ^ 59
def prefixEnd_6882773 : Nat := 4983230072969 + 3 ^ 40 * 6882773 * 2
def baseEnd_6882773 : Nat := 1178056928262701617561403

theorem tailTrace_6882773 : CollatzResearch.WordTrace tailWord_6882773 prefixEnd_6882773 1178056928262701617561403 := by
  unfold tailWord_6882773
  simp only [CollatzResearch.WordTrace]
  refine ⟨251035354693896379888444973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167356903129264253258963315 251035354693896379888444973)
  ·
    refine ⟨94138258010211142458166865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251035354693896379888444973 94138258010211142458166865)
    ·
      refine ⟨70603693507658356843625149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94138258010211142458166865 70603693507658356843625149)
      ·
        refine ⟨26476385065371883816359431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70603693507658356843625149 26476385065371883816359431)
        ·
          refine ⟨39714577598057825724539147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26476385065371883816359431 39714577598057825724539147)
          ·
            refine ⟨59571866397086738586808721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39714577598057825724539147 59571866397086738586808721)
            ·
              refine ⟨44678899797815053940106541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59571866397086738586808721 44678899797815053940106541)
              ·
                refine ⟨16754587424180645227539953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44678899797815053940106541 16754587424180645227539953)
                ·
                  refine ⟨12565940568135483920654965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16754587424180645227539953 12565940568135483920654965)
                  ·
                    refine ⟨1178056928262701617561403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12565940568135483920654965 1178056928262701617561403)
                    ·
                      rfl

theorem cell23_6882773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 5].length) (baseStart_6882773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882773 prefixEnd_6882773 := by exact prefixLift 6882773
  have htrace : WordTrace (prefixWord ++ tailWord_6882773) baseStart_6882773 baseEnd_6882773 := by
    simpa [prefixWord, tailWord_6882773, baseEnd_6882773] using wordTrace_append hprefix tailTrace_6882773
  have hstable : (prefixWord ++ tailWord_6882773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882773).length < 2 ^ (prefixWord ++ tailWord_6882773).sum := by decide
  have hdescent : baseEnd_6882773 < baseStart_6882773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882796 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_6882796 : Nat := 118140960795 + 6882796 * 2 ^ 59
def prefixEnd_6882796 : Nat := 4983230072969 + 3 ^ 40 * 6882796 * 2
def baseEnd_6882796 : Nat := 3534182594843158262696603

theorem tailTrace_6882796 : CollatzResearch.WordTrace tailWord_6882796 prefixEnd_6882796 3534182594843158262696603 := by
  unfold tailWord_6882796
  simp only [CollatzResearch.WordTrace]
  refine ⟨125518096786406527408266121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167357462381875369877688161 125518096786406527408266121)
  ·
    refine ⟨94138572589804895556199591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125518096786406527408266121 94138572589804895556199591)
    ·
      refine ⟨141207858884707343334299387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94138572589804895556199591 141207858884707343334299387)
      ·
        refine ⟨211811788327061015001449081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141207858884707343334299387 211811788327061015001449081)
        ·
          refine ⟨158858841245295761251086811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211811788327061015001449081 158858841245295761251086811)
          ·
            refine ⟨238288261867943641876630217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158858841245295761251086811 238288261867943641876630217)
            ·
              refine ⟨178716196400957731407472663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238288261867943641876630217 178716196400957731407472663)
              ·
                refine ⟨268074294601436597111208995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 178716196400957731407472663 268074294601436597111208995)
                ·
                  refine ⟨402111441902154895666813493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268074294601436597111208995 402111441902154895666813493)
                  ·
                    refine ⟨37697947678327021468763765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 402111441902154895666813493 37697947678327021468763765)
                    ·
                      refine ⟨3534182594843158262696603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37697947678327021468763765 3534182594843158262696603)
                      ·
                        rfl

theorem cell23_6882796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_6882796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882796 prefixEnd_6882796 := by exact prefixLift 6882796
  have htrace : WordTrace (prefixWord ++ tailWord_6882796) baseStart_6882796 baseEnd_6882796 := by
    simpa [prefixWord, tailWord_6882796, baseEnd_6882796] using wordTrace_append hprefix tailTrace_6882796
  have hstable : (prefixWord ++ tailWord_6882796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882796).length < 2 ^ (prefixWord ++ tailWord_6882796).sum := by decide
  have hdescent : baseEnd_6882796 < baseStart_6882796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882803 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 3, 4]
def baseStart_6882803 : Nat := 118140960795 + 6882803 * 2 ^ 59
def prefixEnd_6882803 : Nat := 4983230072969 + 3 ^ 40 * 6882803 * 2
def baseEnd_6882803 : Nat := 1178062063069246578436357

theorem tailTrace_6882803 : CollatzResearch.WordTrace tailWord_6882803 prefixEnd_6882803 1178062063069246578436357 := by
  unfold tailWord_6882803
  simp only [CollatzResearch.WordTrace]
  refine ⟨251036448883787695012037063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167357632589191796674691375 251036448883787695012037063)
  ·
    refine ⟨376554673325681542518055595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251036448883787695012037063 376554673325681542518055595)
    ·
      refine ⟨564832009988522313777083393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376554673325681542518055595 564832009988522313777083393)
      ·
        refine ⟨423624007491391735332812545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564832009988522313777083393 423624007491391735332812545)
        ·
          refine ⟨317718005618543801499609409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423624007491391735332812545 317718005618543801499609409)
          ·
            refine ⟨238288504213907851124707057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317718005618543801499609409 238288504213907851124707057)
            ·
              refine ⟨178716378160430888343530293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238288504213907851124707057 178716378160430888343530293)
              ·
                refine ⟨16754660452540395782205965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 178716378160430888343530293 16754660452540395782205965)
                ·
                  refine ⟨6282997669702648418327237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16754660452540395782205965 6282997669702648418327237)
                  ·
                    refine ⟨1178062063069246578436357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6282997669702648418327237 1178062063069246578436357)
                    ·
                      rfl

theorem cell23_6882803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 4].length) (baseStart_6882803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882803 prefixEnd_6882803 := by exact prefixLift 6882803
  have htrace : WordTrace (prefixWord ++ tailWord_6882803) baseStart_6882803 baseEnd_6882803 := by
    simpa [prefixWord, tailWord_6882803, baseEnd_6882803] using wordTrace_append hprefix tailTrace_6882803
  have hstable : (prefixWord ++ tailWord_6882803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882803).length < 2 ^ (prefixWord ++ tailWord_6882803).sum := by decide
  have hdescent : baseEnd_6882803 < baseStart_6882803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882887 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 1, 5, 2]
def baseStart_6882887 : Nat := 118140960795 + 6882887 * 2 ^ 59
def prefixEnd_6882887 : Nat := 4983230072969 + 3 ^ 40 * 6882887 * 2
def baseEnd_6882887 : Nat := 3534229321582717406658685

theorem tailTrace_6882887 : CollatzResearch.WordTrace tailWord_6882887 prefixEnd_6882887 3534229321582717406658685 := by
  unfold tailWord_6882887
  simp only [CollatzResearch.WordTrace]
  refine ⟨251039512615483377358094915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167359675076988918238729943 251039512615483377358094915)
  ·
    refine ⟨376559268923225066037142373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251039512615483377358094915 376559268923225066037142373)
    ·
      refine ⟨70604862923104699881964195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376559268923225066037142373 70604862923104699881964195)
      ·
        refine ⟨105907294384657049822946293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70604862923104699881964195 105907294384657049822946293)
        ·
          refine ⟨9928808848561598420901215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105907294384657049822946293 9928808848561598420901215)
          ·
            refine ⟨14893213272842397631351823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9928808848561598420901215 14893213272842397631351823)
            ·
              refine ⟨22339819909263596447027735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14893213272842397631351823 22339819909263596447027735)
              ·
                refine ⟨33509729863895394670541603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22339819909263596447027735 33509729863895394670541603)
                ·
                  refine ⟨50264594795843092005812405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33509729863895394670541603 50264594795843092005812405)
                  ·
                    refine ⟨4712305762110289875544913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50264594795843092005812405 4712305762110289875544913)
                    ·
                      refine ⟨3534229321582717406658685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712305762110289875544913 3534229321582717406658685)
                      ·
                        rfl

theorem cell23_6882887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 5, 2].length) (baseStart_6882887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882887 prefixEnd_6882887 := by exact prefixLift 6882887
  have htrace : WordTrace (prefixWord ++ tailWord_6882887) baseStart_6882887 baseEnd_6882887 := by
    simpa [prefixWord, tailWord_6882887, baseEnd_6882887] using wordTrace_append hprefix tailTrace_6882887
  have hstable : (prefixWord ++ tailWord_6882887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882887).length < 2 ^ (prefixWord ++ tailWord_6882887).sum := by decide
  have hdescent : baseEnd_6882887 < baseStart_6882887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882913 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 6]
def baseStart_6882913 : Nat := 118140960795 + 6882913 * 2 ^ 59
def prefixEnd_6882913 : Nat := 4983230072969 + 3 ^ 40 * 6882913 * 2
def baseEnd_6882913 : Nat := 3534242672079734304933565

theorem tailTrace_6882913 : CollatzResearch.WordTrace tailWord_6882913 prefixEnd_6882913 3534242672079734304933565 := by
  unfold tailWord_6882913
  simp only [CollatzResearch.WordTrace]
  refine ⟨251040460913389183798541393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167360307275592789199027595 251040460913389183798541393)
  ·
    refine ⟨188280345685041887848906045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251040460913389183798541393 188280345685041887848906045)
    ·
      refine ⟨70605129631890707943339767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188280345685041887848906045 70605129631890707943339767)
      ·
        refine ⟨105907694447836061915009651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70605129631890707943339767 105907694447836061915009651)
        ·
          refine ⟨158861541671754092872514477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105907694447836061915009651 158861541671754092872514477)
          ·
            refine ⟨59573078126907784827192929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158861541671754092872514477 59573078126907784827192929)
            ·
              refine ⟨44679808595180838620394697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59573078126907784827192929 44679808595180838620394697)
              ·
                refine ⟨33509856446385628965296023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44679808595180838620394697 33509856446385628965296023)
                ·
                  refine ⟨50264784669578443447944035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33509856446385628965296023 50264784669578443447944035)
                  ·
                    refine ⟨75397177004367665171916053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50264784669578443447944035 75397177004367665171916053)
                    ·
                      refine ⟨3534242672079734304933565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75397177004367665171916053 3534242672079734304933565)
                      ·
                        rfl

theorem cell23_6882913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 1, 6].length) (baseStart_6882913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882913 prefixEnd_6882913 := by exact prefixLift 6882913
  have htrace : WordTrace (prefixWord ++ tailWord_6882913) baseStart_6882913 baseEnd_6882913 := by
    simpa [prefixWord, tailWord_6882913, baseEnd_6882913] using wordTrace_append hprefix tailTrace_6882913
  have hstable : (prefixWord ++ tailWord_6882913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882913).length < 2 ^ (prefixWord ++ tailWord_6882913).sum := by decide
  have hdescent : baseEnd_6882913 < baseStart_6882913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882920 : List Nat := [2, 1, 4, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6882920 : Nat := 118140960795 + 6882920 * 2 ^ 59
def prefixEnd_6882920 : Nat := 4983230072969 + 3 ^ 40 * 6882920 * 2
def baseEnd_6882920 : Nat := 3534246266444315777546033

theorem tailTrace_6882920 : CollatzResearch.WordTrace tailWord_6882920 prefixEnd_6882920 3534246266444315777546033 := by
  unfold tailWord_6882920
  simp only [CollatzResearch.WordTrace]
  refine ⟨125520358112181911997023107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167360477482909215996030809 125520358112181911997023107)
  ·
    refine ⟨188280537168272867995534661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125520358112181911997023107 188280537168272867995534661)
    ·
      refine ⟨35302600719051162749162749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188280537168272867995534661 35302600719051162749162749)
      ·
        refine ⟨13238475269644186030936031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35302600719051162749162749 13238475269644186030936031)
        ·
          refine ⟨19857712904466279046404047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13238475269644186030936031 19857712904466279046404047)
          ·
            refine ⟨29786569356699418569606071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19857712904466279046404047 29786569356699418569606071)
            ·
              refine ⟨44679854035049127854409107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29786569356699418569606071 44679854035049127854409107)
              ·
                refine ⟨67019781052573691781613661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44679854035049127854409107 67019781052573691781613661)
                ·
                  refine ⟨25132417894715134418105123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67019781052573691781613661 25132417894715134418105123)
                  ·
                    refine ⟨37698626842072701627157685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25132417894715134418105123 37698626842072701627157685)
                    ·
                      refine ⟨3534246266444315777546033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37698626842072701627157685 3534246266444315777546033)
                      ·
                        rfl

theorem cell23_6882920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6882920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882920 prefixEnd_6882920 := by exact prefixLift 6882920
  have htrace : WordTrace (prefixWord ++ tailWord_6882920) baseStart_6882920 baseEnd_6882920 := by
    simpa [prefixWord, tailWord_6882920, baseEnd_6882920] using wordTrace_append hprefix tailTrace_6882920
  have hstable : (prefixWord ++ tailWord_6882920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882920).length < 2 ^ (prefixWord ++ tailWord_6882920).sum := by decide
  have hdescent : baseEnd_6882920 < baseStart_6882920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882930 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_6882930 : Nat := 118140960795 + 6882930 * 2 ^ 59
def prefixEnd_6882930 : Nat := 4983230072969 + 3 ^ 40 * 6882930 * 2
def baseEnd_6882930 : Nat := 3534251401250860738420987

theorem tailTrace_6882930 : CollatzResearch.WordTrace tailWord_6882930 prefixEnd_6882930 3534251401250860738420987 := by
  unfold tailWord_6882930
  simp only [CollatzResearch.WordTrace]
  refine ⟨62760270238581898925477561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167360720636218397134606829 62760270238581898925477561)
  ·
    refine ⟨47070202678936424194108171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62760270238581898925477561 47070202678936424194108171)
    ·
      refine ⟨70605304018404636291162257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47070202678936424194108171 70605304018404636291162257)
      ·
        refine ⟨52953978013803477218371693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70605304018404636291162257 52953978013803477218371693)
        ·
          refine ⟨19857741755176303956889385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52953978013803477218371693 19857741755176303956889385)
          ·
            refine ⟨14893306316382227967667039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19857741755176303956889385 14893306316382227967667039)
            ·
              refine ⟨22339959474573341951500559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14893306316382227967667039 22339959474573341951500559)
              ·
                refine ⟨33509939211860012927250839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22339959474573341951500559 33509939211860012927250839)
                ·
                  refine ⟨50264908817790019390876259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33509939211860012927250839 50264908817790019390876259)
                  ·
                    refine ⟨75397363226685029086314389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50264908817790019390876259 75397363226685029086314389)
                    ·
                      refine ⟨3534251401250860738420987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 75397363226685029086314389 3534251401250860738420987)
                      ·
                        rfl

theorem cell23_6882930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_6882930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882930 prefixEnd_6882930 := by exact prefixLift 6882930
  have htrace : WordTrace (prefixWord ++ tailWord_6882930) baseStart_6882930 baseEnd_6882930 := by
    simpa [prefixWord, tailWord_6882930, baseEnd_6882930] using wordTrace_append hprefix tailTrace_6882930
  have hstable : (prefixWord ++ tailWord_6882930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882930).length < 2 ^ (prefixWord ++ tailWord_6882930).sum := by decide
  have hdescent : baseEnd_6882930 < baseStart_6882930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882934 : List Nat := [5, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_6882934 : Nat := 118140960795 + 6882934 * 2 ^ 59
def prefixEnd_6882934 : Nat := 4983230072969 + 3 ^ 40 * 6882934 * 2
def baseEnd_6882934 : Nat := 3534253455173478722770969

theorem tailTrace_6882934 : CollatzResearch.WordTrace tailWord_6882934 prefixEnd_6882934 3534253455173478722770969 := by
  unfold tailWord_6882934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15690076677894569024065991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 167360817897542069590037237 15690076677894569024065991)
  ·
    refine ⟨23535115016841853536098987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15690076677894569024065991 23535115016841853536098987)
    ·
      refine ⟨35302672525262780304148481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23535115016841853536098987 35302672525262780304148481)
      ·
        refine ⟨26477004393947085228111361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35302672525262780304148481 26477004393947085228111361)
        ·
          refine ⟨19857753295460313921083521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26477004393947085228111361 19857753295460313921083521)
          ·
            refine ⟨14893314971595235440812641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19857753295460313921083521 14893314971595235440812641)
            ·
              refine ⟨11169986228696426580609481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14893314971595235440812641 11169986228696426580609481)
              ·
                refine ⟨8377489671522319935457111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11169986228696426580609481 8377489671522319935457111)
                ·
                  refine ⟨12566234507283479903185667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8377489671522319935457111 12566234507283479903185667)
                  ·
                    refine ⟨18849351760925219854778501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12566234507283479903185667 18849351760925219854778501)
                    ·
                      refine ⟨3534253455173478722770969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18849351760925219854778501 3534253455173478722770969)
                      ·
                        rfl

theorem cell23_6882934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_6882934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882934 prefixEnd_6882934 := by exact prefixLift 6882934
  have htrace : WordTrace (prefixWord ++ tailWord_6882934) baseStart_6882934 baseEnd_6882934 := by
    simpa [prefixWord, tailWord_6882934, baseEnd_6882934] using wordTrace_append hprefix tailTrace_6882934
  have hstable : (prefixWord ++ tailWord_6882934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882934).length < 2 ^ (prefixWord ++ tailWord_6882934).sum := by decide
  have hdescent : baseEnd_6882934 < baseStart_6882934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882937 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 3]
def baseStart_6882937 : Nat := 118140960795 + 6882937 * 2 ^ 59
def prefixEnd_6882937 : Nat := 4983230072969 + 3 ^ 40 * 6882937 * 2
def baseEnd_6882937 : Nat := 3534254995615442211033455

theorem tailTrace_6882937 : CollatzResearch.WordTrace tailWord_6882937 prefixEnd_6882937 3534254995615442211033455 := by
  unfold tailWord_6882937
  simp only [CollatzResearch.WordTrace]
  refine ⟨251041336265302235897415065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167360890843534823931610043 251041336265302235897415065)
  ·
    refine ⟨188281002198976676923061299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251041336265302235897415065 188281002198976676923061299)
    ·
      refine ⟨282421503298465015384591949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188281002198976676923061299 282421503298465015384591949)
      ·
        refine ⟨105908063736924380769221981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282421503298465015384591949 105908063736924380769221981)
        ·
          refine ⟨39715523901346642788458243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105908063736924380769221981 39715523901346642788458243)
          ·
            refine ⟨59573285852019964182687365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39715523901346642788458243 59573285852019964182687365)
            ·
              refine ⟨11169991097253743284253881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59573285852019964182687365 11169991097253743284253881)
              ·
                refine ⟨8377493322940307463190411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11169991097253743284253881 8377493322940307463190411)
                ·
                  refine ⟨12566239984410461194785617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8377493322940307463190411 12566239984410461194785617)
                  ·
                    refine ⟨9424679988307845896089213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12566239984410461194785617 9424679988307845896089213)
                    ·
                      refine ⟨3534254995615442211033455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9424679988307845896089213 3534254995615442211033455)
                      ·
                        rfl

theorem cell23_6882937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_6882937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882937 prefixEnd_6882937 := by exact prefixLift 6882937
  have htrace : WordTrace (prefixWord ++ tailWord_6882937) baseStart_6882937 baseEnd_6882937 := by
    simpa [prefixWord, tailWord_6882937, baseEnd_6882937] using wordTrace_append hprefix tailTrace_6882937
  have hstable : (prefixWord ++ tailWord_6882937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882937).length < 2 ^ (prefixWord ++ tailWord_6882937).sum := by decide
  have hdescent : baseEnd_6882937 < baseStart_6882937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882951 : List Nat := [1, 1, 4, 2, 1, 3, 3, 3, 1, 2, 2]
def baseStart_6882951 : Nat := 118140960795 + 6882951 * 2 ^ 59
def prefixEnd_6882951 : Nat := 4983230072969 + 3 ^ 40 * 6882951 * 2
def baseEnd_6882951 : Nat := 3534262184344605156258391

theorem tailTrace_6882951 : CollatzResearch.WordTrace tailWord_6882951 prefixEnd_6882951 3534262184344605156258391 := by
  unfold tailWord_6882951
  simp only [CollatzResearch.WordTrace]
  refine ⟨251041846887251516288424707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167361231258167677525616471 251041846887251516288424707)
  ·
    refine ⟨376562770330877274432637061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251041846887251516288424707 376562770330877274432637061)
    ·
      refine ⟨70605519437039488956119449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376562770330877274432637061 70605519437039488956119449)
      ·
        refine ⟨52954139577779616717089587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70605519437039488956119449 52954139577779616717089587)
        ·
          refine ⟨79431209366669425075634381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52954139577779616717089587 79431209366669425075634381)
          ·
            refine ⟨29786703512501034403362893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79431209366669425075634381 29786703512501034403362893)
            ·
              refine ⟨11170013817187887901261085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29786703512501034403362893 11170013817187887901261085)
              ·
                refine ⟨4188755181445457962972907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11170013817187887901261085 4188755181445457962972907)
                ·
                  refine ⟨6283132772168186944459361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188755181445457962972907 6283132772168186944459361)
                  ·
                    refine ⟨4712349579126140208344521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6283132772168186944459361 4712349579126140208344521)
                    ·
                      refine ⟨3534262184344605156258391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712349579126140208344521 3534262184344605156258391)
                      ·
                        rfl

theorem cell23_6882951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 3, 1, 2, 2].length) (baseStart_6882951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882951 prefixEnd_6882951 := by exact prefixLift 6882951
  have htrace : WordTrace (prefixWord ++ tailWord_6882951) baseStart_6882951 baseEnd_6882951 := by
    simpa [prefixWord, tailWord_6882951, baseEnd_6882951] using wordTrace_append hprefix tailTrace_6882951
  have hstable : (prefixWord ++ tailWord_6882951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882951).length < 2 ^ (prefixWord ++ tailWord_6882951).sum := by decide
  have hdescent : baseEnd_6882951 < baseStart_6882951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882967 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 3]
def baseStart_6882967 : Nat := 118140960795 + 6882967 * 2 ^ 59
def prefixEnd_6882967 : Nat := 4983230072969 + 3 ^ 40 * 6882967 * 2
def baseEnd_6882967 : Nat := 3534270400035077093658317

theorem tailTrace_6882967 : CollatzResearch.WordTrace tailWord_6882967 prefixEnd_6882967 3534270400035077093658317 := by
  unfold tailWord_6882967
  simp only [CollatzResearch.WordTrace]
  refine ⟨251042430455193551021007155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167361620303462367347338103 251042430455193551021007155)
  ·
    refine ⟨376563645682790326531510733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251042430455193551021007155 376563645682790326531510733)
    ·
      refine ⟨141211367131046372449316525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 376563645682790326531510733 141211367131046372449316525)
      ·
        refine ⟨52954262674142389668493697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141211367131046372449316525 52954262674142389668493697)
        ·
          refine ⟨39715697005606792251370273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52954262674142389668493697 39715697005606792251370273)
          ·
            refine ⟨29786772754205094188527705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39715697005606792251370273 29786772754205094188527705)
            ·
              refine ⟨22340079565653820641395779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29786772754205094188527705 22340079565653820641395779)
              ·
                refine ⟨33510119348480730962093669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22340079565653820641395779 33510119348480730962093669)
                ·
                  refine ⟨6283147377840137055392563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33510119348480730962093669 6283147377840137055392563)
                  ·
                    refine ⟨9424721066760205583088845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6283147377840137055392563 9424721066760205583088845)
                    ·
                      refine ⟨3534270400035077093658317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9424721066760205583088845 3534270400035077093658317)
                      ·
                        rfl

theorem cell23_6882967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_6882967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882967 prefixEnd_6882967 := by exact prefixLift 6882967
  have htrace : WordTrace (prefixWord ++ tailWord_6882967) baseStart_6882967 baseEnd_6882967 := by
    simpa [prefixWord, tailWord_6882967, baseEnd_6882967] using wordTrace_append hprefix tailTrace_6882967
  have hstable : (prefixWord ++ tailWord_6882967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882967).length < 2 ^ (prefixWord ++ tailWord_6882967).sum := by decide
  have hdescent : baseEnd_6882967 < baseStart_6882967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882968 : List Nat := [2, 1, 2, 4, 1, 3, 3, 2, 1, 2, 2]
def baseStart_6882968 : Nat := 118140960795 + 6882968 * 2 ^ 59
def prefixEnd_6882968 : Nat := 4983230072969 + 3 ^ 40 * 6882968 * 2
def baseEnd_6882968 : Nat := 3534270913515731589745813

theorem tailTrace_6882968 : CollatzResearch.WordTrace tailWord_6882968 prefixEnd_6882968 3534270913515731589745813 := by
  unfold tailWord_6882968
  simp only [CollatzResearch.WordTrace]
  refine ⟨125521233464094964095896779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167361644618793285461195705 125521233464094964095896779)
  ·
    refine ⟨188281850196142446143845169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125521233464094964095896779 188281850196142446143845169)
    ·
      refine ⟨141211387647106834607883877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188281850196142446143845169 141211387647106834607883877)
      ·
        refine ⟨26477135183832531488978227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141211387647106834607883877 26477135183832531488978227)
        ·
          refine ⟨39715702775748797233467341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26477135183832531488978227 39715702775748797233467341)
          ·
            refine ⟨14893388540905798962550253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39715702775748797233467341 14893388540905798962550253)
            ·
              refine ⟨5585020702839674610956345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14893388540905798962550253 5585020702839674610956345)
              ·
                refine ⟨4188765527129755958217259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5585020702839674610956345 4188765527129755958217259)
                ·
                  refine ⟨6283148290694633937325889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188765527129755958217259 6283148290694633937325889)
                  ·
                    refine ⟨4712361218020975452994417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6283148290694633937325889 4712361218020975452994417)
                    ·
                      refine ⟨3534270913515731589745813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712361218020975452994417 3534270913515731589745813)
                      ·
                        rfl

theorem cell23_6882968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_6882968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882968 prefixEnd_6882968 := by exact prefixLift 6882968
  have htrace : WordTrace (prefixWord ++ tailWord_6882968) baseStart_6882968 baseEnd_6882968 := by
    simpa [prefixWord, tailWord_6882968, baseEnd_6882968] using wordTrace_append hprefix tailTrace_6882968
  have hstable : (prefixWord ++ tailWord_6882968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882968).length < 2 ^ (prefixWord ++ tailWord_6882968).sum := by decide
  have hdescent : baseEnd_6882968 < baseStart_6882968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882978 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_6882978 : Nat := 118140960795 + 6882978 * 2 ^ 59
def prefixEnd_6882978 : Nat := 4983230072969 + 3 ^ 40 * 6882978 * 2
def baseEnd_6882978 : Nat := 1178092016107425516873589

theorem tailTrace_6882978 : CollatzResearch.WordTrace tailWord_6882978 prefixEnd_6882978 1178092016107425516873589 := by
  unfold tailWord_6882978
  simp only [CollatzResearch.WordTrace]
  refine ⟨62760707914538424974914397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167361887772102466599771725 62760707914538424974914397)
  ·
    refine ⟨23535265467951909365592899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62760707914538424974914397 23535265467951909365592899)
    ·
      refine ⟨35302898201927864048389349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23535265467951909365592899 35302898201927864048389349)
      ·
        refine ⟨6619293412861474509073003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35302898201927864048389349 6619293412861474509073003)
        ·
          refine ⟨9928940119292211763609505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619293412861474509073003 9928940119292211763609505)
          ·
            refine ⟨7446705089469158822707129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9928940119292211763609505 7446705089469158822707129)
            ·
              refine ⟨5585028817101869117030347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7446705089469158822707129 5585028817101869117030347)
              ·
                refine ⟨8377543225652803675545521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585028817101869117030347 8377543225652803675545521)
                ·
                  refine ⟨6283157419239602756659141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8377543225652803675545521 6283157419239602756659141)
                  ·
                    refine ⟨1178092016107425516873589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283157419239602756659141 1178092016107425516873589)
                    ·
                      rfl

theorem cell23_6882978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_6882978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882978 prefixEnd_6882978 := by exact prefixLift 6882978
  have htrace : WordTrace (prefixWord ++ tailWord_6882978) baseStart_6882978 baseEnd_6882978 := by
    simpa [prefixWord, tailWord_6882978, baseEnd_6882978] using wordTrace_append hprefix tailTrace_6882978
  have hstable : (prefixWord ++ tailWord_6882978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882978).length < 2 ^ (prefixWord ++ tailWord_6882978).sum := by decide
  have hdescent : baseEnd_6882978 < baseStart_6882978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6882994 : List Nat := [3, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_6882994 : Nat := 118140960795 + 6882994 * 2 ^ 59
def prefixEnd_6882994 : Nat := 4983230072969 + 3 ^ 40 * 6882994 * 2
def baseEnd_6882994 : Nat := 3534284264012748488020693

theorem tailTrace_6882994 : CollatzResearch.WordTrace tailWord_6882994 prefixEnd_6882994 3534284264012748488020693 := by
  unfold tailWord_6882994
  simp only [CollatzResearch.WordTrace]
  refine ⟨62760853806523933658060009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167362276817397156421493357 62760853806523933658060009)
  ·
    refine ⟨47070640354892950243545007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62760853806523933658060009 47070640354892950243545007)
    ·
      refine ⟨70605960532339425365317511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47070640354892950243545007 70605960532339425365317511)
      ·
        refine ⟨105908940798509138047976267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70605960532339425365317511 105908940798509138047976267)
        ·
          refine ⟨158863411197763707071964401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105908940798509138047976267 158863411197763707071964401)
          ·
            refine ⟨119147558398322780303973301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158863411197763707071964401 119147558398322780303973301)
            ·
              refine ⟨11170083599842760653497497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 119147558398322780303973301 11170083599842760653497497)
              ·
                refine ⟨8377562699882070490123123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11170083599842760653497497 8377562699882070490123123)
                ·
                  refine ⟨12566344049823105735184685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8377562699882070490123123 12566344049823105735184685)
                  ·
                    refine ⟨4712379018683664650694257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12566344049823105735184685 4712379018683664650694257)
                    ·
                      refine ⟨3534284264012748488020693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712379018683664650694257 3534284264012748488020693)
                      ·
                        rfl

theorem cell23_6882994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_6882994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6882994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6882994 prefixEnd_6882994 := by exact prefixLift 6882994
  have htrace : WordTrace (prefixWord ++ tailWord_6882994) baseStart_6882994 baseEnd_6882994 := by
    simpa [prefixWord, tailWord_6882994, baseEnd_6882994] using wordTrace_append hprefix tailTrace_6882994
  have hstable : (prefixWord ++ tailWord_6882994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6882994).length < 2 ^ (prefixWord ++ tailWord_6882994).sum := by decide
  have hdescent : baseEnd_6882994 < baseStart_6882994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6882994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883007 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 1, 4, 2]
def baseStart_6883007 : Nat := 118140960795 + 6883007 * 2 ^ 59
def prefixEnd_6883007 : Nat := 4983230072969 + 3 ^ 40 * 6883007 * 2
def baseEnd_6883007 : Nat := 3534290939261256937158133

theorem tailTrace_6883007 : CollatzResearch.WordTrace tailWord_6883007 prefixEnd_6883007 3534290939261256937158133 := by
  unfold tailWord_6883007
  simp only [CollatzResearch.WordTrace]
  refine ⟨251043889375048637852463275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167362592916699091901642183 251043889375048637852463275)
  ·
    refine ⟨376565834062572956778694913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251043889375048637852463275 376565834062572956778694913)
    ·
      refine ⟨282424375546929717584021185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376565834062572956778694913 282424375546929717584021185)
      ·
        refine ⟨211818281660197288188015889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 282424375546929717584021185 211818281660197288188015889)
        ·
          refine ⟨158863711245147966141011917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211818281660197288188015889 158863711245147966141011917)
          ·
            refine ⟨59573891716930487302879469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158863711245147966141011917 59573891716930487302879469)
            ·
              refine ⟨22340209393848932738579801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59573891716930487302879469 22340209393848932738579801)
              ·
                refine ⟨16755157045386699553934851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22340209393848932738579801 16755157045386699553934851)
                ·
                  refine ⟨25132735568080049330902277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16755157045386699553934851 25132735568080049330902277)
                  ·
                    refine ⟨4712387919015009249544177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25132735568080049330902277 4712387919015009249544177)
                    ·
                      refine ⟨3534290939261256937158133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712387919015009249544177 3534290939261256937158133)
                      ·
                        rfl

theorem cell23_6883007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 4, 2].length) (baseStart_6883007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883007 prefixEnd_6883007 := by exact prefixLift 6883007
  have htrace : WordTrace (prefixWord ++ tailWord_6883007) baseStart_6883007 baseEnd_6883007 := by
    simpa [prefixWord, tailWord_6883007, baseEnd_6883007] using wordTrace_append hprefix tailTrace_6883007
  have hstable : (prefixWord ++ tailWord_6883007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883007).length < 2 ^ (prefixWord ++ tailWord_6883007).sum := by decide
  have hdescent : baseEnd_6883007 < baseStart_6883007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883013 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 9]
def baseStart_6883013 : Nat := 118140960795 + 6883013 * 2 ^ 59
def prefixEnd_6883013 : Nat := 4983230072969 + 3 ^ 40 * 6883013 * 2
def baseEnd_6883013 : Nat := 392699335571687101520345

theorem tailTrace_6883013 : CollatzResearch.WordTrace tailWord_6883013 prefixEnd_6883013 392699335571687101520345 := by
  unfold tailWord_6883013
  simp only [CollatzResearch.WordTrace]
  refine ⟨251044108213026900877181693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167362738808684600584787795 251044108213026900877181693)
  ·
    refine ⟨94141540579885087828943135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251044108213026900877181693 94141540579885087828943135)
    ·
      refine ⟨141212310869827631743414703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94141540579885087828943135 141212310869827631743414703)
      ·
        refine ⟨211818466304741447615122055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141212310869827631743414703 211818466304741447615122055)
        ·
          refine ⟨317727699457112171422683083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211818466304741447615122055 317727699457112171422683083)
          ·
            refine ⟨476591549185668257134024625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317727699457112171422683083 476591549185668257134024625)
            ·
              refine ⟨357443661889251192850518469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476591549185668257134024625 357443661889251192850518469)
              ·
                refine ⟨67020686604234598659472213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357443661889251192850518469 67020686604234598659472213)
                ·
                  refine ⟨392699335571687101520345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67020686604234598659472213 392699335571687101520345)
                  ·
                    rfl

theorem cell23_6883013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 9].length) (baseStart_6883013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883013 prefixEnd_6883013 := by exact prefixLift 6883013
  have htrace : WordTrace (prefixWord ++ tailWord_6883013) baseStart_6883013 baseEnd_6883013 := by
    simpa [prefixWord, tailWord_6883013, baseEnd_6883013] using wordTrace_append hprefix tailTrace_6883013
  have hstable : (prefixWord ++ tailWord_6883013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883013).length < 2 ^ (prefixWord ++ tailWord_6883013).sum := by decide
  have hdescent : baseEnd_6883013 < baseStart_6883013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883023 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 7]
def baseStart_6883023 : Nat := 118140960795 + 6883023 * 2 ^ 59
def prefixEnd_6883023 : Nat := 4983230072969 + 3 ^ 40 * 6883023 * 2
def baseEnd_6883023 : Nat := 3534299154951728874558059

theorem tailTrace_6883023 : CollatzResearch.WordTrace tailWord_6883023 prefixEnd_6883023 3534299154951728874558059 := by
  unfold tailWord_6883023
  simp only [CollatzResearch.WordTrace]
  refine ⟨251044472942990672585045723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167362981961993781723363815 251044472942990672585045723)
  ·
    refine ⟨376566709414486008877568585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251044472942990672585045723 376566709414486008877568585)
    ·
      refine ⟨282425032060864506658176439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376566709414486008877568585 282425032060864506658176439)
      ·
        refine ⟨423637548091296759987264659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282425032060864506658176439 423637548091296759987264659)
        ·
          refine ⟨635456322136945139980896989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423637548091296759987264659 635456322136945139980896989)
          ·
            refine ⟨238296120801354427492836371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 635456322136945139980896989 238296120801354427492836371)
            ·
              refine ⟨357444181202031641239254557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238296120801354427492836371 357444181202031641239254557)
              ·
                refine ⟨134041567950761865464720459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357444181202031641239254557 134041567950761865464720459)
                ·
                  refine ⟨201062351926142798197080689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 134041567950761865464720459 201062351926142798197080689)
                  ·
                    refine ⟨150796763944607098647810517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 201062351926142798197080689 150796763944607098647810517)
                    ·
                      refine ⟨3534299154951728874558059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 150796763944607098647810517 3534299154951728874558059)
                      ·
                        rfl

theorem cell23_6883023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_6883023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883023 prefixEnd_6883023 := by exact prefixLift 6883023
  have htrace : WordTrace (prefixWord ++ tailWord_6883023) baseStart_6883023 baseEnd_6883023 := by
    simpa [prefixWord, tailWord_6883023, baseEnd_6883023] using wordTrace_append hprefix tailTrace_6883023
  have hstable : (prefixWord ++ tailWord_6883023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883023).length < 2 ^ (prefixWord ++ tailWord_6883023).sum := by decide
  have hdescent : baseEnd_6883023 < baseStart_6883023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883040 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3]
def baseStart_6883040 : Nat := 118140960795 + 6883040 * 2 ^ 59
def prefixEnd_6883040 : Nat := 4983230072969 + 3 ^ 40 * 6883040 * 2
def baseEnd_6883040 : Nat := 3534307884122855308045481

theorem tailTrace_6883040 : CollatzResearch.WordTrace tailWord_6883040 prefixEnd_6883040 3534307884122855308045481 := by
  unfold tailWord_6883040
  simp only [CollatzResearch.WordTrace]
  refine ⟨125522546491964542244207287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167363395322619389658943049 125522546491964542244207287)
  ·
    refine ⟨188283819737946813366310931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125522546491964542244207287 188283819737946813366310931)
    ·
      refine ⟨282425729606920220049466397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188283819737946813366310931 282425729606920220049466397)
      ·
        refine ⟨105909648602595082518549899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282425729606920220049466397 105909648602595082518549899)
        ·
          refine ⟨158864472903892623777824849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105909648602595082518549899 158864472903892623777824849)
          ·
            refine ⟨119148354677919467833368637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158864472903892623777824849 119148354677919467833368637)
            ·
              refine ⟨44680633004219800437513239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119148354677919467833368637 44680633004219800437513239)
              ·
                refine ⟨67020949506329700656269859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44680633004219800437513239 67020949506329700656269859)
                ·
                  refine ⟨100531424259494550984404789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67020949506329700656269859 100531424259494550984404789)
                  ·
                    refine ⟨9424821024327614154787949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100531424259494550984404789 9424821024327614154787949)
                    ·
                      refine ⟨3534307884122855308045481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9424821024327614154787949 3534307884122855308045481)
                      ·
                        rfl

theorem cell23_6883040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 3].length) (baseStart_6883040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883040 prefixEnd_6883040 := by exact prefixLift 6883040
  have htrace : WordTrace (prefixWord ++ tailWord_6883040) baseStart_6883040 baseEnd_6883040 := by
    simpa [prefixWord, tailWord_6883040, baseEnd_6883040] using wordTrace_append hprefix tailTrace_6883040
  have hstable : (prefixWord ++ tailWord_6883040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883040).length < 2 ^ (prefixWord ++ tailWord_6883040).sum := by decide
  have hdescent : baseEnd_6883040 < baseStart_6883040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883092 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_6883092 : Nat := 118140960795 + 6883092 * 2 ^ 59
def prefixEnd_6883092 : Nat := 4983230072969 + 3 ^ 40 * 6883092 * 2
def baseEnd_6883092 : Nat := 3534334585116889104595243

theorem tailTrace_6883092 : CollatzResearch.WordTrace tailWord_6883092 prefixEnd_6883092 3534334585116889104595243 := by
  unfold tailWord_6883092
  simp only [CollatzResearch.WordTrace]
  refine ⟨125523494789870348684653765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167364659719827131579538353 125523494789870348684653765)
  ·
    refine ⟨23535655273100690378372581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125523494789870348684653765 23535655273100690378372581)
    ·
      refine ⟨4412935363706379445944859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23535655273100690378372581 4412935363706379445944859)
      ·
        refine ⟨6619403045559569168917289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4412935363706379445944859 6619403045559569168917289)
        ·
          refine ⟨4964552284169676876687967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6619403045559569168917289 4964552284169676876687967)
          ·
            refine ⟨7446828426254515315031951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4964552284169676876687967 7446828426254515315031951)
            ·
              refine ⟨11170242639381772972547927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7446828426254515315031951 11170242639381772972547927)
              ·
                refine ⟨16755363959072659458821891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11170242639381772972547927 16755363959072659458821891)
                ·
                  refine ⟨25133045938608989188232837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16755363959072659458821891 25133045938608989188232837)
                  ·
                    refine ⟨4712446113489185472793657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25133045938608989188232837 4712446113489185472793657)
                    ·
                      refine ⟨3534334585116889104595243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712446113489185472793657 3534334585116889104595243)
                      ·
                        rfl

theorem cell23_6883092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_6883092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883092 prefixEnd_6883092 := by exact prefixLift 6883092
  have htrace : WordTrace (prefixWord ++ tailWord_6883092) baseStart_6883092 baseEnd_6883092 := by
    simpa [prefixWord, tailWord_6883092, baseEnd_6883092] using wordTrace_append hprefix tailTrace_6883092
  have hstable : (prefixWord ++ tailWord_6883092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883092).length < 2 ^ (prefixWord ++ tailWord_6883092).sum := by decide
  have hdescent : baseEnd_6883092 < baseStart_6883092 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883107 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 3, 4]
def baseStart_6883107 : Nat := 118140960795 + 6883107 * 2 ^ 59
def prefixEnd_6883107 : Nat := 4983230072969 + 3 ^ 40 * 6883107 * 2
def baseEnd_6883107 : Nat := 1178114095775568848635891

theorem tailTrace_6883107 : CollatzResearch.WordTrace tailWord_6883107 prefixEnd_6883107 1178114095775568848635891 := by
  unfold tailWord_6883107
  simp only [CollatzResearch.WordTrace]
  refine ⟨251047536674686354931103575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167365024449790903287402383 251047536674686354931103575)
  ·
    refine ⟨376571305012029532396655363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251047536674686354931103575 376571305012029532396655363)
    ·
      refine ⟨564856957518044298594983045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376571305012029532396655363 564856957518044298594983045)
      ·
        refine ⟨105910679534633305986559321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 564856957518044298594983045 105910679534633305986559321)
        ·
          refine ⟨79433009650974979489919491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105910679534633305986559321 79433009650974979489919491)
          ·
            refine ⟨119149514476462469234879237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79433009650974979489919491 119149514476462469234879237)
            ·
              refine ⟨22340533964336712981539857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119149514476462469234879237 22340533964336712981539857)
              ·
                refine ⟨16755400473252534736154893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22340533964336712981539857 16755400473252534736154893)
                ·
                  refine ⟨6283275177469700526058085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16755400473252534736154893 6283275177469700526058085)
                  ·
                    refine ⟨1178114095775568848635891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283275177469700526058085 1178114095775568848635891)
                    ·
                      rfl

theorem cell23_6883107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 4].length) (baseStart_6883107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883107 prefixEnd_6883107 := by exact prefixLift 6883107
  have htrace : WordTrace (prefixWord ++ tailWord_6883107) baseStart_6883107 baseEnd_6883107 := by
    simpa [prefixWord, tailWord_6883107, baseEnd_6883107] using wordTrace_append hprefix tailTrace_6883107
  have hstable : (prefixWord ++ tailWord_6883107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883107).length < 2 ^ (prefixWord ++ tailWord_6883107).sum := by decide
  have hdescent : baseEnd_6883107 < baseStart_6883107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883134 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_6883134 : Nat := 118140960795 + 6883134 * 2 ^ 59
def prefixEnd_6883134 : Nat := 4983230072969 + 3 ^ 40 * 6883134 * 2
def baseEnd_6883134 : Nat := 3534356151304377940270049

theorem tailTrace_6883134 : CollatzResearch.WordTrace tailWord_6883134 prefixEnd_6883134 3534356151304377940270049 := by
  unfold tailWord_6883134
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381065180698567317792057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167365680963725692361557637 31381065180698567317792057)
  ·
    refine ⟨23535798885523925488344043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31381065180698567317792057 23535798885523925488344043)
    ·
      refine ⟨35303698328285888232516065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23535798885523925488344043 35303698328285888232516065)
      ·
        refine ⟨26477773746214416174387049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35303698328285888232516065 26477773746214416174387049)
        ·
          refine ⟨19858330309660812130790287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26477773746214416174387049 19858330309660812130790287)
          ·
            refine ⟨29787495464491218196185431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19858330309660812130790287 29787495464491218196185431)
            ·
              refine ⟨44681243196736827294278147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29787495464491218196185431 44681243196736827294278147)
              ·
                refine ⟨67021864795105240941417221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44681243196736827294278147 67021864795105240941417221)
                ·
                  refine ⟨12566599649082232676515729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67021864795105240941417221 12566599649082232676515729)
                  ·
                    refine ⟨9424949736811674507386797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12566599649082232676515729 9424949736811674507386797)
                    ·
                      refine ⟨3534356151304377940270049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9424949736811674507386797 3534356151304377940270049)
                      ·
                        rfl

theorem cell23_6883134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_6883134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883134 prefixEnd_6883134 := by exact prefixLift 6883134
  have htrace : WordTrace (prefixWord ++ tailWord_6883134) baseStart_6883134 baseEnd_6883134 := by
    simpa [prefixWord, tailWord_6883134, baseEnd_6883134] using wordTrace_append hprefix tailTrace_6883134
  have hstable : (prefixWord ++ tailWord_6883134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883134).length < 2 ^ (prefixWord ++ tailWord_6883134).sum := by decide
  have hdescent : baseEnd_6883134 < baseStart_6883134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883141 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 1, 4]
def baseStart_6883141 : Nat := 118140960795 + 6883141 * 2 ^ 59
def prefixEnd_6883141 : Nat := 4983230072969 + 3 ^ 40 * 6883141 * 2
def baseEnd_6883141 : Nat := 1178119915222986470960839

theorem tailTrace_6883141 : CollatzResearch.WordTrace tailWord_6883141 prefixEnd_6883141 1178119915222986470960839 := by
  unfold tailWord_6883141
  simp only [CollatzResearch.WordTrace]
  refine ⟨251048776756563178737841277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167365851171042119158560851 251048776756563178737841277)
  ·
    refine ⟨94143291283711192026690479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251048776756563178737841277 94143291283711192026690479)
    ·
      refine ⟨141214936925566788040035719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94143291283711192026690479 141214936925566788040035719)
      ·
        refine ⟨211822405388350182060053579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141214936925566788040035719 211822405388350182060053579)
        ·
          refine ⟨317733608082525273090080369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211822405388350182060053579 317733608082525273090080369)
          ·
            refine ⟨238300206061893954817560277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317733608082525273090080369 238300206061893954817560277)
            ·
              refine ⟨5585161079575639566036569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238300206061893954817560277 5585161079575639566036569)
              ·
                refine ⟨4188870809681729674527427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5585161079575639566036569 4188870809681729674527427)
                ·
                  refine ⟨6283306214522594511791141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4188870809681729674527427 6283306214522594511791141)
                  ·
                    refine ⟨1178119915222986470960839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283306214522594511791141 1178119915222986470960839)
                    ·
                      rfl

theorem cell23_6883141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 4].length) (baseStart_6883141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883141 prefixEnd_6883141 := by exact prefixLift 6883141
  have htrace : WordTrace (prefixWord ++ tailWord_6883141) baseStart_6883141 baseEnd_6883141 := by
    simpa [prefixWord, tailWord_6883141, baseEnd_6883141] using wordTrace_append hprefix tailTrace_6883141
  have hstable : (prefixWord ++ tailWord_6883141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883141).length < 2 ^ (prefixWord ++ tailWord_6883141).sum := by decide
  have hdescent : baseEnd_6883141 < baseStart_6883141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883150 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_6883150 : Nat := 118140960795 + 6883150 * 2 ^ 59
def prefixEnd_6883150 : Nat := 4983230072969 + 3 ^ 40 * 6883150 * 2
def baseEnd_6883150 : Nat := 1178121455664949959223325

theorem tailTrace_6883150 : CollatzResearch.WordTrace tailWord_6883150 prefixEnd_6883150 1178121455664949959223325 := by
  unfold tailWord_6883150
  simp only [CollatzResearch.WordTrace]
  refine ⟨31381138126691321659364863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167366070009020382183279269 31381138126691321659364863)
  ·
    refine ⟨47071707190036982489047295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31381138126691321659364863 47071707190036982489047295)
    ·
      refine ⟨70607560785055473733570943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47071707190036982489047295 70607560785055473733570943)
      ·
        refine ⟨105911341177583210600356415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70607560785055473733570943 105911341177583210600356415)
        ·
          refine ⟨158867011766374815900534623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105911341177583210600356415 158867011766374815900534623)
          ·
            refine ⟨238300517649562223850801935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158867011766374815900534623 238300517649562223850801935)
            ·
              refine ⟨357450776474343335776202903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238300517649562223850801935 357450776474343335776202903)
              ·
                refine ⟨536176164711515003664304355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 357450776474343335776202903 536176164711515003664304355)
                ·
                  refine ⟨804264247067272505496456533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 536176164711515003664304355 804264247067272505496456533)
                  ·
                    refine ⟨1178121455664949959223325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 804264247067272505496456533 1178121455664949959223325)
                    ·
                      rfl

theorem cell23_6883150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_6883150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883150 prefixEnd_6883150 := by exact prefixLift 6883150
  have htrace : WordTrace (prefixWord ++ tailWord_6883150) baseStart_6883150 baseEnd_6883150 := by
    simpa [prefixWord, tailWord_6883150, baseEnd_6883150] using wordTrace_append hprefix tailTrace_6883150
  have hstable : (prefixWord ++ tailWord_6883150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883150).length < 2 ^ (prefixWord ++ tailWord_6883150).sum := by decide
  have hdescent : baseEnd_6883150 < baseStart_6883150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883154 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 6]
def baseStart_6883154 : Nat := 118140960795 + 6883154 * 2 ^ 59
def prefixEnd_6883154 : Nat := 4983230072969 + 3 ^ 40 * 6883154 * 2
def baseEnd_6883154 : Nat := 392707380101940873557773

theorem tailTrace_6883154 : CollatzResearch.WordTrace tailWord_6883154 prefixEnd_6883154 392707380101940873557773 := by
  unfold tailWord_6883154
  simp only [CollatzResearch.WordTrace]
  refine ⟨62762312726379020489516129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167366167270344054638709677 62762312726379020489516129)
  ·
    refine ⟨47071734544784265367137097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62762312726379020489516129 47071734544784265367137097)
    ·
      refine ⟨35303800908588199025352823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47071734544784265367137097 35303800908588199025352823)
      ·
        refine ⟨52955701362882298538029235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35303800908588199025352823 52955701362882298538029235)
        ·
          refine ⟨79433552044323447807043853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52955701362882298538029235 79433552044323447807043853)
          ·
            refine ⟨29787582016621292927641445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79433552044323447807043853 29787582016621292927641445)
            ·
              refine ⟨5585171628116492423932771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29787582016621292927641445 5585171628116492423932771)
              ·
                refine ⟨8377757442174738635899157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585171628116492423932771 8377757442174738635899157)
                ·
                  refine ⟨392707380101940873557773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8377757442174738635899157 392707380101940873557773)
                  ·
                    rfl

theorem cell23_6883154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_6883154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883154 prefixEnd_6883154 := by exact prefixLift 6883154
  have htrace : WordTrace (prefixWord ++ tailWord_6883154) baseStart_6883154 baseEnd_6883154 := by
    simpa [prefixWord, tailWord_6883154, baseEnd_6883154] using wordTrace_append hprefix tailTrace_6883154
  have hstable : (prefixWord ++ tailWord_6883154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883154).length < 2 ^ (prefixWord ++ tailWord_6883154).sum := by decide
  have hdescent : baseEnd_6883154 < baseStart_6883154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883167 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 3, 5]
def baseStart_6883167 : Nat := 118140960795 + 6883167 * 2 ^ 59
def prefixEnd_6883167 : Nat := 4983230072969 + 3 ^ 40 * 6883167 * 2
def baseEnd_6883167 : Nat := 1178124365388658770385799

theorem tailTrace_6883167 : CollatzResearch.WordTrace tailWord_6883167 prefixEnd_6883167 1178124365388658770385799 := by
  unfold tailWord_6883167
  simp only [CollatzResearch.WordTrace]
  refine ⟨251049725054468985178287755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167366483369645990118858503 251049725054468985178287755)
  ·
    refine ⟨376574587581703477767431633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251049725054468985178287755 376574587581703477767431633)
    ·
      refine ⟨282430940686277608325573725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376574587581703477767431633 282430940686277608325573725)
      ·
        refine ⟨105911602757354103122090147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282430940686277608325573725 105911602757354103122090147)
        ·
          refine ⟨158867404136031154683135221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105911602757354103122090147 158867404136031154683135221)
          ·
            refine ⟨14893819137752920751543927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158867404136031154683135221 14893819137752920751543927)
            ·
              refine ⟨22340728706629381127315891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14893819137752920751543927 22340728706629381127315891)
              ·
                refine ⟨33511093059944071690973837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22340728706629381127315891 33511093059944071690973837)
                ·
                  refine ⟨12566659897479026884115189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33511093059944071690973837 12566659897479026884115189)
                  ·
                    refine ⟨1178124365388658770385799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12566659897479026884115189 1178124365388658770385799)
                    ·
                      rfl

theorem cell23_6883167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_6883167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883167 prefixEnd_6883167 := by exact prefixLift 6883167
  have htrace : WordTrace (prefixWord ++ tailWord_6883167) baseStart_6883167 baseEnd_6883167 := by
    simpa [prefixWord, tailWord_6883167, baseEnd_6883167] using wordTrace_append hprefix tailTrace_6883167
  have hstable : (prefixWord ++ tailWord_6883167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883167).length < 2 ^ (prefixWord ++ tailWord_6883167).sum := by decide
  have hdescent : baseEnd_6883167 < baseStart_6883167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883217 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 4]
def baseStart_6883217 : Nat := 118140960795 + 6883217 * 2 ^ 59
def prefixEnd_6883217 : Nat := 4983230072969 + 3 ^ 40 * 6883217 * 2
def baseEnd_6883217 : Nat := 3534398770198701115532167

theorem tailTrace_6883217 : CollatzResearch.WordTrace tailWord_6883217 prefixEnd_6883217 3534398770198701115532167 := by
  unfold tailWord_6883217
  simp only [CollatzResearch.WordTrace]
  refine ⟨251051548704287843717607905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167367699136191895811738603 251051548704287843717607905)
  ·
    refine ⟨188288661528215882788205929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251051548704287843717607905 188288661528215882788205929)
    ·
      refine ⟨141216496146161912091154447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188288661528215882788205929 141216496146161912091154447)
      ·
        refine ⟨211824744219242868136731671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141216496146161912091154447 211824744219242868136731671)
        ·
          refine ⟨317737116328864302205097507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211824744219242868136731671 317737116328864302205097507)
          ·
            refine ⟨476605674493296453307646261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317737116328864302205097507 476605674493296453307646261)
            ·
              refine ⟨44681781983746542497591837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 476605674493296453307646261 44681781983746542497591837)
              ·
                refine ⟨16755668243904953436596939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44681781983746542497591837 16755668243904953436596939)
                ·
                  refine ⟨25133502365857430154895409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16755668243904953436596939 25133502365857430154895409)
                  ·
                    refine ⟨18850126774393072616171557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25133502365857430154895409 18850126774393072616171557)
                    ·
                      refine ⟨3534398770198701115532167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18850126774393072616171557 3534398770198701115532167)
                      ·
                        rfl

theorem cell23_6883217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 4].length) (baseStart_6883217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883217 prefixEnd_6883217 := by exact prefixLift 6883217
  have htrace : WordTrace (prefixWord ++ tailWord_6883217) baseStart_6883217 baseEnd_6883217 := by
    simpa [prefixWord, tailWord_6883217, baseEnd_6883217] using wordTrace_append hprefix tailTrace_6883217
  have hstable : (prefixWord ++ tailWord_6883217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883217).length < 2 ^ (prefixWord ++ tailWord_6883217).sum := by decide
  have hdescent : baseEnd_6883217 < baseStart_6883217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883221 : List Nat := [1, 3, 2, 1, 1, 3, 3, 2, 3, 2, 2]
def baseStart_6883221 : Nat := 118140960795 + 6883221 * 2 ^ 59
def prefixEnd_6883221 : Nat := 4983230072969 + 3 ^ 40 * 6883221 * 2
def baseEnd_6883221 : Nat := 3534400824121319099882149

theorem tailTrace_6883221 : CollatzResearch.WordTrace tailWord_6883221 prefixEnd_6883221 3534400824121319099882149 := by
  unfold tailWord_6883221
  simp only [CollatzResearch.WordTrace]
  refine ⟨251051694596273352400753517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167367796397515568267169011 251051694596273352400753517)
  ·
    refine ⟨94144385473602507150282569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 251051694596273352400753517 94144385473602507150282569)
    ·
      refine ⟨70608289105201880362711927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94144385473602507150282569 70608289105201880362711927)
      ·
        refine ⟨105912433657802820544067891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70608289105201880362711927 105912433657802820544067891)
        ·
          refine ⟨158868650486704230816101837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105912433657802820544067891 158868650486704230816101837)
          ·
            refine ⟨59575743932514086556038189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 158868650486704230816101837 59575743932514086556038189)
            ·
              refine ⟨22340903974692782458514321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59575743932514086556038189 22340903974692782458514321)
              ·
                refine ⟨16755677981019586843885741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22340903974692782458514321 16755677981019586843885741)
                ·
                  refine ⟨6283379242882345066457153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16755677981019586843885741 6283379242882345066457153)
                  ·
                    refine ⟨4712534432161758799842865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6283379242882345066457153 4712534432161758799842865)
                    ·
                      refine ⟨3534400824121319099882149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712534432161758799842865 3534400824121319099882149)
                      ·
                        rfl

theorem cell23_6883221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_6883221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883221 prefixEnd_6883221 := by exact prefixLift 6883221
  have htrace : WordTrace (prefixWord ++ tailWord_6883221) baseStart_6883221 baseEnd_6883221 := by
    simpa [prefixWord, tailWord_6883221, baseEnd_6883221] using wordTrace_append hprefix tailTrace_6883221
  have hstable : (prefixWord ++ tailWord_6883221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883221).length < 2 ^ (prefixWord ++ tailWord_6883221).sum := by decide
  have hdescent : baseEnd_6883221 < baseStart_6883221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883297 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 5]
def baseStart_6883297 : Nat := 118140960795 + 6883297 * 2 ^ 59
def prefixEnd_6883297 : Nat := 4983230072969 + 3 ^ 40 * 6883297 * 2
def baseEnd_6883297 : Nat := 3534439848651060802531799

theorem tailTrace_6883297 : CollatzResearch.WordTrace tailWord_6883297 prefixEnd_6883297 3534439848651060802531799 := by
  unfold tailWord_6883297
  simp only [CollatzResearch.WordTrace]
  refine ⟨251054466543998017380520145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167369644362665344920346763 251054466543998017380520145)
  ·
    refine ⟨188290849907998513035390109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251054466543998017380520145 188290849907998513035390109)
    ·
      refine ⟨70609068715499442388271291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188290849907998513035390109 70609068715499442388271291)
      ·
        refine ⟨105913603073249163582406937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70609068715499442388271291 105913603073249163582406937)
        ·
          refine ⟨79435202304936872686805203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105913603073249163582406937 79435202304936872686805203)
          ·
            refine ⟨119152803457405309030207805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79435202304936872686805203 119152803457405309030207805)
            ·
              refine ⟨44682301296526990886327927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119152803457405309030207805 44682301296526990886327927)
              ·
                refine ⟨67023451944790486329491891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44682301296526990886327927 67023451944790486329491891)
                ·
                  refine ⟨100535177917185729494237837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67023451944790486329491891 100535177917185729494237837)
                  ·
                    refine ⟨37700691718944648560339189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100535177917185729494237837 37700691718944648560339189)
                    ·
                      refine ⟨3534439848651060802531799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37700691718944648560339189 3534439848651060802531799)
                      ·
                        rfl

theorem cell23_6883297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 3, 5].length) (baseStart_6883297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883297 prefixEnd_6883297 := by exact prefixLift 6883297
  have htrace : WordTrace (prefixWord ++ tailWord_6883297) baseStart_6883297 baseEnd_6883297 := by
    simpa [prefixWord, tailWord_6883297, baseEnd_6883297] using wordTrace_append hprefix tailTrace_6883297
  have hstable : (prefixWord ++ tailWord_6883297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883297).length < 2 ^ (prefixWord ++ tailWord_6883297).sum := by decide
  have hdescent : baseEnd_6883297 < baseStart_6883297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883307 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4]
def baseStart_6883307 : Nat := 118140960795 + 6883307 * 2 ^ 59
def prefixEnd_6883307 : Nat := 4983230072969 + 3 ^ 40 * 6883307 * 2
def baseEnd_6883307 : Nat := 3534444983457605763406753

theorem tailTrace_6883307 : CollatzResearch.WordTrace tailWord_6883307 prefixEnd_6883307 3534444983457605763406753 := by
  unfold tailWord_6883307
  simp only [CollatzResearch.WordTrace]
  refine ⟨251054831273961789088384175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167369887515974526058922783 251054831273961789088384175)
  ·
    refine ⟨376582246910942683632576263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251054831273961789088384175 376582246910942683632576263)
    ·
      refine ⟨564873370366414025448864395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376582246910942683632576263 564873370366414025448864395)
      ·
        refine ⟨847310055549621038173296593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564873370366414025448864395 847310055549621038173296593)
        ·
          refine ⟨635482541662215778629972445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 847310055549621038173296593 635482541662215778629972445)
          ·
            refine ⟨238305953123330916986239667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 635482541662215778629972445 238305953123330916986239667)
            ·
              refine ⟨357458929684996375479359501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238305953123330916986239667 357458929684996375479359501)
              ·
                refine ⟨134047098631873640804759813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357458929684996375479359501 134047098631873640804759813)
                ·
                  refine ⟨25133830993476307650892465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 134047098631873640804759813 25133830993476307650892465)
                  ·
                    refine ⟨18850373245107230738169349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25133830993476307650892465 18850373245107230738169349)
                    ·
                      refine ⟨3534444983457605763406753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18850373245107230738169349 3534444983457605763406753)
                      ·
                        rfl

theorem cell23_6883307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 4].length) (baseStart_6883307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883307 prefixEnd_6883307 := by exact prefixLift 6883307
  have htrace : WordTrace (prefixWord ++ tailWord_6883307) baseStart_6883307 baseEnd_6883307 := by
    simpa [prefixWord, tailWord_6883307, baseEnd_6883307] using wordTrace_append hprefix tailTrace_6883307
  have hstable : (prefixWord ++ tailWord_6883307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883307).length < 2 ^ (prefixWord ++ tailWord_6883307).sum := by decide
  have hdescent : baseEnd_6883307 < baseStart_6883307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883311 : List Nat := [1, 1, 2, 1, 4, 2, 1, 3, 4, 2, 2]
def baseStart_6883311 : Nat := 118140960795 + 6883311 * 2 ^ 59
def prefixEnd_6883311 : Nat := 4983230072969 + 3 ^ 40 * 6883311 * 2
def baseEnd_6883311 : Nat := 3534447037380223747756735

theorem tailTrace_6883311 : CollatzResearch.WordTrace tailWord_6883311 prefixEnd_6883311 3534447037380223747756735 := by
  unfold tailWord_6883311
  simp only [CollatzResearch.WordTrace]
  refine ⟨251054977165947297771529787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167369984777298198514353191 251054977165947297771529787)
  ·
    refine ⟨376582465748920946657294681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251054977165947297771529787 376582465748920946657294681)
    ·
      refine ⟨282436849311690709992971011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376582465748920946657294681 282436849311690709992971011)
      ·
        refine ⟨423655273967536064989456517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282436849311690709992971011 423655273967536064989456517)
        ·
          refine ⟨79435363868913012185523097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 423655273967536064989456517 79435363868913012185523097)
          ·
            refine ⟨59576522901684759139142323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79435363868913012185523097 59576522901684759139142323)
            ·
              refine ⟨89364784352527138708713485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59576522901684759139142323 89364784352527138708713485)
              ·
                refine ⟨33511794132197677015767557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89364784352527138708713485 33511794132197677015767557)
                ·
                  refine ⟨6283461399787064440456417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33511794132197677015767557 6283461399787064440456417)
                  ·
                    refine ⟨4712596049840298330342313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6283461399787064440456417 4712596049840298330342313)
                    ·
                      refine ⟨3534447037380223747756735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712596049840298330342313 3534447037380223747756735)
                      ·
                        rfl

theorem cell23_6883311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 3, 4, 2, 2].length) (baseStart_6883311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883311 prefixEnd_6883311 := by exact prefixLift 6883311
  have htrace : WordTrace (prefixWord ++ tailWord_6883311) baseStart_6883311 baseEnd_6883311 := by
    simpa [prefixWord, tailWord_6883311, baseEnd_6883311] using wordTrace_append hprefix tailTrace_6883311
  have hstable : (prefixWord ++ tailWord_6883311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883311).length < 2 ^ (prefixWord ++ tailWord_6883311).sum := by decide
  have hdescent : baseEnd_6883311 < baseStart_6883311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883332 : List Nat := [2, 3, 2, 4, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6883332 : Nat := 118140960795 + 6883332 * 2 ^ 59
def prefixEnd_6883332 : Nat := 4983230072969 + 3 ^ 40 * 6883332 * 2
def baseEnd_6883332 : Nat := 3534457820473968165594139

theorem tailTrace_6883332 : CollatzResearch.WordTrace tailWord_6883332 prefixEnd_6883332 3534457820473968165594139 := by
  unfold tailWord_6883332
  simp only [CollatzResearch.WordTrace]
  refine ⟨125527871549435609179022125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167370495399247478905362833 125527871549435609179022125)
  ·
    refine ⟨47072951831038353442133297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125527871549435609179022125 47072951831038353442133297)
    ·
      refine ⟨35304713873278765081599973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47072951831038353442133297 35304713873278765081599973)
      ·
        refine ⟨6619633851239768452799995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35304713873278765081599973 6619633851239768452799995)
        ·
          refine ⟨9929450776859652679199993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619633851239768452799995 9929450776859652679199993)
          ·
            refine ⟨7447088082644739509399995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9929450776859652679199993 7447088082644739509399995)
            ·
              refine ⟨11170632123967109264099993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7447088082644739509399995 11170632123967109264099993)
              ·
                refine ⟨8377974092975331948074995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11170632123967109264099993 8377974092975331948074995)
                ·
                  refine ⟨12566961139462997922112493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8377974092975331948074995 12566961139462997922112493)
                  ·
                    refine ⟨4712610427298624220792185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12566961139462997922112493 4712610427298624220792185)
                    ·
                      refine ⟨3534457820473968165594139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712610427298624220792185 3534457820473968165594139)
                      ·
                        rfl

theorem cell23_6883332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6883332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883332 prefixEnd_6883332 := by exact prefixLift 6883332
  have htrace : WordTrace (prefixWord ++ tailWord_6883332) baseStart_6883332 baseEnd_6883332 := by
    simpa [prefixWord, tailWord_6883332, baseEnd_6883332] using wordTrace_append hprefix tailTrace_6883332
  have hstable : (prefixWord ++ tailWord_6883332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883332).length < 2 ^ (prefixWord ++ tailWord_6883332).sum := by decide
  have hdescent : baseEnd_6883332 < baseStart_6883332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883347 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 1, 7]
def baseStart_6883347 : Nat := 118140960795 + 6883347 * 2 ^ 59
def prefixEnd_6883347 : Nat := 4983230072969 + 3 ^ 40 * 6883347 * 2
def baseEnd_6883347 : Nat := 1178155174227928535635523

theorem tailTrace_6883347 : CollatzResearch.WordTrace tailWord_6883347 prefixEnd_6883347 1178155174227928535635523 := by
  unfold tailWord_6883347
  simp only [CollatzResearch.WordTrace]
  refine ⟨251056290193816875919840295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167370860129211250613226863 251056290193816875919840295)
  ·
    refine ⟨376584435290725313879760443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251056290193816875919840295 376584435290725313879760443)
    ·
      refine ⟨564876652936087970819640665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376584435290725313879760443 564876652936087970819640665)
      ·
        refine ⟨423657489702065978114730499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 564876652936087970819640665 423657489702065978114730499)
        ·
          refine ⟨635486234553098967172095749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423657489702065978114730499 635486234553098967172095749)
          ·
            refine ⟨119153668978706056344767953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 635486234553098967172095749 119153668978706056344767953)
            ·
              refine ⟨89365251734029542258575965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119153668978706056344767953 89365251734029542258575965)
              ·
                refine ⟨33511969400261078346965987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89365251734029542258575965 33511969400261078346965987)
                ·
                  refine ⟨50267954100391617520448981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33511969400261078346965987 50267954100391617520448981)
                  ·
                    refine ⟨1178155174227928535635523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50267954100391617520448981 1178155174227928535635523)
                    ·
                      rfl

theorem cell23_6883347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 7].length) (baseStart_6883347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883347 prefixEnd_6883347 := by exact prefixLift 6883347
  have htrace : WordTrace (prefixWord ++ tailWord_6883347) baseStart_6883347 baseEnd_6883347 := by
    simpa [prefixWord, tailWord_6883347, baseEnd_6883347] using wordTrace_append hprefix tailTrace_6883347
  have hstable : (prefixWord ++ tailWord_6883347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883347).length < 2 ^ (prefixWord ++ tailWord_6883347).sum := by decide
  have hdescent : baseEnd_6883347 < baseStart_6883347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883387 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5]
def baseStart_6883387 : Nat := 118140960795 + 6883387 * 2 ^ 59
def prefixEnd_6883387 : Nat := 4983230072969 + 3 ^ 40 * 6883387 * 2
def baseEnd_6883387 : Nat := 3534486061909965450406385

theorem tailTrace_6883387 : CollatzResearch.WordTrace tailWord_6883387 prefixEnd_6883387 3534486061909965450406385 := by
  unfold tailWord_6883387
  simp only [CollatzResearch.WordTrace]
  refine ⟨251057749113671962751296415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167371832742447975167530943 251057749113671962751296415)
  ·
    refine ⟨376586623670507944126944623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251057749113671962751296415 376586623670507944126944623)
    ·
      refine ⟨564879935505761916190416935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376586623670507944126944623 564879935505761916190416935)
      ·
        refine ⟨847319903258642874285625403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564879935505761916190416935 847319903258642874285625403)
        ·
          refine ⟨1270979854887964311428438105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847319903258642874285625403 1270979854887964311428438105)
          ·
            refine ⟨953234891165973233571328579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1270979854887964311428438105 953234891165973233571328579)
            ·
              refine ⟨1429852336748959850356992869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953234891165973233571328579 1429852336748959850356992869)
              ·
                refine ⟨268097313140429971941936163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1429852336748959850356992869 268097313140429971941936163)
                ·
                  refine ⟨402145969710644957912904245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 268097313140429971941936163 402145969710644957912904245)
                  ·
                    refine ⟨37701184660372964804334773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 402145969710644957912904245 37701184660372964804334773)
                    ·
                      refine ⟨3534486061909965450406385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37701184660372964804334773 3534486061909965450406385)
                      ·
                        rfl

theorem cell23_6883387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 5].length) (baseStart_6883387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883387 prefixEnd_6883387 := by exact prefixLift 6883387
  have htrace : WordTrace (prefixWord ++ tailWord_6883387) baseStart_6883387 baseEnd_6883387 := by
    simpa [prefixWord, tailWord_6883387, baseEnd_6883387] using wordTrace_append hprefix tailTrace_6883387
  have hstable : (prefixWord ++ tailWord_6883387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883387).length < 2 ^ (prefixWord ++ tailWord_6883387).sum := by decide
  have hdescent : baseEnd_6883387 < baseStart_6883387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883407 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 10]
def baseStart_6883407 : Nat := 118140960795 + 6883407 * 2 ^ 59
def prefixEnd_6883407 : Nat := 4983230072969 + 3 ^ 40 * 6883407 * 2
def baseEnd_6883407 : Nat := 392721814613672819128477

theorem tailTrace_6883407 : CollatzResearch.WordTrace tailWord_6883407 prefixEnd_6883407 392721814613672819128477 := by
  unfold tailWord_6883407
  simp only [CollatzResearch.WordTrace]
  refine ⟨251058478573599506167024475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167372319049066337444682983 251058478573599506167024475)
  ·
    refine ⟨376587717860399259250536713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251058478573599506167024475 376587717860399259250536713)
    ·
      refine ⟨282440788395299444437902535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376587717860399259250536713 282440788395299444437902535)
      ·
        refine ⟨423661182592949166656853803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282440788395299444437902535 423661182592949166656853803)
        ·
          refine ⟨635491773889423749985280705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423661182592949166656853803 635491773889423749985280705)
          ·
            refine ⟨476618830417067812488960529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 635491773889423749985280705 476618830417067812488960529)
            ·
              refine ⟨357464122812800859366720397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476618830417067812488960529 357464122812800859366720397)
              ·
                refine ⟨134049046054800322262520149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 357464122812800859366720397 134049046054800322262520149)
                ·
                  refine ⟨392721814613672819128477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 134049046054800322262520149 392721814613672819128477)
                  ·
                    rfl

theorem cell23_6883407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 10].length) (baseStart_6883407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883407 prefixEnd_6883407 := by exact prefixLift 6883407
  have htrace : WordTrace (prefixWord ++ tailWord_6883407) baseStart_6883407 baseEnd_6883407 := by
    simpa [prefixWord, tailWord_6883407, baseEnd_6883407] using wordTrace_append hprefix tailTrace_6883407
  have hstable : (prefixWord ++ tailWord_6883407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883407).length < 2 ^ (prefixWord ++ tailWord_6883407).sum := by decide
  have hdescent : baseEnd_6883407 < baseStart_6883407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883424 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 8]
def baseStart_6883424 : Nat := 118140960795 + 6883424 * 2 ^ 59
def prefixEnd_6883424 : Nat := 4983230072969 + 3 ^ 40 * 6883424 * 2
def baseEnd_6883424 : Nat := 392722784521575756182635

theorem tailTrace_6883424 : CollatzResearch.WordTrace tailWord_6883424 prefixEnd_6883424 392722784521575756182635 := by
  unfold tailWord_6883424
  simp only [CollatzResearch.WordTrace]
  refine ⟨125529549307268959035196663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167372732409691945380262217 125529549307268959035196663)
  ·
    refine ⟨188294323960903438552794995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125529549307268959035196663 188294323960903438552794995)
    ·
      refine ⟨282441485941355157829192493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188294323960903438552794995 282441485941355157829192493)
      ·
        refine ⟨105915557228008184185947185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282441485941355157829192493 105915557228008184185947185)
        ·
          refine ⟨79436667921006138139460389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105915557228008184185947185 79436667921006138139460389)
          ·
            refine ⟨14894375235188650901148823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79436667921006138139460389 14894375235188650901148823)
            ·
              refine ⟨22341562852782976351723235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14894375235188650901148823 22341562852782976351723235)
              ·
                refine ⟨33512344279174464527584853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22341562852782976351723235 33512344279174464527584853)
                ·
                  refine ⟨392722784521575756182635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33512344279174464527584853 392722784521575756182635)
                  ·
                    rfl

theorem cell23_6883424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_6883424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883424 prefixEnd_6883424 := by exact prefixLift 6883424
  have htrace : WordTrace (prefixWord ++ tailWord_6883424) baseStart_6883424 baseEnd_6883424 := by
    simpa [prefixWord, tailWord_6883424, baseEnd_6883424] using wordTrace_append hprefix tailTrace_6883424
  have hstable : (prefixWord ++ tailWord_6883424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883424).length < 2 ^ (prefixWord ++ tailWord_6883424).sum := by decide
  have hdescent : baseEnd_6883424 < baseStart_6883424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883428 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_6883428 : Nat := 118140960795 + 6883428 * 2 ^ 59
def prefixEnd_6883428 : Nat := 4983230072969 + 3 ^ 40 * 6883428 * 2
def baseEnd_6883428 : Nat := 1178169038205599929997899

theorem tailTrace_6883428 : CollatzResearch.WordTrace tailWord_6883428 prefixEnd_6883428 1178169038205599929997899 := by
  unfold tailWord_6883428
  simp only [CollatzResearch.WordTrace]
  refine ⟨125529622253261713376769469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167372829671015617835692625 125529622253261713376769469)
  ·
    refine ⟨47073608344973142516288551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 125529622253261713376769469 47073608344973142516288551)
    ·
      refine ⟨70610412517459713774432827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47073608344973142516288551 70610412517459713774432827)
      ·
        refine ⟨105915618776189570661649241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70610412517459713774432827 105915618776189570661649241)
        ·
          refine ⟨79436714082142177996236931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105915618776189570661649241 79436714082142177996236931)
          ·
            refine ⟨119155071123213266994355397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79436714082142177996236931 119155071123213266994355397)
            ·
              refine ⟨22341575835602487561441637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119155071123213266994355397 22341575835602487561441637)
              ·
                refine ⟨4189045469175466417770307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22341575835602487561441637 4189045469175466417770307)
                ·
                  refine ⟨6283568203763199626655461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189045469175466417770307 6283568203763199626655461)
                  ·
                    refine ⟨1178169038205599929997899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283568203763199626655461 1178169038205599929997899)
                    ·
                      rfl

theorem cell23_6883428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_6883428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883428 prefixEnd_6883428 := by exact prefixLift 6883428
  have htrace : WordTrace (prefixWord ++ tailWord_6883428) baseStart_6883428 baseEnd_6883428 := by
    simpa [prefixWord, tailWord_6883428, baseEnd_6883428] using wordTrace_append hprefix tailTrace_6883428
  have hstable : (prefixWord ++ tailWord_6883428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883428).length < 2 ^ (prefixWord ++ tailWord_6883428).sum := by decide
  have hdescent : baseEnd_6883428 < baseStart_6883428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883441 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 6]
def baseStart_6883441 : Nat := 118140960795 + 6883441 * 2 ^ 59
def prefixEnd_6883441 : Nat := 4983230072969 + 3 ^ 40 * 6883441 * 2
def baseEnd_6883441 : Nat := 392723754429478693236793

theorem tailTrace_6883441 : CollatzResearch.WordTrace tailWord_6883441 prefixEnd_6883441 392723754429478693236793 := by
  unfold tailWord_6883441
  simp only [CollatzResearch.WordTrace]
  refine ⟨251059718655476329973762177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167373145770317553315841451 251059718655476329973762177)
  ·
    refine ⟨188294788991607247480321633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251059718655476329973762177 188294788991607247480321633)
    ·
      refine ⟨141221091743705435610241225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188294788991607247480321633 141221091743705435610241225)
      ·
        refine ⟨105915818807779076707680919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 141221091743705435610241225 105915818807779076707680919)
        ·
          refine ⟨158873728211668615061521379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105915818807779076707680919 158873728211668615061521379)
          ·
            refine ⟨238310592317502922592282069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158873728211668615061521379 238310592317502922592282069)
            ·
              refine ⟨5585404507441474748256611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 238310592317502922592282069 5585404507441474748256611)
              ·
                refine ⟨8378106761162212122384917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5585404507441474748256611 8378106761162212122384917)
                ·
                  refine ⟨392723754429478693236793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8378106761162212122384917 392723754429478693236793)
                  ·
                    rfl

theorem cell23_6883441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 6].length) (baseStart_6883441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883441 prefixEnd_6883441 := by exact prefixLift 6883441
  have htrace : WordTrace (prefixWord ++ tailWord_6883441) baseStart_6883441 baseEnd_6883441 := by
    simpa [prefixWord, tailWord_6883441, baseEnd_6883441] using wordTrace_append hprefix tailTrace_6883441
  have hstable : (prefixWord ++ tailWord_6883441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883441).length < 2 ^ (prefixWord ++ tailWord_6883441).sum := by decide
  have hdescent : baseEnd_6883441 < baseStart_6883441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883485 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_6883485 : Nat := 118140960795 + 6883485 * 2 ^ 59
def prefixEnd_6883485 : Nat := 4983230072969 + 3 ^ 40 * 6883485 * 2
def baseEnd_6883485 : Nat := 3534536383014106066980935

theorem tailTrace_6883485 : CollatzResearch.WordTrace tailWord_6883485 prefixEnd_6883485 3534536383014106066980935 := by
  unfold tailWord_6883485
  simp only [CollatzResearch.WordTrace]
  refine ⟨251061323467316925488363909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167374215644877950325575939 251061323467316925488363909)
  ·
    refine ⟨47073998150121923529068233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251061323467316925488363909 47073998150121923529068233)
    ·
      refine ⟨35305498612591442646801175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47073998150121923529068233 35305498612591442646801175)
      ·
        refine ⟨52958247918887163970201763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35305498612591442646801175 52958247918887163970201763)
        ·
          refine ⟨79437371878330745955302645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52958247918887163970201763 79437371878330745955302645)
          ·
            refine ⟨7447253613593507433309623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79437371878330745955302645 7447253613593507433309623)
            ·
              refine ⟨11170880420390261149964435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7447253613593507433309623 11170880420390261149964435)
              ·
                refine ⟨16756320630585391724946653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11170880420390261149964435 16756320630585391724946653)
                ·
                  refine ⟨6283620236469521896854995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16756320630585391724946653 6283620236469521896854995)
                  ·
                    refine ⟨9425430354704282845282493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6283620236469521896854995 9425430354704282845282493)
                    ·
                      refine ⟨3534536383014106066980935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9425430354704282845282493 3534536383014106066980935)
                      ·
                        rfl

theorem cell23_6883485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_6883485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883485 prefixEnd_6883485 := by exact prefixLift 6883485
  have htrace : WordTrace (prefixWord ++ tailWord_6883485) baseStart_6883485 baseEnd_6883485 := by
    simpa [prefixWord, tailWord_6883485, baseEnd_6883485] using wordTrace_append hprefix tailTrace_6883485
  have hstable : (prefixWord ++ tailWord_6883485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883485).length < 2 ^ (prefixWord ++ tailWord_6883485).sum := by decide
  have hdescent : baseEnd_6883485 < baseStart_6883485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883505 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 1, 5]
def baseStart_6883505 : Nat := 118140960795 + 6883505 * 2 ^ 59
def prefixEnd_6883505 : Nat := 4983230072969 + 3 ^ 40 * 6883505 * 2
def baseEnd_6883505 : Nat := 1178182217542398662910281

theorem tailTrace_6883505 : CollatzResearch.WordTrace tailWord_6883505 prefixEnd_6883505 1178182217542398662910281 := by
  unfold tailWord_6883505
  simp only [CollatzResearch.WordTrace]
  refine ⟨251062052927244468904091969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167374701951496312602727979 251062052927244468904091969)
  ·
    refine ⟨188296539695433351678068977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251062052927244468904091969 188296539695433351678068977)
    ·
      refine ⟨141222404771575013758551733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 188296539695433351678068977 141222404771575013758551733)
      ·
        refine ⟨13239600447335157539864225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141222404771575013758551733 13239600447335157539864225)
        ·
          refine ⟨9929700335501368154898169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13239600447335157539864225 9929700335501368154898169)
          ·
            refine ⟨7447275251626026116173627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9929700335501368154898169 7447275251626026116173627)
            ·
              refine ⟨11170912877439039174260441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7447275251626026116173627 11170912877439039174260441)
              ·
                refine ⟨8378184658079279380695331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11170912877439039174260441 8378184658079279380695331)
                ·
                  refine ⟨12567276987118919071042997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8378184658079279380695331 12567276987118919071042997)
                  ·
                    refine ⟨1178182217542398662910281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12567276987118919071042997 1178182217542398662910281)
                    ·
                      rfl

theorem cell23_6883505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 5].length) (baseStart_6883505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883505 prefixEnd_6883505 := by exact prefixLift 6883505
  have htrace : WordTrace (prefixWord ++ tailWord_6883505) baseStart_6883505 baseEnd_6883505 := by
    simpa [prefixWord, tailWord_6883505, baseEnd_6883505] using wordTrace_append hprefix tailTrace_6883505
  have hstable : (prefixWord ++ tailWord_6883505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883505).length < 2 ^ (prefixWord ++ tailWord_6883505).sum := by decide
  have hdescent : baseEnd_6883505 < baseStart_6883505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883514 : List Nat := [3, 1, 1, 1, 2, 2, 4, 9]
def baseStart_6883514 : Nat := 118140960795 + 6883514 * 2 ^ 59
def prefixEnd_6883514 : Nat := 4983230072969 + 3 ^ 40 * 6883514 * 2
def baseEnd_6883514 : Nat := 130909306442706905685863

theorem tailTrace_6883514 : CollatzResearch.WordTrace tailWord_6883514 prefixEnd_6883514 130909306442706905685863 := by
  unfold tailWord_6883514
  simp only [CollatzResearch.WordTrace]
  refine ⟨62765595296052965860292399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167374920789474575627446397 62765595296052965860292399)
  ·
    refine ⟨94148392944079448790438599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62765595296052965860292399 94148392944079448790438599)
    ·
      refine ⟨141222589416119173185657899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94148392944079448790438599 141222589416119173185657899)
      ·
        refine ⟨211833884124178759778486849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141222589416119173185657899 211833884124178759778486849)
        ·
          refine ⟨158875413093134069833865137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211833884124178759778486849 158875413093134069833865137)
          ·
            refine ⟨119156559819850552375398853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158875413093134069833865137 119156559819850552375398853)
            ·
              refine ⟨22341854966221978570387285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119156559819850552375398853 22341854966221978570387285)
              ·
                refine ⟨130909306442706905685863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22341854966221978570387285 130909306442706905685863)
                ·
                  rfl

theorem cell23_6883514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 9].length) (baseStart_6883514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883514 prefixEnd_6883514 := by exact prefixLift 6883514
  have htrace : WordTrace (prefixWord ++ tailWord_6883514) baseStart_6883514 baseEnd_6883514 := by
    simpa [prefixWord, tailWord_6883514, baseEnd_6883514] using wordTrace_append hprefix tailTrace_6883514
  have hstable : (prefixWord ++ tailWord_6883514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883514).length < 2 ^ (prefixWord ++ tailWord_6883514).sum := by decide
  have hdescent : baseEnd_6883514 < baseStart_6883514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883518 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_6883518 : Nat := 118140960795 + 6883518 * 2 ^ 59
def prefixEnd_6883518 : Nat := 4983230072969 + 3 ^ 40 * 6883518 * 2
def baseEnd_6883518 : Nat := 1178184442625234812622761

theorem tailTrace_6883518 : CollatzResearch.WordTrace tailWord_6883518 prefixEnd_6883518 1178184442625234812622761 := by
  unfold tailWord_6883518
  simp only [CollatzResearch.WordTrace]
  refine ⟨31382815884524671515539401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167375018050798248082876805 31382815884524671515539401)
  ·
    refine ⟨23537111913393503636654551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31382815884524671515539401 23537111913393503636654551)
    ·
      refine ⟨35305667870090255454981827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23537111913393503636654551 35305667870090255454981827)
      ·
        refine ⟨52958501805135383182472741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35305667870090255454981827 52958501805135383182472741)
        ·
          refine ⟨9929719088462884346713639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52958501805135383182472741 9929719088462884346713639)
          ·
            refine ⟨14894578632694326520070459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929719088462884346713639 14894578632694326520070459)
            ·
              refine ⟨22341867949041489780105689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14894578632694326520070459 22341867949041489780105689)
              ·
                refine ⟨16756400961781117335079267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22341867949041489780105689 16756400961781117335079267)
                ·
                  refine ⟨25134601442671676002618901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16756400961781117335079267 25134601442671676002618901)
                  ·
                    refine ⟨1178184442625234812622761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25134601442671676002618901 1178184442625234812622761)
                    ·
                      rfl

theorem cell23_6883518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_6883518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883518 prefixEnd_6883518 := by exact prefixLift 6883518
  have htrace : WordTrace (prefixWord ++ tailWord_6883518) baseStart_6883518 baseEnd_6883518 := by
    simpa [prefixWord, tailWord_6883518, baseEnd_6883518] using wordTrace_append hprefix tailTrace_6883518
  have hstable : (prefixWord ++ tailWord_6883518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883518).length < 2 ^ (prefixWord ++ tailWord_6883518).sum := by decide
  have hdescent : baseEnd_6883518 < baseStart_6883518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883555 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6883555 : Nat := 118140960795 + 6883555 * 2 ^ 59
def prefixEnd_6883555 : Nat := 4983230072969 + 3 ^ 40 * 6883555 * 2
def baseEnd_6883555 : Nat := 3534572326659920793105613

theorem tailTrace_6883555 : CollatzResearch.WordTrace tailWord_6883555 prefixEnd_6883555 3534572326659920793105613 := by
  unfold tailWord_6883555
  simp only [CollatzResearch.WordTrace]
  refine ⟨251063876577063327443412119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167375917718042218295608079 251063876577063327443412119)
  ·
    refine ⟨376595814865594991165118179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251063876577063327443412119 376595814865594991165118179)
    ·
      refine ⟨564893722298392486747677269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376595814865594991165118179 564893722298392486747677269)
      ·
        refine ⟨6619848308184286954074343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 564893722298392486747677269 6619848308184286954074343)
        ·
          refine ⟨9929772462276430431111515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6619848308184286954074343 9929772462276430431111515)
          ·
            refine ⟨14894658693414645646667273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9929772462276430431111515 14894658693414645646667273)
            ·
              refine ⟨11170994020060984235000455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14894658693414645646667273 11170994020060984235000455)
              ·
                refine ⟨16756491030091476352500683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11170994020060984235000455 16756491030091476352500683)
                ·
                  refine ⟨25134736545137214528751025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16756491030091476352500683 25134736545137214528751025)
                  ·
                    refine ⟨18851052408852910896563269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25134736545137214528751025 18851052408852910896563269)
                    ·
                      refine ⟨3534572326659920793105613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18851052408852910896563269 3534572326659920793105613)
                      ·
                        rfl

theorem cell23_6883555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6883555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883555 prefixEnd_6883555 := by exact prefixLift 6883555
  have htrace : WordTrace (prefixWord ++ tailWord_6883555) baseStart_6883555 baseEnd_6883555 := by
    simpa [prefixWord, tailWord_6883555, baseEnd_6883555] using wordTrace_append hprefix tailTrace_6883555
  have hstable : (prefixWord ++ tailWord_6883555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883555).length < 2 ^ (prefixWord ++ tailWord_6883555).sum := by decide
  have hdescent : baseEnd_6883555 < baseStart_6883555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883585 : List Nat := [1, 2, 4, 1, 1, 2, 3, 3, 1, 3, 2]
def baseStart_6883585 : Nat := 118140960795 + 6883585 * 2 ^ 59
def prefixEnd_6883585 : Nat := 4983230072969 + 3 ^ 40 * 6883585 * 2
def baseEnd_6883585 : Nat := 3534587731079555675730475

theorem tailTrace_6883585 : CollatzResearch.WordTrace tailWord_6883585 prefixEnd_6883585 3534587731079555675730475 := by
  unfold tailWord_6883585
  simp only [CollatzResearch.WordTrace]
  refine ⟨251064970766954642567004209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167376647177969761711336139 251064970766954642567004209)
  ·
    refine ⟨188298728075215981925253157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 251064970766954642567004209 188298728075215981925253157)
    ·
      refine ⟨35306011514102996610984967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 188298728075215981925253157 35306011514102996610984967)
      ·
        refine ⟨52959017271154494916477451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35306011514102996610984967 52959017271154494916477451)
        ·
          refine ⟨79438525906731742374716177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52959017271154494916477451 79438525906731742374716177)
          ·
            refine ⟨59578894430048806781037133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79438525906731742374716177 59578894430048806781037133)
            ·
              refine ⟨22342085411268302542888925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59578894430048806781037133 22342085411268302542888925)
              ·
                refine ⟨8378282029225613453583347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22342085411268302542888925 8378282029225613453583347)
                ·
                  refine ⟨12567423043838420180375021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8378282029225613453583347 12567423043838420180375021)
                  ·
                    refine ⟨4712783641439407567640633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12567423043838420180375021 4712783641439407567640633)
                    ·
                      refine ⟨3534587731079555675730475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712783641439407567640633 3534587731079555675730475)
                      ·
                        rfl

theorem cell23_6883585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_6883585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883585 prefixEnd_6883585 := by exact prefixLift 6883585
  have htrace : WordTrace (prefixWord ++ tailWord_6883585) baseStart_6883585 baseEnd_6883585 := by
    simpa [prefixWord, tailWord_6883585, baseEnd_6883585] using wordTrace_append hprefix tailTrace_6883585
  have hstable : (prefixWord ++ tailWord_6883585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883585).length < 2 ^ (prefixWord ++ tailWord_6883585).sum := by decide
  have hdescent : baseEnd_6883585 < baseStart_6883585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883592 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 2, 1, 3]
def baseStart_6883592 : Nat := 118140960795 + 6883592 * 2 ^ 59
def prefixEnd_6883592 : Nat := 4983230072969 + 3 ^ 40 * 6883592 * 2
def baseEnd_6883592 : Nat := 3534591325444137148342943

theorem tailTrace_6883592 : CollatzResearch.WordTrace tailWord_6883592 prefixEnd_6883592 3534591325444137148342943 := by
  unfold tailWord_6883592
  simp only [CollatzResearch.WordTrace]
  refine ⟨125532613038964641381254515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167376817385286188508339353 125532613038964641381254515)
  ·
    refine ⟨188298919558446962071881773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125532613038964641381254515 188298919558446962071881773)
    ·
      refine ⟨70612094834417610776955665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 188298919558446962071881773 70612094834417610776955665)
      ·
        refine ⟨52959071125813208082716749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70612094834417610776955665 52959071125813208082716749)
        ·
          refine ⟨19859651672179953031018781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52959071125813208082716749 19859651672179953031018781)
          ·
            refine ⟨7447369377067482386632043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19859651672179953031018781 7447369377067482386632043)
            ·
              refine ⟨11171054065601223579948065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7447369377067482386632043 11171054065601223579948065)
              ·
                refine ⟨8378290549200917684961049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11171054065601223579948065 8378290549200917684961049)
                ·
                  refine ⟨6283717911900688263720787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8378290549200917684961049 6283717911900688263720787)
                  ·
                    refine ⟨9425576867851032395581181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6283717911900688263720787 9425576867851032395581181)
                    ·
                      refine ⟨3534591325444137148342943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9425576867851032395581181 3534591325444137148342943)
                      ·
                        rfl

theorem cell23_6883592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_6883592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883592 prefixEnd_6883592 := by exact prefixLift 6883592
  have htrace : WordTrace (prefixWord ++ tailWord_6883592) baseStart_6883592 baseEnd_6883592 := by
    simpa [prefixWord, tailWord_6883592, baseEnd_6883592] using wordTrace_append hprefix tailTrace_6883592
  have hstable : (prefixWord ++ tailWord_6883592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883592).length < 2 ^ (prefixWord ++ tailWord_6883592).sum := by decide
  have hdescent : baseEnd_6883592 < baseStart_6883592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883611 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4]
def baseStart_6883611 : Nat := 118140960795 + 6883611 * 2 ^ 59
def prefixEnd_6883611 : Nat := 4983230072969 + 3 ^ 40 * 6883611 * 2
def baseEnd_6883611 : Nat := 3534601081576572574005355

theorem tailTrace_6883611 : CollatzResearch.WordTrace tailWord_6883611 prefixEnd_6883611 3534601081576572574005355 := by
  unfold tailWord_6883611
  simp only [CollatzResearch.WordTrace]
  refine ⟨251065919064860449007450687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167377279376573632671633791 251065919064860449007450687)
  ·
    refine ⟨376598878597290673511176031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251065919064860449007450687 376598878597290673511176031)
    ·
      refine ⟨564898317895936010266764047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376598878597290673511176031 564898317895936010266764047)
      ·
        refine ⟨847347476843904015400146071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564898317895936010266764047 847347476843904015400146071)
        ·
          refine ⟨1271021215265856023100219107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847347476843904015400146071 1271021215265856023100219107)
          ·
            refine ⟨1906531822898784034650328661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271021215265856023100219107 1906531822898784034650328661)
            ·
              refine ⟨22342169799595125406058539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1906531822898784034650328661 22342169799595125406058539)
              ·
                refine ⟨33513254699392688109087809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22342169799595125406058539 33513254699392688109087809)
                ·
                  refine ⟨25134941024544516081815857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33513254699392688109087809 25134941024544516081815857)
                  ·
                    refine ⟨18851205768408387061361893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25134941024544516081815857 18851205768408387061361893)
                    ·
                      refine ⟨3534601081576572574005355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18851205768408387061361893 3534601081576572574005355)
                      ·
                        rfl

theorem cell23_6883611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 2, 4].length) (baseStart_6883611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883611 prefixEnd_6883611 := by exact prefixLift 6883611
  have htrace : WordTrace (prefixWord ++ tailWord_6883611) baseStart_6883611 baseEnd_6883611 := by
    simpa [prefixWord, tailWord_6883611, baseEnd_6883611] using wordTrace_append hprefix tailTrace_6883611
  have hstable : (prefixWord ++ tailWord_6883611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883611).length < 2 ^ (prefixWord ++ tailWord_6883611).sum := by decide
  have hdescent : baseEnd_6883611 < baseStart_6883611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883615 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 1, 4, 2]
def baseStart_6883615 : Nat := 118140960795 + 6883615 * 2 ^ 59
def prefixEnd_6883615 : Nat := 4983230072969 + 3 ^ 40 * 6883615 * 2
def baseEnd_6883615 : Nat := 3534603135499190558355337

theorem tailTrace_6883615 : CollatzResearch.WordTrace tailWord_6883615 prefixEnd_6883615 3534603135499190558355337 := by
  unfold tailWord_6883615
  simp only [CollatzResearch.WordTrace]
  refine ⟨251066064956845957690596299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167377376637897305127064199 251066064956845957690596299)
  ·
    refine ⟨376599097435268936535894449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251066064956845957690596299 376599097435268936535894449)
    ·
      refine ⟨282449323076451702401920837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376599097435268936535894449 282449323076451702401920837)
      ·
        refine ⟨52959248076834694200360157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 282449323076451702401920837 52959248076834694200360157)
        ·
          refine ⟨19859718028813010325135059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52959248076834694200360157 19859718028813010325135059)
          ·
            refine ⟨29789577043219515487702589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19859718028813010325135059 29789577043219515487702589)
            ·
              refine ⟨11171091391207318307888471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29789577043219515487702589 11171091391207318307888471)
              ·
                refine ⟨16756637086810977461832707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11171091391207318307888471 16756637086810977461832707)
                ·
                  refine ⟨25134955630216466192749061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16756637086810977461832707 25134955630216466192749061)
                  ·
                    refine ⟨4712804180665587411140449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25134955630216466192749061 4712804180665587411140449)
                    ·
                      refine ⟨3534603135499190558355337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712804180665587411140449 3534603135499190558355337)
                      ·
                        rfl

theorem cell23_6883615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_6883615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883615 prefixEnd_6883615 := by exact prefixLift 6883615
  have htrace : WordTrace (prefixWord ++ tailWord_6883615) baseStart_6883615 baseEnd_6883615 := by
    simpa [prefixWord, tailWord_6883615, baseEnd_6883615] using wordTrace_append hprefix tailTrace_6883615
  have hstable : (prefixWord ++ tailWord_6883615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883615).length < 2 ^ (prefixWord ++ tailWord_6883615).sum := by decide
  have hdescent : baseEnd_6883615 < baseStart_6883615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883631 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 3]
def baseStart_6883631 : Nat := 118140960795 + 6883631 * 2 ^ 59
def prefixEnd_6883631 : Nat := 4983230072969 + 3 ^ 40 * 6883631 * 2
def baseEnd_6883631 : Nat := 3534611351189662495755263

theorem tailTrace_6883631 : CollatzResearch.WordTrace tailWord_6883631 prefixEnd_6883631 3534611351189662495755263 := by
  unfold tailWord_6883631
  simp only [CollatzResearch.WordTrace]
  refine ⟨251066648524787992423178747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167377765683191994948785831 251066648524787992423178747)
  ·
    refine ⟨376599972787181988634768121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251066648524787992423178747 376599972787181988634768121)
    ·
      refine ⟨282449979590386491476076091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 376599972787181988634768121 282449979590386491476076091)
      ·
        refine ⟨423674969385579737214114137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282449979590386491476076091 423674969385579737214114137)
        ·
          refine ⟨317756227039184802910585603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423674969385579737214114137 317756227039184802910585603)
          ·
            refine ⟨476634340558777204365878405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317756227039184802910585603 476634340558777204365878405)
            ·
              refine ⟨89368938854770725818602201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 476634340558777204365878405 89368938854770725818602201)
              ·
                refine ⟨67026704141078044363951651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89368938854770725818602201 67026704141078044363951651)
                ·
                  refine ⟨100540056211617066545927477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67026704141078044363951651 100540056211617066545927477)
                  ·
                    refine ⟨9425630269839099988680701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 100540056211617066545927477 9425630269839099988680701)
                    ·
                      refine ⟨3534611351189662495755263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9425630269839099988680701 3534611351189662495755263)
                      ·
                        rfl

theorem cell23_6883631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_6883631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883631 prefixEnd_6883631 := by exact prefixLift 6883631
  have htrace : WordTrace (prefixWord ++ tailWord_6883631) baseStart_6883631 baseEnd_6883631 := by
    simpa [prefixWord, tailWord_6883631, baseEnd_6883631] using wordTrace_append hprefix tailTrace_6883631
  have hstable : (prefixWord ++ tailWord_6883631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883631).length < 2 ^ (prefixWord ++ tailWord_6883631).sum := by decide
  have hdescent : baseEnd_6883631 < baseStart_6883631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883651 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 4, 5]
def baseStart_6883651 : Nat := 118140960795 + 6883651 * 2 ^ 59
def prefixEnd_6883651 : Nat := 4983230072969 + 3 ^ 40 * 6883651 * 2
def baseEnd_6883651 : Nat := 1178207206934250805835057

theorem tailTrace_6883651 : CollatzResearch.WordTrace tailWord_6883651 prefixEnd_6883651 1178207206934250805835057 := by
  unfold tailWord_6883651
  simp only [CollatzResearch.WordTrace]
  refine ⟨251067377984715535838906807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167378251989810357225937871 251067377984715535838906807)
  ·
    refine ⟨376601066977073303758360211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251067377984715535838906807 376601066977073303758360211)
    ·
      refine ⟨564901600465609955637540317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376601066977073303758360211 564901600465609955637540317)
      ·
        refine ⟨211838100174603733364077619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 564901600465609955637540317 211838100174603733364077619)
        ·
          refine ⟨317757150261905600046116429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211838100174603733364077619 317757150261905600046116429)
          ·
            refine ⟨119158931348214600017293661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317757150261905600046116429 119158931348214600017293661)
            ·
              refine ⟨44684599255580475006485123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119158931348214600017293661 44684599255580475006485123)
              ·
                refine ⟨67026898883370712509727685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44684599255580475006485123 67026898883370712509727685)
                ·
                  refine ⟨12567543540632008595573941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67026898883370712509727685 12567543540632008595573941)
                  ·
                    refine ⟨1178207206934250805835057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12567543540632008595573941 1178207206934250805835057)
                    ·
                      rfl

theorem cell23_6883651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 5].length) (baseStart_6883651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883651 prefixEnd_6883651 := by exact prefixLift 6883651
  have htrace : WordTrace (prefixWord ++ tailWord_6883651) baseStart_6883651 baseEnd_6883651 := by
    simpa [prefixWord, tailWord_6883651, baseEnd_6883651] using wordTrace_append hprefix tailTrace_6883651
  have hstable : (prefixWord ++ tailWord_6883651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883651).length < 2 ^ (prefixWord ++ tailWord_6883651).sum := by decide
  have hdescent : baseEnd_6883651 < baseStart_6883651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883655 : List Nat := [1, 1, 4, 1, 2, 2, 5, 2, 5]
def baseStart_6883655 : Nat := 118140960795 + 6883655 * 2 ^ 59
def prefixEnd_6883655 : Nat := 4983230072969 + 3 ^ 40 * 6883655 * 2
def baseEnd_6883655 : Nat := 392735963858374489095017

theorem tailTrace_6883655 : CollatzResearch.WordTrace tailWord_6883655 prefixEnd_6883655 392735963858374489095017 := by
  unfold tailWord_6883655
  simp only [CollatzResearch.WordTrace]
  refine ⟨251067523876701044522052419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167378349251134029681368279 251067523876701044522052419)
  ·
    refine ⟨376601285815051566783078629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251067523876701044522052419 376601285815051566783078629)
    ·
      refine ⟨70612741090322168771827243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376601285815051566783078629 70612741090322168771827243)
      ·
        refine ⟨105919111635483253157740865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70612741090322168771827243 105919111635483253157740865)
        ·
          refine ⟨79439333726612439868305649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105919111635483253157740865 79439333726612439868305649)
          ·
            refine ⟨59579500294959329901229237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79439333726612439868305649 59579500294959329901229237)
            ·
              refine ⟨5585578152652437178240241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59579500294959329901229237 5585578152652437178240241)
              ·
                refine ⟨4189183614489327883680181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5585578152652437178240241 4189183614489327883680181)
                ·
                  refine ⟨392735963858374489095017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4189183614489327883680181 392735963858374489095017)
                  ·
                    rfl

theorem cell23_6883655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 2, 5].length) (baseStart_6883655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883655 prefixEnd_6883655 := by exact prefixLift 6883655
  have htrace : WordTrace (prefixWord ++ tailWord_6883655) baseStart_6883655 baseEnd_6883655 := by
    simpa [prefixWord, tailWord_6883655, baseEnd_6883655] using wordTrace_append hprefix tailTrace_6883655
  have hstable : (prefixWord ++ tailWord_6883655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883655).length < 2 ^ (prefixWord ++ tailWord_6883655).sum := by decide
  have hdescent : baseEnd_6883655 < baseStart_6883655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883708 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_6883708 : Nat := 118140960795 + 6883708 * 2 ^ 59
def prefixEnd_6883708 : Nat := 4983230072969 + 3 ^ 40 * 6883708 * 2
def baseEnd_6883708 : Nat := 3534650889200058694492409

theorem tailTrace_6883708 : CollatzResearch.WordTrace tailWord_6883708 prefixEnd_6883708 3534650889200058694492409 := by
  unfold tailWord_6883708
  simp only [CollatzResearch.WordTrace]
  refine ⟨125534728472754517286865889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167379637963672689715821185 125534728472754517286865889)
  ·
    refine ⟨94151046354565887965149417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125534728472754517286865889 94151046354565887965149417)
    ·
      refine ⟨70613284765924415973862063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94151046354565887965149417 70613284765924415973862063)
      ·
        refine ⟨105919927148886623960793095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70613284765924415973862063 105919927148886623960793095)
        ·
          refine ⟨158879890723329935941189643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105919927148886623960793095 158879890723329935941189643)
          ·
            refine ⟨238319836084994903911784465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158879890723329935941189643 238319836084994903911784465)
            ·
              refine ⟨178739877063746177933838349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238319836084994903911784465 178739877063746177933838349)
              ·
                refine ⟨67027453898904816725189381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178739877063746177933838349 67027453898904816725189381)
                ·
                  refine ⟨12567647606044653135973009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67027453898904816725189381 12567647606044653135973009)
                  ·
                    refine ⟨9425735704533489851979757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12567647606044653135973009 9425735704533489851979757)
                    ·
                      refine ⟨3534650889200058694492409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9425735704533489851979757 3534650889200058694492409)
                      ·
                        rfl

theorem cell23_6883708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_6883708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883708 prefixEnd_6883708 := by exact prefixLift 6883708
  have htrace : WordTrace (prefixWord ++ tailWord_6883708) baseStart_6883708 baseEnd_6883708 := by
    simpa [prefixWord, tailWord_6883708, baseEnd_6883708] using wordTrace_append hprefix tailTrace_6883708
  have hstable : (prefixWord ++ tailWord_6883708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883708).length < 2 ^ (prefixWord ++ tailWord_6883708).sum := by decide
  have hdescent : baseEnd_6883708 < baseStart_6883708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883732 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_6883732 : Nat := 118140960795 + 6883732 * 2 ^ 59
def prefixEnd_6883732 : Nat := 4983230072969 + 3 ^ 40 * 6883732 * 2
def baseEnd_6883732 : Nat := 1178221070911922200197433

theorem tailTrace_6883732 : CollatzResearch.WordTrace tailWord_6883732 prefixEnd_6883732 1178221070911922200197433 := by
  unfold tailWord_6883732
  simp only [CollatzResearch.WordTrace]
  refine ⟨125535166148711043336302725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167380221531614724448403633 125535166148711043336302725)
  ·
    refine ⟨23537843652883320625556761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 125535166148711043336302725 23537843652883320625556761)
    ·
      refine ⟨17653382739662490469167571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23537843652883320625556761 17653382739662490469167571)
      ·
        refine ⟨26480074109493735703751357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17653382739662490469167571 26480074109493735703751357)
        ·
          refine ⟨9930027791060150888906759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26480074109493735703751357 9930027791060150888906759)
          ·
            refine ⟨14895041686590226333360139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9930027791060150888906759 14895041686590226333360139)
            ·
              refine ⟨22342562529885339500040209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895041686590226333360139 22342562529885339500040209)
              ·
                refine ⟨16756921897414004625030157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22342562529885339500040209 16756921897414004625030157)
                ·
                  refine ⟨6283845711530251734386309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16756921897414004625030157 6283845711530251734386309)
                  ·
                    refine ⟨1178221070911922200197433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283845711530251734386309 1178221070911922200197433)
                    ·
                      rfl

theorem cell23_6883732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_6883732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883732 prefixEnd_6883732 := by exact prefixLift 6883732
  have htrace : WordTrace (prefixWord ++ tailWord_6883732) baseStart_6883732 baseEnd_6883732 := by
    simpa [prefixWord, tailWord_6883732, baseEnd_6883732] using wordTrace_append hprefix tailTrace_6883732
  have hstable : (prefixWord ++ tailWord_6883732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883732).length < 2 ^ (prefixWord ++ tailWord_6883732).sum := by decide
  have hdescent : baseEnd_6883732 < baseStart_6883732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883742 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6883742 : Nat := 118140960795 + 6883742 * 2 ^ 59
def prefixEnd_6883742 : Nat := 4983230072969 + 3 ^ 40 * 6883742 * 2
def baseEnd_6883742 : Nat := 3534668347542311561467253

theorem tailTrace_6883742 : CollatzResearch.WordTrace tailWord_6883742 prefixEnd_6883742 3534668347542311561467253 := by
  unfold tailWord_6883742
  simp only [CollatzResearch.WordTrace]
  refine ⟨31383837128423232297558685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 167380464684923905586979653 31383837128423232297558685)
  ·
    refine ⟨11768938923158712111584507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31383837128423232297558685 11768938923158712111584507)
    ·
      refine ⟨17653408384738068167376761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11768938923158712111584507 17653408384738068167376761)
      ·
        refine ⟨13240056288553551125532571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17653408384738068167376761 13240056288553551125532571)
        ·
          refine ⟨19860084432830326688298857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240056288553551125532571 19860084432830326688298857)
          ·
            refine ⟨14895063324622745016224143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19860084432830326688298857 14895063324622745016224143)
            ·
              refine ⟨22342594986934117524336215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895063324622745016224143 22342594986934117524336215)
              ·
                refine ⟨33513892480401176286504323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22342594986934117524336215 33513892480401176286504323)
                ·
                  refine ⟨50270838720601764429756485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33513892480401176286504323 50270838720601764429756485)
                  ·
                    refine ⟨9425782260112830830579341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50270838720601764429756485 9425782260112830830579341)
                    ·
                      refine ⟨3534668347542311561467253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9425782260112830830579341 3534668347542311561467253)
                      ·
                        rfl

theorem cell23_6883742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6883742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883742 prefixEnd_6883742 := by exact prefixLift 6883742
  have htrace : WordTrace (prefixWord ++ tailWord_6883742) baseStart_6883742 baseEnd_6883742 := by
    simpa [prefixWord, tailWord_6883742, baseEnd_6883742] using wordTrace_append hprefix tailTrace_6883742
  have hstable : (prefixWord ++ tailWord_6883742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883742).length < 2 ^ (prefixWord ++ tailWord_6883742).sum := by decide
  have hdescent : baseEnd_6883742 < baseStart_6883742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883772 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6883772 : Nat := 118140960795 + 6883772 * 2 ^ 59
def prefixEnd_6883772 : Nat := 4983230072969 + 3 ^ 40 * 6883772 * 2
def baseEnd_6883772 : Nat := 3534683751961946444092115

theorem tailTrace_6883772 : CollatzResearch.WordTrace tailWord_6883772 prefixEnd_6883772 3534683751961946444092115 := by
  unfold tailWord_6883772
  simp only [CollatzResearch.WordTrace]
  refine ⟨125535895608638586752030785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167381194144851449002707713 125535895608638586752030785)
  ·
    refine ⟨94151921706478940064023089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 125535895608638586752030785 94151921706478940064023089)
    ·
      refine ⟨70613941279859205048017317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94151921706478940064023089 70613941279859205048017317)
      ·
        refine ⟨13240113989973600946503247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70613941279859205048017317 13240113989973600946503247)
        ·
          refine ⟨19860170984960401419754871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240113989973600946503247 19860170984960401419754871)
          ·
            refine ⟨29790256477440602129632307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19860170984960401419754871 29790256477440602129632307)
            ·
              refine ⟨44685384716160903194448461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29790256477440602129632307 44685384716160903194448461)
              ·
                refine ⟨16757019268560338697918173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44685384716160903194448461 16757019268560338697918173)
                ·
                  refine ⟨6283882225710127011719315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16757019268560338697918173 6283882225710127011719315)
                  ·
                    refine ⟨9425823338565190517578973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6283882225710127011719315 9425823338565190517578973)
                    ·
                      refine ⟨3534683751961946444092115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9425823338565190517578973 3534683751961946444092115)
                      ·
                        rfl

theorem cell23_6883772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6883772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883772 prefixEnd_6883772 := by exact prefixLift 6883772
  have htrace : WordTrace (prefixWord ++ tailWord_6883772) baseStart_6883772 baseEnd_6883772 := by
    simpa [prefixWord, tailWord_6883772, baseEnd_6883772] using wordTrace_append hprefix tailTrace_6883772
  have hstable : (prefixWord ++ tailWord_6883772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883772).length < 2 ^ (prefixWord ++ tailWord_6883772).sum := by decide
  have hdescent : baseEnd_6883772 < baseStart_6883772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883805 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6883805 : Nat := 118140960795 + 6883805 * 2 ^ 59
def prefixEnd_6883805 : Nat := 4983230072969 + 3 ^ 40 * 6883805 * 2
def baseEnd_6883805 : Nat := 1178233565607848271659821

theorem tailTrace_6883805 : CollatzResearch.WordTrace tailWord_6883805 prefixEnd_6883805 1178233565607848271659821 := by
  unfold tailWord_6883805
  simp only [CollatzResearch.WordTrace]
  refine ⟨251072994826157620140012869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167381996550771746760008579 251072994826157620140012869)
  ·
    refine ⟨47076186529904553776252413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 251072994826157620140012869 47076186529904553776252413)
    ·
      refine ⟨17653569948714207666094655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47076186529904553776252413 17653569948714207666094655)
      ·
        refine ⟨26480354923071311499141983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17653569948714207666094655 26480354923071311499141983)
        ·
          refine ⟨39720532384606967248712975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26480354923071311499141983 39720532384606967248712975)
          ·
            refine ⟨59580798576910450873069463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39720532384606967248712975 59580798576910450873069463)
            ·
              refine ⟨89371197865365676309604195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59580798576910450873069463 89371197865365676309604195)
              ·
                refine ⟨134056796798048514464406293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89371197865365676309604195 134056796798048514464406293)
                ·
                  refine ⟨6283912349908524115519045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 134056796798048514464406293 6283912349908524115519045)
                  ·
                    refine ⟨1178233565607848271659821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6283912349908524115519045 1178233565607848271659821)
                    ·
                      rfl

theorem cell23_6883805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6883805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883805 prefixEnd_6883805 := by exact prefixLift 6883805
  have htrace : WordTrace (prefixWord ++ tailWord_6883805) baseStart_6883805 baseEnd_6883805 := by
    simpa [prefixWord, tailWord_6883805, baseEnd_6883805] using wordTrace_append hprefix tailTrace_6883805
  have hstable : (prefixWord ++ tailWord_6883805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883805).length < 2 ^ (prefixWord ++ tailWord_6883805).sum := by decide
  have hdescent : baseEnd_6883805 < baseStart_6883805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883808 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4]
def baseStart_6883808 : Nat := 118140960795 + 6883808 * 2 ^ 59
def prefixEnd_6883808 : Nat := 4983230072969 + 3 ^ 40 * 6883808 * 2
def baseEnd_6883808 : Nat := 3534702237265508303241949

theorem tailTrace_6883808 : CollatzResearch.WordTrace tailWord_6883808 prefixEnd_6883808 3534702237265508303241949 := by
  unfold tailWord_6883808
  simp only [CollatzResearch.WordTrace]
  refine ⟨125536552122573375826186039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167382069496764501101581385 125536552122573375826186039)
  ·
    refine ⟨188304828183860063739279059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125536552122573375826186039 188304828183860063739279059)
    ·
      refine ⟨282457242275790095608918589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188304828183860063739279059 282457242275790095608918589)
      ·
        refine ⟨105921465853421285853344471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 282457242275790095608918589 105921465853421285853344471)
        ·
          refine ⟨158882198780131928780016707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105921465853421285853344471 158882198780131928780016707)
          ·
            refine ⟨238323298170197893170025061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158882198780131928780016707 238323298170197893170025061)
            ·
              refine ⟨44685618406912104969379699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 238323298170197893170025061 44685618406912104969379699)
              ·
                refine ⟨67028427610368157454069549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44685618406912104969379699 67028427610368157454069549)
                ·
                  refine ⟨25135660353888059045276081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67028427610368157454069549 25135660353888059045276081)
                  ·
                    refine ⟨18851745265416044283957061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25135660353888059045276081 18851745265416044283957061)
                    ·
                      refine ⟨3534702237265508303241949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18851745265416044283957061 3534702237265508303241949)
                      ·
                        rfl

theorem cell23_6883808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_6883808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883808 prefixEnd_6883808 := by exact prefixLift 6883808
  have htrace : WordTrace (prefixWord ++ tailWord_6883808) baseStart_6883808 baseEnd_6883808 := by
    simpa [prefixWord, tailWord_6883808, baseEnd_6883808] using wordTrace_append hprefix tailTrace_6883808
  have hstable : (prefixWord ++ tailWord_6883808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883808).length < 2 ^ (prefixWord ++ tailWord_6883808).sum := by decide
  have hdescent : baseEnd_6883808 < baseStart_6883808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883815 : List Nat := [1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_6883815 : Nat := 118140960795 + 6883815 * 2 ^ 59
def prefixEnd_6883815 : Nat := 4983230072969 + 3 ^ 40 * 6883815 * 2
def baseEnd_6883815 : Nat := 3534705831630089775854417

theorem tailTrace_6883815 : CollatzResearch.WordTrace tailWord_6883815 prefixEnd_6883815 3534705831630089775854417 := by
  unfold tailWord_6883815
  simp only [CollatzResearch.WordTrace]
  refine ⟨251073359556121391847876899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167382239704080927898584599 251073359556121391847876899)
  ·
    refine ⟨376610039334182087771815349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251073359556121391847876899 376610039334182087771815349)
    ·
      refine ⟨35307191187579570728607689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 376610039334182087771815349 35307191187579570728607689)
      ·
        refine ⟨26480393390684678046455767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35307191187579570728607689 26480393390684678046455767)
        ·
          refine ⟨39720590086027017069683651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26480393390684678046455767 39720590086027017069683651)
          ·
            refine ⟨59580885129040525604525477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39720590086027017069683651 59580885129040525604525477)
            ·
              refine ⟨11171415961695098550848527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59580885129040525604525477 11171415961695098550848527)
              ·
                refine ⟨16757123942542647826272791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11171415961695098550848527 16757123942542647826272791)
                ·
                  refine ⟨25135685913813971739409187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16757123942542647826272791 25135685913813971739409187)
                  ·
                    refine ⟨37703528870720957609113781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25135685913813971739409187 37703528870720957609113781)
                    ·
                      refine ⟨3534705831630089775854417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37703528870720957609113781 3534705831630089775854417)
                      ·
                        rfl

theorem cell23_6883815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_6883815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883815 prefixEnd_6883815 := by exact prefixLift 6883815
  have htrace : WordTrace (prefixWord ++ tailWord_6883815) baseStart_6883815 baseEnd_6883815 := by
    simpa [prefixWord, tailWord_6883815, baseEnd_6883815] using wordTrace_append hprefix tailTrace_6883815
  have hstable : (prefixWord ++ tailWord_6883815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883815).length < 2 ^ (prefixWord ++ tailWord_6883815).sum := by decide
  have hdescent : baseEnd_6883815 < baseStart_6883815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883818 : List Nat := [3, 1, 3, 1, 3, 1, 11]
def baseStart_6883818 : Nat := 118140960795 + 6883818 * 2 ^ 59
def prefixEnd_6883818 : Nat := 4983230072969 + 3 ^ 40 * 6883818 * 2
def baseEnd_6883818 : Nat := 43638362618173497087863

theorem tailTrace_6883818 : CollatzResearch.WordTrace tailWord_6883818 prefixEnd_6883818 43638362618173497087863 := by
  unfold tailWord_6883818
  simp only [CollatzResearch.WordTrace]
  refine ⟨62768367243777630840059027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 167382312650073682240157405 62768367243777630840059027)
  ·
    refine ⟨94152550865666446260088541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62768367243777630840059027 94152550865666446260088541)
    ·
      refine ⟨35307206574624917347533203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94152550865666446260088541 35307206574624917347533203)
      ·
        refine ⟨52960809861937376021299805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35307206574624917347533203 52960809861937376021299805)
        ·
          refine ⟨19860303698226516007987427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52960809861937376021299805 19860303698226516007987427)
          ·
            refine ⟨29790455547339774011981141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19860303698226516007987427 29790455547339774011981141)
            ·
              refine ⟨43638362618173497087863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29790455547339774011981141 43638362618173497087863)
              ·
                rfl

theorem cell23_6883818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 11].length) (baseStart_6883818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883818 prefixEnd_6883818 := by exact prefixLift 6883818
  have htrace : WordTrace (prefixWord ++ tailWord_6883818) baseStart_6883818 baseEnd_6883818 := by
    simpa [prefixWord, tailWord_6883818, baseEnd_6883818] using wordTrace_append hprefix tailTrace_6883818
  have hstable : (prefixWord ++ tailWord_6883818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883818).length < 2 ^ (prefixWord ++ tailWord_6883818).sum := by decide
  have hdescent : baseEnd_6883818 < baseStart_6883818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883846 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6883846 : Nat := 118140960795 + 6883846 * 2 ^ 59
def prefixEnd_6883846 : Nat := 4983230072969 + 3 ^ 40 * 6883846 * 2
def baseEnd_6883846 : Nat := 3534721749530379154566775

theorem tailTrace_6883846 : CollatzResearch.WordTrace tailWord_6883846 prefixEnd_6883846 3534721749530379154566775 := by
  unfold tailWord_6883846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7846077819344033879445481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 167382993479339389428170261 7846077819344033879445481)
  ·
    refine ⟨5884558364508025409584111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7846077819344033879445481 5884558364508025409584111)
    ·
      refine ⟨8826837546762038114376167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5884558364508025409584111 8826837546762038114376167)
      ·
        refine ⟨13240256320143057171564251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8826837546762038114376167 13240256320143057171564251)
        ·
          refine ⟨19860384480214585757346377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240256320143057171564251 19860384480214585757346377)
          ·
            refine ⟨14895288360160939318009783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19860384480214585757346377 14895288360160939318009783)
            ·
              refine ⟨22342932540241408977014675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14895288360160939318009783 22342932540241408977014675)
              ·
                refine ⟨33514398810362113465522013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22342932540241408977014675 33514398810362113465522013)
                ·
                  refine ⟨12567899553885792549570755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33514398810362113465522013 12567899553885792549570755)
                  ·
                    refine ⟨18851849330828688824356133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12567899553885792549570755 18851849330828688824356133)
                    ·
                      refine ⟨3534721749530379154566775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18851849330828688824356133 3534721749530379154566775)
                      ·
                        rfl

theorem cell23_6883846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6883846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883846 prefixEnd_6883846 := by exact prefixLift 6883846
  have htrace : WordTrace (prefixWord ++ tailWord_6883846) baseStart_6883846 baseEnd_6883846 := by
    simpa [prefixWord, tailWord_6883846, baseEnd_6883846] using wordTrace_append hprefix tailTrace_6883846
  have hstable : (prefixWord ++ tailWord_6883846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883846).length < 2 ^ (prefixWord ++ tailWord_6883846).sum := by decide
  have hdescent : baseEnd_6883846 < baseStart_6883846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883880 : List Nat := [2, 1, 5, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6883880 : Nat := 118140960795 + 6883880 * 2 ^ 59
def prefixEnd_6883880 : Nat := 4983230072969 + 3 ^ 40 * 6883880 * 2
def baseEnd_6883880 : Nat := 3534739207872632021541619

theorem tailTrace_6883880 : CollatzResearch.WordTrace tailWord_6883880 prefixEnd_6883880 3534739207872632021541619 := by
  unfold tailWord_6883880
  simp only [CollatzResearch.WordTrace]
  refine ⟨125537865150442953974496547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167383820200590605299328729 125537865150442953974496547)
  ·
    refine ⟨188306797725664430961744821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125537865150442953974496547 188306797725664430961744821)
    ·
      refine ⟨17653762286781040402663577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 188306797725664430961744821 17653762286781040402663577)
      ·
        refine ⟨13240321715085780301997683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17653762286781040402663577 13240321715085780301997683)
        ·
          refine ⟨19860482572628670452996525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13240321715085780301997683 19860482572628670452996525)
          ·
            refine ⟨7447680964735751419873697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19860482572628670452996525 7447680964735751419873697)
            ·
              refine ⟨5585760723551813564905273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7447680964735751419873697 5585760723551813564905273)
              ·
                refine ⟨4189320542663860173678955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5585760723551813564905273 4189320542663860173678955)
                ·
                  refine ⟨6283980813995790260518433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4189320542663860173678955 6283980813995790260518433)
                  ·
                    refine ⟨4712985610496842695388825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6283980813995790260518433 4712985610496842695388825)
                    ·
                      refine ⟨3534739207872632021541619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4712985610496842695388825 3534739207872632021541619)
                      ·
                        rfl

theorem cell23_6883880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6883880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883880 prefixEnd_6883880 := by exact prefixLift 6883880
  have htrace : WordTrace (prefixWord ++ tailWord_6883880) baseStart_6883880 baseEnd_6883880 := by
    simpa [prefixWord, tailWord_6883880, baseEnd_6883880] using wordTrace_append hprefix tailTrace_6883880
  have hstable : (prefixWord ++ tailWord_6883880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883880).length < 2 ^ (prefixWord ++ tailWord_6883880).sum := by decide
  have hdescent : baseEnd_6883880 < baseStart_6883880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883888 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5]
def baseStart_6883888 : Nat := 118140960795 + 6883888 * 2 ^ 59
def prefixEnd_6883888 : Nat := 4983230072969 + 3 ^ 40 * 6883888 * 2
def baseEnd_6883888 : Nat := 3534743315717867990241581

theorem tailTrace_6883888 : CollatzResearch.WordTrace tailWord_6883888 prefixEnd_6883888 3534743315717867990241581 := by
  unfold tailWord_6883888
  simp only [CollatzResearch.WordTrace]
  refine ⟨125538011042428462657642159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 167384014723237950210189545 125538011042428462657642159)
  ·
    refine ⟨188307016563642693986463239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 125538011042428462657642159 188307016563642693986463239)
    ·
      refine ⟨282460524845464040979694859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 188307016563642693986463239 282460524845464040979694859)
      ·
        refine ⟨423690787268196061469542289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282460524845464040979694859 423690787268196061469542289)
        ·
          refine ⟨317768090451147046102156717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423690787268196061469542289 317768090451147046102156717)
          ·
            refine ⟨119163033919180142288308769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 317768090451147046102156717 119163033919180142288308769)
            ·
              refine ⟨89372275439385106716231577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 119163033919180142288308769 89372275439385106716231577)
              ·
                refine ⟨67029206579538830037173683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 89372275439385106716231577 67029206579538830037173683)
                ·
                  refine ⟨100543809869308245055760525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67029206579538830037173683 100543809869308245055760525)
                  ·
                    refine ⟨37703928700990591895910197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 100543809869308245055760525 37703928700990591895910197)
                    ·
                      refine ⟨3534743315717867990241581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37703928700990591895910197 3534743315717867990241581)
                      ·
                        rfl

theorem cell23_6883888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 5].length) (baseStart_6883888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883888 prefixEnd_6883888 := by exact prefixLift 6883888
  have htrace : WordTrace (prefixWord ++ tailWord_6883888) baseStart_6883888 baseEnd_6883888 := by
    simpa [prefixWord, tailWord_6883888, baseEnd_6883888] using wordTrace_append hprefix tailTrace_6883888
  have hstable : (prefixWord ++ tailWord_6883888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883888).length < 2 ^ (prefixWord ++ tailWord_6883888).sum := by decide
  have hdescent : baseEnd_6883888 < baseStart_6883888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6883975 : List Nat := [1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 4]
def baseStart_6883975 : Nat := 118140960795 + 6883975 * 2 ^ 59
def prefixEnd_6883975 : Nat := 4983230072969 + 3 ^ 40 * 6883975 * 2
def baseEnd_6883975 : Nat := 3534787988534809149853681

theorem tailTrace_6883975 : CollatzResearch.WordTrace tailWord_6883975 prefixEnd_6883975 3534787988534809149853681 := by
  unfold tailWord_6883975
  simp only [CollatzResearch.WordTrace]
  refine ⟨251079195235541739173701379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 167386130157027826115800919 251079195235541739173701379)
  ·
    refine ⟨376618792853312608760552069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 251079195235541739173701379 376618792853312608760552069)
    ·
      refine ⟨70616023659996114142603513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 376618792853312608760552069 70616023659996114142603513)
      ·
        refine ⟨52962017744997085606952635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70616023659996114142603513 52962017744997085606952635)
        ·
          refine ⟨79443026617495628410428953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52962017744997085606952635 79443026617495628410428953)
          ·
            refine ⟨59582269963121721307821715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79443026617495628410428953 59582269963121721307821715)
            ·
              refine ⟨89373404944682581961732573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59582269963121721307821715 89373404944682581961732573)
              ·
                refine ⟨33515026854255968235649715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89373404944682581961732573 33515026854255968235649715)
                ·
                  refine ⟨50272540281383952353474573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33515026854255968235649715 50272540281383952353474573)
                  ·
                    refine ⟨18852202605518982132552965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50272540281383952353474573 18852202605518982132552965)
                    ·
                      refine ⟨3534787988534809149853681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18852202605518982132552965 3534787988534809149853681)
                      ·
                        rfl

theorem cell23_6883975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_6883975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6883975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6883975 prefixEnd_6883975 := by exact prefixLift 6883975
  have htrace : WordTrace (prefixWord ++ tailWord_6883975) baseStart_6883975 baseEnd_6883975 := by
    simpa [prefixWord, tailWord_6883975, baseEnd_6883975] using wordTrace_append hprefix tailTrace_6883975
  have hstable : (prefixWord ++ tailWord_6883975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6883975).length < 2 ^ (prefixWord ++ tailWord_6883975).sum := by decide
  have hdescent : baseEnd_6883975 < baseStart_6883975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6883975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
